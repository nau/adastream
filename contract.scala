//> using scala 3.3.0
//> using plugin org.scalus:scalus-plugin_3:0.3.0
//> using dep org.scalus:scalus_3:0.3.0

package adastream

import io.bullet.borer.Cbor
import scalus.*
import scalus.Compile
import scalus.Compiler.compile
import scalus.Compiler.fieldAsData
import scalus.builtins.Builtins
import scalus.builtins.ByteString
import scalus.ledger.api.v1.FromDataInstances.given
import scalus.ledger.api.v2.FromDataInstances.given
import scalus.ledger.api.v2.ScriptPurpose.*
import scalus.ledger.api.v2.*
import scalus.prelude.AssocMap
import scalus.prelude.List
import scalus.prelude.Maybe.*
import scalus.prelude.Prelude.===
import scalus.prelude.Prelude.given
import scalus.pretty
import scalus.sir.SIR
import scalus.sir.SimpleSirToUplcLowering
import scalus.uplc.Cek
import scalus.uplc.Data
import scalus.uplc.Data.FromData
import scalus.uplc.Data.fromData
import scalus.uplc.Program
import scalus.uplc.ProgramFlatCodec
import scalus.uplc.FromDataInstances.given
import scalus.uplc.Term
import scalus.utils.Utils
import scalus.ledger.api.v1.POSIXTime
import scalus.ledger.api.v1.Extended
import scalus.uplc.FromData

@Compile
object BondContract {
    import List.*

    case class BondConfig(preimageHash: ByteString, encId: ByteString, serverPubKey: ByteString)
    case class FraudProof(
        signature: ByteString,
        preimage: ByteString,
        encryptedChunk: ByteString,
        chunkHash: ByteString,
        chunkIndex: BigInt,
        merkleProof: List[ByteString]
    )

    given FromData[BondConfig] = FromData.deriveCaseClass
    given FromData[FraudProof] = FromData.deriveCaseClass

    def integerToByteString(num: BigInt): ByteString =
        if num == BigInt(0) then ByteString.empty
        else Builtins.consByteString(num % 256, integerToByteString(num / 256))

    val xor = (a: ByteString, b: ByteString) => a

    inline def verifyMerkleInclusionProof(
        merkleProof: List[ByteString],
        encryptedChunk: ByteString,
        chunkHash: ByteString,
        chunkIndex: BigInt,
        encId: ByteString
    ): Boolean =
        val encryptedChunkAndChunkHashHash = Builtins.sha2_256(
          Builtins.appendByteString(encryptedChunk, chunkHash)
        )
        val merkleRoot = List.foldLeft(merkleProof, encryptedChunkAndChunkHashHash) { (acc, hash) =>
            if chunkIndex % 2 == BigInt(0) then
                Builtins.sha2_256(Builtins.appendByteString(hash, acc))
            else Builtins.sha2_256(Builtins.appendByteString(acc, hash))
        }
        if Builtins.equalsByteString(merkleRoot, encId) then true
        else throw new Exception("M")

    inline def verifyFraudProof(
        chunkHash: ByteString,
        chunkIndex: BigInt,
        encId: ByteString,
        encryptedChunk: ByteString,
        merkleProof: prelude.List[ByteString],
        preimage: ByteString,
        preimageHash: ByteString,
        serverPubKey: ByteString,
        signature: ByteString
    ): Boolean =
        val verifyWrongChunkHash =
            // hash( Ei ⊕ hash( preimage || i) ) ≠ Hi
            val expectedChunkHash = Builtins.sha2_256(
              xor(
                encryptedChunk,
                Builtins.sha2_256(
                  Builtins.appendByteString(
                    preimage,
                    integerToByteString(chunkIndex)
                  )
                )
              )
            )
            if Builtins.equalsByteString(expectedChunkHash, chunkHash) then throw new Exception("H")
            else true
        val verifyValidClaimSignature = {
            val claim = Builtins.appendByteString(encId, preimageHash)
            if Builtins.verifySchnorrSecp256k1Signature(
                  serverPubKey,
                  claim,
                  signature
                )
            then true
            else throw new Exception("S")
        }
        val verifyValidPreimage =
            if Builtins.equalsByteString(
                  preimageHash,
                  Builtins.sha2_256(preimage)
                )
            then true
            else throw new Exception("P")
        val merkleInclusionProofValid = verifyMerkleInclusionProof(
          merkleProof,
          encryptedChunk,
          chunkHash,
          chunkIndex,
          encId
        )
        verifyWrongChunkHash
        && verifyValidClaimSignature
        && verifyValidPreimage
        && merkleInclusionProofValid

    def bondContractValidator(datum: Data, redeemer: Data, ctxData: Data) = {
        fromData[BondConfig](datum) match
            case BondConfig(preimageHash, encId, serverPubKey) =>
                fromData[FraudProof](redeemer) match
                    case FraudProof(
                          signature,
                          preimage,
                          encryptedChunk,
                          chunkHash,
                          chunkIndex,
                          merkleProof
                        ) =>
                        verifyFraudProof(
                          chunkHash,
                          chunkIndex,
                          encId,
                          encryptedChunk,
                          merkleProof,
                          preimage,
                          preimageHash,
                          serverPubKey,
                          signature
                        )
    }

    /*
     * HTLC contract validator
     */
    def makeHtlcContractValidator(
        clientPubKeyHash: Data,
        expiration: POSIXTime,
        hash: ByteString
    ) =
        (datum: Data, redeemer: Data, ctxData: Data) => {
            val validPreimage = Builtins.equalsByteString(
              hash,
              Builtins.sha2_256(Builtins.unsafeDataAsB(redeemer))
            )
            val expired = {
                val txInfoData = fieldAsData[ScriptContext](_.txInfo)(ctxData)
                val signatoriesData = fieldAsData[TxInfo](_.signatories)(txInfoData)
                val txtime = fromData[POSIXTimeRange](
                  fieldAsData[TxInfo](_.validRange)(txInfoData)
                )
                txtime.from.extended match
                    case Extended.Finite(txtime) =>
                        val expired = expiration < txtime
                        val signedByClient = {
                            val signaturePubKeyHashData =
                                Builtins.unsafeDataAsList(signatoriesData).head
                            Builtins.equalsData(signaturePubKeyHashData, clientPubKeyHash)
                        }
                        expired && signedByClient
                    case _ => false
            }
            if validPreimage || expired then () else throw new Exception()
        }
}

@main def main() = {
    val compiledBondScript = compile(BondContract.bondContractValidator)
    val bondValidator = compiledBondScript.toUplc(generateErrorTraces = true)
    val bondProgram = Program((2, 0, 0), bondValidator)
    val compiledHtlcScript = compile(BondContract.makeHtlcContractValidator)
    val htlcValidator = compiledHtlcScript.toUplc(generateErrorTraces = true)
    val htlcProgram = Program((2, 0, 0), htlcValidator)
    println(compiledBondScript.pretty.render(100))
    println(bondProgram.doubleCborHex)
    println(compiledHtlcScript.pretty.render(100))
    println(htlcProgram.doubleCborHex)
    println(s"bondProgram size: ${bondProgram.doubleCborEncoded.size}")
    println(s"htlcProgram size: ${htlcProgram.doubleCborEncoded.size}")
}
