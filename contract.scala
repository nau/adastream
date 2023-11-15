//> using scala 3.3.0
//> using toolkit 0.2.1
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
import scalus.uplc.Data.{FromData, ToData}
import scalus.uplc.Data.{fromData, toData}
import scalus.uplc.Program
import scalus.uplc.ProgramFlatCodec
import scalus.uplc.FromDataInstances.given
import scalus.uplc.ToDataInstances.given
import scalus.uplc.Term
import scalus.utils.Utils
import scalus.ledger.api.v1.POSIXTime
import scalus.ledger.api.v1.Extended
import scalus.uplc.FromData
import scalus.uplc.ToData

@Compile
object BondContract {
    import List.*

    case class BondConfig(
        preimageHash: ByteString,
        encId: ByteString,
        serverPubKey: ByteString,
        serverPkh: ByteString
    )

    enum BondAction:
        case Withdraw(preimage: ByteString)
        case FraudProof(
            signature: ByteString,
            preimage: ByteString,
            encryptedChunk: ByteString,
            chunkHash: ByteString,
            chunkIndex: BigInt,
            merkleProof: List[ByteString]
        )

    given FromData[BondConfig] = FromData.deriveCaseClass
    given ToData[BondConfig] = ToData.deriveCaseClass[BondConfig](0)

    given FromData[BondAction] = FromData.deriveEnum {
        case 0 => FromData.deriveConstructor[BondAction.Withdraw]
        case 1 => FromData.deriveConstructor[BondAction.FraudProof]
    }
    given ToData[BondAction] = (a: BondAction) =>
        a match
            case BondAction.Withdraw(preimage) =>
                Builtins.mkConstr(0, Builtins.mkCons(preimage.toData, Builtins.mkNilData()))
            case BondAction.FraudProof(
                  signature,
                  preimage,
                  encryptedChunk,
                  chunkHash,
                  chunkIndex,
                  merkleProof
                ) =>
                Builtins.mkConstr(
                  1,
                  Builtins.mkCons(
                    signature.toData,
                    Builtins.mkCons(
                      preimage.toData,
                      Builtins.mkCons(
                        encryptedChunk.toData,
                        Builtins.mkCons(
                          chunkHash.toData,
                          Builtins.mkCons(
                            chunkIndex.toData,
                            Builtins.mkCons(
                              merkleProof.toData,
                              Builtins.mkNilData()
                            )
                          )
                        )
                      )
                    )
                  )
                )

    def integerToByteString(num: BigInt): ByteString =
        def loop(div: BigInt, result: ByteString): ByteString = {
            val shifted = num / div
            val newResult = Builtins.consByteString(shifted % 256, result)
            if shifted == BigInt(0) then newResult
            else loop(div * 256, newResult)
        }
        loop(1, ByteString.empty)

    def xorBytes(a: BigInt, b: BigInt): BigInt = {
        def pow(base: BigInt, exponent: BigInt): BigInt = {
            if exponent == BigInt(0) then BigInt(1)
            else base * pow(base, exponent - 1)
        }

        def xorHelper(a: BigInt, b: BigInt, i: BigInt, result: BigInt): BigInt = {
            if (i < 0) result
            else {
                val pow2i = pow(2, i)
                val bitA = (a / pow2i) % 2
                val bitB = (b / pow2i) % 2
                val xorBit = (bitA + bitB) % 2
                xorHelper(a, b, i - 1, result + xorBit * pow2i)
            }
        }

        xorHelper(a, b, 7, 0)
    }

    // a and b are of the same length
    def xor(a: ByteString, b: ByteString) = {
        val l1 = Builtins.lengthOfByteString(a)
        val l2 = Builtins.lengthOfByteString(b)
        def xorHelper(a: ByteString, b: ByteString, i: BigInt, result: ByteString): ByteString = {
            if i < 0 then result
            else {
                val byteA = Builtins.indexByteString(a, i)
                val byteB = Builtins.indexByteString(b, i)
                val xorByte = Builtins.trace("xorBytes")(xorBytes(byteA, byteB))
                xorHelper(a, b, i - 1, Builtins.consByteString(xorByte, result))
            }
        }
        if l1 == l2 then xorHelper(a, b, l1 - 1, ByteString.empty)
        else throw new Exception("X")
    }

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

    def verifyPreimage(preimage: ByteString, preimageHash: ByteString): Boolean =
        if Builtins.equalsByteString(
              preimageHash,
              Builtins.sha2_256(preimage)
            )
        then true
        else throw new Exception("P")

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
              Builtins.trace("xor")(xor(
                encryptedChunk,
                Builtins.trace("sha2_256")(Builtins.sha2_256(
                  Builtins.appendByteString(
                    preimage,
                    Builtins.trace("integerToByteString")(integerToByteString(chunkIndex))
                  )
                ))
              ))
            )
            if Builtins.equalsByteString(expectedChunkHash, chunkHash) then throw new Exception("H")
            else true
        Builtins.trace("verifyWrongChunkHash")(true)
        /* val verifyValidClaimSignature = {
            val claim = Builtins.appendByteString(encId, preimageHash)
            if Builtins.verifySchnorrSecp256k1Signature(
                  serverPubKey,
                  claim,
                  signature
                )
            then true
            else throw new Exception("S")
        }
         */
        val verifyValidPreimage = verifyPreimage(preimage, preimageHash)
        /*
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
        && merkleInclusionProofValid */
        verifyValidPreimage

    def bondContractValidator(datum: Data, redeemer: Data, ctxData: Data) = {
        val a = Builtins.trace("bondContractValidator")(true)
        fromData[BondConfig](datum) match
            case BondConfig(preimageHash, encId, serverPubKey, serverPkh) =>
                fromData[BondAction](redeemer) match
                    case BondAction.Withdraw(preimage) =>
                        val signatories = fieldAsData[ScriptContext](_.txInfo.signatories)(ctxData)
                        val pkh =
                            Builtins.unsafeDataAsB(Builtins.unsafeDataAsList(signatories).head)
                        val verifySignature =
                            if Builtins.equalsByteString(pkh, serverPkh) then true
                            else throw new Exception("W")
                        val verifyValidPreimage = verifyPreimage(preimage, preimageHash)
                        verifySignature && verifyValidPreimage
                    case BondAction.FraudProof(
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

object Bond:
    val compiledBondScript = compile(BondContract.bondContractValidator)
    val bondValidator = compiledBondScript.toUplc(generateErrorTraces = true)
    val bondProgram = Program((2, 0, 0), bondValidator)
    val compiledHtlcScript = compile(BondContract.makeHtlcContractValidator)
    val htlcValidator = compiledHtlcScript.toUplc(generateErrorTraces = true)
    val htlcProgram = Program((2, 0, 0), htlcValidator)
    @main def main() = {
        println(compiledBondScript.pretty.render(100))
        // println(bondProgram.doubleCborHex)
        // println(compiledHtlcScript.pretty.render(100))
        // println(htlcProgram.doubleCborHex)
        println(s"bondProgram size: ${bondProgram.doubleCborEncoded.size}")
        println(s"htlcProgram size: ${htlcProgram.doubleCborEncoded.size}")
    }
