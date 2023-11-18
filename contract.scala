//> using scala 3.3.0
//> using toolkit 0.2.1
//> using plugin org.scalus:scalus-plugin_3:0.3.0
//> using dep org.scalus:scalus_3:0.3.0
//> using dep org.bouncycastle:bcprov-jdk18on:1.77

package adastream

import io.bullet.borer.Cbor
import org.bouncycastle.crypto.digests.SHA256Digest
import scalus.Compile
import scalus.Compiler.compile
import scalus.Compiler.fieldAsData
import scalus.*
import scalus.builtins.Builtins
import scalus.builtins.ByteString
import scalus.ledger.api.v1.Extended
import scalus.ledger.api.v1.FromDataInstances.given
import scalus.ledger.api.v1.POSIXTime
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
import scalus.uplc.Data.ToData
import scalus.uplc.Data.fromData
import scalus.uplc.Data.toData
import scalus.uplc.FromData
import scalus.uplc.FromDataInstances.given
import scalus.uplc.Program
import scalus.uplc.ProgramFlatCodec
import scalus.uplc.Term
import scalus.uplc.ToData
import scalus.uplc.ToDataInstances.given
import scalus.utils.Utils

import java.nio.ByteBuffer
import java.nio.file.Path
import java.util.Arrays
import scala.annotation.tailrec
import scala.collection.mutable.ArrayBuffer
import java.io.InputStream
import java.io.FileInputStream
import adastream.Encryption.chunksFromInputStream
import org.bouncycastle.crypto.params.Ed25519PrivateKeyParameters
import org.bouncycastle.crypto.signers.Ed25519Signer
import adastream.Encryption.signMessage

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
        def xorHelper(a: BigInt, b: BigInt, pow: BigInt, result: BigInt): BigInt = {
            if pow == BigInt(256) then result
            else xorHelper(a / 2, b / 2, pow * 2, result + ((a + b) % 2) * pow)
        }
        xorHelper(a, b, 1, 0)
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
                val xorByte = xorBytes(byteA, byteB)
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
        def loop(index: BigInt, curHash: ByteString, siblings: List[ByteString]): ByteString =
            siblings match
                case Nil => curHash
                case Cons(sibling, rest) =>
                    val nextHash =
                        if index % 2 == BigInt(0) then
                            Builtins.sha2_256(Builtins.appendByteString(curHash, sibling))
                        else Builtins.sha2_256(Builtins.appendByteString(sibling, curHash))
                    loop(index / 2, nextHash, rest)

        val merkleRoot = loop(chunkIndex, encryptedChunkAndChunkHashHash, merkleProof)
        Builtins.equalsByteString(merkleRoot, encId)

    def verifyPreimage(preimage: ByteString, preimageHash: ByteString): Boolean =
        Builtins.equalsByteString(
          preimageHash,
          Builtins.sha2_256(preimage)
        )

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
              Builtins.trace("xor")(
                xor(
                  encryptedChunk,
                  Builtins.trace("sha2_256")(
                    Builtins.sha2_256(
                      Builtins.appendByteString(
                        preimage,
                        Builtins.trace("integerToByteString")(integerToByteString(chunkIndex))
                      )
                    )
                  )
                )
              )
            )
            !Builtins.equalsByteString(expectedChunkHash, chunkHash)
        Builtins.trace("verifyWrongChunkHash")(true)
        val verifyValidClaimSignature = {
            val claim = Builtins.appendByteString(encId, preimageHash)
            Builtins.verifyEd25519Signature(
              serverPubKey,
              claim,
              signature
            )
        }
        Builtins.trace("verifyValidClaimSignature")(true)

        val verifyValidPreimage = verifyPreimage(preimage, preimageHash)
        Builtins.trace("verifyValidPreimage")(true)

        val merkleInclusionProofValid = verifyMerkleInclusionProof(
          merkleProof,
          encryptedChunk,
          chunkHash,
          chunkIndex,
          encId
        )
        (verifyWrongChunkHash || (throw new Exception("W")))
        && (verifyValidClaimSignature || (throw new Exception("S")))
        && (verifyValidPreimage || (throw new Exception("P")))
        && (merkleInclusionProofValid || (throw new Exception("M")))

    def bondContractValidator(datum: Data, redeemer: Data, ctxData: Data) = {
        fromData[BondConfig](datum) match
            case BondConfig(preimageHash, encId, serverPubKey, serverPkh) =>
                val a = Builtins.trace("fromData[BondConfig]")(true)
                fromData[BondAction](redeemer) match
                    case BondAction.Withdraw(preimage) =>
                        val a = Builtins.trace("BondAction.Withdraw(preimage)")(true)
                        val signatories = fieldAsData[ScriptContext](_.txInfo.signatories)(ctxData)
                        val pkh =
                            Builtins.unsafeDataAsB(Builtins.unsafeDataAsList(signatories).head)
                        val verifySignature = Builtins.equalsByteString(pkh, serverPkh)
                        val verifyValidPreimage = verifyPreimage(preimage, preimageHash)
                        (verifySignature || (throw new Exception("S")))
                        && (verifyValidPreimage || (throw new Exception("P")))
                    case BondAction.FraudProof(
                          signature,
                          preimage,
                          encryptedChunk,
                          chunkHash,
                          chunkIndex,
                          merkleProof
                        ) =>
                        val a = Builtins.trace("BondAction.FraudProof")(true)
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

import scala.collection.immutable.ArraySeq

class MerkleTree(private val levels: ArrayBuffer[ArrayBuffer[ByteString]]) {
    def getMerkleRoot: ByteString = {
        levels.last.head
    }

    def makeMerkleProof(index: Int): ArraySeq[ByteString] = {
        val proofSize = levels.length - 1
        val hashesCount = levels.head.length
        assert(index < hashesCount)
        if proofSize == 0 then return ArraySeq.empty

        var proof = ArraySeq.newBuilder[ByteString]
        for (level <- 0 until proofSize) {
            val levelHashes = levels(level)
            val idx = index / (1 << level)
            val proofHashIdx = if idx % 2 == 0 then idx + 1 else idx - 1
            proof += levelHashes(proofHashIdx)
        }

        proof.result()
    }

    override def toString(): String =
        levels.map(_.map(_.toHex.take(8)).mkString(",")).mkString("\n")
}

object MerkleTree {
    def fromHashes(hashes: ArraySeq[ByteString]): MerkleTree = {
        @annotation.tailrec
        def buildLevels(
            currentLevelHashes: ArrayBuffer[ByteString],
            accumulatedLevels: ArrayBuffer[ArrayBuffer[ByteString]]
        ): ArrayBuffer[ArrayBuffer[ByteString]] = {
            if currentLevelHashes.length == 1 then
                // If only one hash is left, add it to the levels and finish
                accumulatedLevels += currentLevelHashes
                accumulatedLevels
            else
                // Calculate the next level and recurse
                val nextLevelHashes = calculateMerkleTreeLevel(currentLevelHashes)
                accumulatedLevels += currentLevelHashes
                buildLevels(nextLevelHashes, accumulatedLevels)
        }

        if (hashes.isEmpty) {
            MerkleTree(ArrayBuffer(ArrayBuffer(ByteString.unsafeFromArray(new Array[Byte](32)))))
        } else if (hashes.length == 1) {
            MerkleTree(ArrayBuffer(ArrayBuffer.from(hashes)))
        } else {
            MerkleTree(buildLevels(ArrayBuffer.from(hashes), ArrayBuffer.empty))
        }
    }

    def calculateMerkleTreeLevel(hashes: ArrayBuffer[ByteString]): ArrayBuffer[ByteString] = {
        var levelHashes = ArrayBuffer.empty[ByteString]
        // Duplicate the last element if the number of elements is odd
        if hashes.length % 2 == 1
        then hashes.addOne(hashes.last)

        for (i <- hashes.indices by 2) {
            val combinedHash = hashes(i).bytes ++ hashes(i + 1).bytes
            levelHashes += ByteString.unsafeFromArray(Utils.sha2_256(combinedHash))
        }
        levelHashes
    }

    def calculateMerkleRootFromProof(
        index: Int,
        hash: ByteString,
        proof: ArraySeq[ByteString]
    ): ByteString = {

        var idx = index
        val hasher = new SHA256Digest()
        def finalizeReset(): Array[Byte] = {
            val hash = new Array[Byte](hasher.getDigestSize)
            hasher.doFinal(hash, 0)
            hash
        }
        var currentHash = hash

        proof.foreach { sibling =>
            val combinedHash =
                if idx % 2 == 0 then currentHash.bytes ++ sibling.bytes
                else sibling.bytes ++ currentHash.bytes
            hasher.update(combinedHash.toArray, 0, combinedHash.length)
            val hash = new Array[Byte](hasher.getDigestSize)
            hasher.doFinal(hash, 0)
            currentHash = ByteString.unsafeFromArray(hash)
            idx /= 2
        }

        currentHash
    }

}

object Encryption {
    def encryptChunk(chunk: Array[Byte], secret: Array[Byte], index: Int): Array[Byte] = {
        val hasher = new SHA256Digest()
        hasher.update(secret, 0, secret.length)

        // Convert index to bytes and update the hasher
        // We add +1 to avoid the case 0 == 0x encoded as zero bytes
        val indexBytes = BondContract.integerToByteString(index + 1).bytes
        hasher.update(indexBytes, 0, indexBytes.length)

        // Finalize the hash
        val hash = new Array[Byte](hasher.getDigestSize)
        hasher.doFinal(hash, 0)

        // XOR each byte of the chunk with the hash
        chunk.zip(hash).map { case (chunkByte, hashByte) => (chunkByte ^ hashByte).toByte }
    }

    def decryptChunk(chunk: Array[Byte], secret: Array[Byte], index: Int): Array[Byte] = {
        encryptChunk(chunk, secret, index)
    }

    def readChunk32(inputStream: InputStream): Array[Byte] = {
        val buffer = new Array[Byte](32)
        val bytesRead = inputStream.read(buffer)
        if (bytesRead == -1) null
        else if (bytesRead < 32) {
            // Pad the buffer with zeros if less than chunkSize bytes are read
            java.util.Arrays.fill(buffer, bytesRead, 32, 0.toByte)
            buffer
        } else buffer
    }

    def calculateFileIdAndEncId(inputFile: Path, secret: Array[Byte]): (ByteString, ByteString) = {
        import java.io.{File, FileInputStream}

        val inputStream = new FileInputStream(inputFile.toFile())

        val hashes = ArraySeq.newBuilder[ByteString]
        val encHashes = ArraySeq.newBuilder[ByteString]
        var index = 0
        while (inputStream.available() > 0) {
            val chunk = readChunk32(inputStream)
            val encrypted = encryptChunk(chunk, secret, index)
            val hash = Utils.sha2_256(chunk)
            val encHash = Utils.sha2_256(encrypted ++ hash)
            hashes += ByteString.unsafeFromArray(hash)
            encHashes += ByteString.unsafeFromArray(encHash)
            index += 1
        }
        val fileId = MerkleTree.fromHashes(hashes.result()).getMerkleRoot
        val encId = MerkleTree.fromHashes(encHashes.result()).getMerkleRoot
        (fileId, encId)
    }

    def chunksFromInputStream(inputStream: InputStream): LazyList[Array[Byte]] = {
        if (inputStream.available() > 0) {
            val chunk = readChunk32(inputStream)
            chunk #:: chunksFromInputStream(inputStream)
        } else LazyList.empty
    }


    def signMessage(claim: ByteString, privateKey: Ed25519PrivateKeyParameters): ByteString =
        val signer = new Ed25519Signer();
        signer.init(true, privateKey);
        signer.update(claim.bytes, 0, claim.bytes.length)
        ByteString.fromArray(signer.generateSignature())
}

object Bond:
    val compiledBondScript = compile(BondContract.bondContractValidator)
    val bondValidator = compiledBondScript.toUplc(generateErrorTraces = true)
    val bondProgram = Program((2, 0, 0), bondValidator)
    val compiledHtlcScript = compile(BondContract.makeHtlcContractValidator)
    val xorBytesScript = compile(BondContract.xorBytes).toUplc(generateErrorTraces = true)
    val htlcValidator = compiledHtlcScript.toUplc(generateErrorTraces = true)
    val htlcProgram = Program((2, 0, 0), htlcValidator)

    def publish(file: String) = {
        val hashes = Encryption
            .chunksFromInputStream(new FileInputStream(file))
            .map(ch => ByteString.fromArray(Utils.sha2_256(ch)))
        val merkleTree = MerkleTree.fromHashes(ArraySeq.from(hashes))
        println(s"fileId: ${merkleTree.getMerkleRoot.toHex}")
    }

    def encrypt(file: String, secret: String, privateKey: String) = {
        val preimage = Utils.hexToBytes(secret)
        val preimageHash = ByteString.unsafeFromArray(Utils.sha2_256(preimage))
        val encryptedChunks = ArraySeq.newBuilder[Array[Byte]]
        val hashes = ArraySeq.newBuilder[ByteString]
        val encHashes = ArraySeq.newBuilder[ByteString]
        chunksFromInputStream(new FileInputStream(file)).zipWithIndex.foreach {
            case (chunk, index) =>
                val encrypted = Encryption.encryptChunk(chunk, preimage, index)
                val hash = Utils.sha2_256(chunk)
                val encHash = Utils.sha2_256(encrypted ++ hash)
                encryptedChunks += encrypted
                hashes += ByteString.unsafeFromArray(hash)
                encHashes += ByteString.unsafeFromArray(encHash)
        }
        val fileId = MerkleTree.fromHashes(hashes.result()).getMerkleRoot
        val encId = MerkleTree.fromHashes(encHashes.result()).getMerkleRoot
        val claim = Builtins.appendByteString(encId, preimageHash)
        val pk = new Ed25519PrivateKeyParameters(Utils.hexToBytes(privateKey))
        val signature = signMessage(claim, pk)
        val fileOut = new java.io.FileOutputStream(file + ".encrypted")
        fileOut.write(signature.bytes)
        fileOut.write(preimageHash.bytes)
        encryptedChunks.result().foreach(chunk => fileOut.write(chunk))
        fileOut.close()
        println(s"preimage: ${Utils.bytesToHex(preimage)}")
        println(s"preimageHash: ${preimageHash.toHex}")
        println(s"pubKey: ${Utils.bytesToHex(pk.generatePublicKey().getEncoded())}")
        println(s"signature: ${signature.toHex}")
        println(s"fileId: ${fileId.toHex}")
        println(s"encId: ${encId.toHex}")
    }

    @main def main(cmd: String, others: String*) = {
        cmd match
            case "info" =>
                // println(compiledBondScript.pretty.render(100))
                // println(bondProgram.doubleCborHex)
                // println(compiledHtlcScript.pretty.render(100))
                // println(htlcProgram.doubleCborHex)
                println(s"bondProgram size: ${bondProgram.doubleCborEncoded.size}")
                println(s"htlcProgram size: ${htlcProgram.doubleCborEncoded.size}")
            case "publish" => publish(others.head)
            case "encrypt" => encrypt(others.head, others(1), others(2))

    }
