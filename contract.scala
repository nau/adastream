//> using scala 3.3.1
//> using toolkit 0.2.1
//> using plugin org.scalus:scalus-plugin_3:0.4.1
//> using dep org.scalus:scalus_3:0.4.1
//> using dep org.bouncycastle:bcprov-jdk18on:1.77
//> using dep net.i2p.crypto:eddsa:0.3.0
//> using dep com.bloxbean.cardano:cardano-client-lib:0.5.0
//> using dep com.bloxbean.cardano:cardano-client-backend-blockfrost:0.5.0

package adastream

import adastream.Encryption.chunksFromInputStream
import adastream.Encryption.signMessage
import dotty.tools.dotc.util.Util
import io.bullet.borer.Cbor
import org.bouncycastle.crypto.digests.SHA256Digest
import org.bouncycastle.crypto.params.Ed25519PrivateKeyParameters
import org.bouncycastle.crypto.params.Ed25519PublicKeyParameters
import org.bouncycastle.crypto.signers.Ed25519Signer
import scalus.Compile
import scalus.Compiler.compile
import scalus.Compiler.fieldAsData
import scalus.*
import scalus.builtins.Builtins
import scalus.builtins.ByteString
import scalus.builtins.given
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

import java.io.FileInputStream
import java.io.FileOutputStream
import java.io.InputStream
import java.nio.ByteBuffer
import java.nio.file.Path
import java.util.Arrays
import scala.annotation.tailrec
import scala.collection.mutable.ArrayBuffer
import com.bloxbean.cardano.client.address.AddressProvider
import com.bloxbean.cardano.client.plutus.spec.PlutusV2Script
import com.bloxbean.cardano.client.common.model.Networks
import com.bloxbean.cardano.client.backend.blockfrost.service.BFBackendService
import com.bloxbean.cardano.client.backend.blockfrost.common.Constants
import com.bloxbean.cardano.client.account.Account
import com.bloxbean.cardano.client.quicktx.QuickTxBuilder
import com.bloxbean.cardano.client.quicktx.Tx
import com.bloxbean.cardano.client.api.model.Amount
import com.bloxbean.cardano.client.function.helper.SignerProviders
import org.bouncycastle.crypto.digests.Blake2bDigest
import com.bloxbean.cardano.client.plutus.spec.BigIntPlutusData
import com.bloxbean.cardano.client.plutus.spec.PlutusData
import com.bloxbean.cardano.client.plutus.spec.*
import net.i2p.crypto.eddsa.EdDSAEngine
import com.bloxbean.cardano.client.crypto.config.CryptoConfiguration
import com.bloxbean.cardano.client.crypto.cip1852.CIP1852
import com.bloxbean.cardano.client.crypto.cip1852.DerivationPath
import com.bloxbean.cardano.client.function.helper.ScriptUtxoFinders
import com.bloxbean.cardano.client.backend.api.DefaultUtxoSupplier
import com.bloxbean.cardano.client.quicktx.ScriptTx
import com.bloxbean.cardano.client.api.TransactionEvaluator
import com.bloxbean.cardano.client.api.model.Result
import scala.util.Random
import adastream.BondContract.BondConfig
import adastream.BondContract.BondAction
import adastream.Encryption.blake2b224Hash

extension (a: Array[Byte]) def toHex: String = Utils.bytesToHex(a)

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
                        if index % 2 == BigInt(0)
                        then Builtins.sha2_256(Builtins.appendByteString(curHash, sibling))
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

    def chunksFromInputStream(inputStream: InputStream): Iterator[Array[Byte]] = {
        new Iterator[Array[Byte]] {
            var nextChunk = readChunk32(inputStream)
            override def hasNext: Boolean = nextChunk != null
            override def next(): Array[Byte] = {
                val chunk = nextChunk
                nextChunk = readChunk32(inputStream)
                chunk
            }
        }
    }

    def signMessage(claim: ByteString, privateKey: Ed25519PrivateKeyParameters): ByteString =
        val signer = new Ed25519Signer();
        signer.init(true, privateKey);
        signer.update(claim.bytes, 0, claim.bytes.length)
        ByteString.fromArray(signer.generateSignature())

    def blake2b224Hash(data: Array[Byte]): Array[Byte] = {
        val digest = new Blake2bDigest(224) // 224 bits
        digest.update(data, 0, data.length)
        val hash = new Array[Byte](digest.getDigestSize)
        digest.doFinal(hash, 0)
        hash
    }
}

object Bond:
    val compiledBondScript = compile(BondContract.bondContractValidator)
    val bondValidator = compiledBondScript.toUplc(generateErrorTraces = true)
    val bondProgram = Program((1, 0, 0), bondValidator)
    val compiledHtlcScript = compile(BondContract.makeHtlcContractValidator)
    val xorBytesScript = compile(BondContract.xorBytes).toUplc(generateErrorTraces = true)
    val htlcValidator = compiledHtlcScript.toUplc(generateErrorTraces = true)
    val htlcProgram = Program((1, 0, 0), htlcValidator)

    def publish() = {
        val is = System.in
        val hashes = Encryption
            .chunksFromInputStream(System.in)
            .map(ch => ByteString.fromArray(Utils.sha2_256(ch)))
        val merkleTree = MerkleTree.fromHashes(ArraySeq.from(hashes))
        println(s"fileId: ${merkleTree.getMerkleRoot.toHex}")
    }

    def encrypt(secret: String, encryptIncorrectly: Boolean) = {
        val preimage = Utils.hexToBytes(secret)
        val preimageHash = ByteString.unsafeFromArray(Utils.sha2_256(preimage))
        val encryptedChunks = ArraySeq.newBuilder[Array[Byte]]
        val hashes = ArraySeq.newBuilder[ByteString]
        val encHashes = ArraySeq.newBuilder[ByteString]
        val chunks = chunksFromInputStream(System.in).toArray
        val randomWrongChunkIndex = Random.nextInt(chunks.length)
        System.err.println(s"randomWrongChunkIndex: $randomWrongChunkIndex")
        chunks.zipWithIndex.foreach { case (chunk, index) =>
            val encrypted =
                val encrypted = Encryption.encryptChunk(chunk, preimage, index)
                if encryptIncorrectly && randomWrongChunkIndex == index
                then encrypted.updated(0, (encrypted(0) + 1).toByte)
                else encrypted
            val hash = Utils.sha2_256(chunk)
            val encHash = Utils.sha2_256(encrypted ++ hash)
            encryptedChunks += encrypted
            hashes += ByteString.unsafeFromArray(hash)
            encHashes += ByteString.unsafeFromArray(encHash)
        }
        val fileId = MerkleTree.fromHashes(hashes.result()).getMerkleRoot
        val encId = MerkleTree.fromHashes(encHashes.result()).getMerkleRoot
        val claim = Builtins.appendByteString(encId, preimageHash)
        val signingProvider = CryptoConfiguration.INSTANCE.getSigningProvider()
        val mnemonic = System.getenv("MNEMONIC")

        val hdKeyPair = new CIP1852().getKeyPairFromMnemonic(
          mnemonic,
          DerivationPath.createExternalAddressDerivationPath(0)
        );
        val signature =
            signingProvider.signExtended(claim.bytes, hdKeyPair.getPrivateKey().getKeyData())
        val fileOut = System.out
        fileOut.write(signature)
        fileOut.write(preimageHash.bytes)
        for (enc, hash) <- encryptedChunks.result().zip(hashes.result()) do
            fileOut.write(enc)
            fileOut.write(hash.bytes)
        System.err.println(s"preimage: ${Utils.bytesToHex(preimage)}")
        System.err.println(s"preimageHash: ${preimageHash.toHex}")
        System.err.println(s"pubKey: ${hdKeyPair.getPublicKey().getKeyData().toHex}")
        System.err.println(s"signature: ${signature.toHex}")
        System.err.println(s"fileId: ${fileId.toHex}")
        System.err.println(s"encId: ${encId.toHex}")
    }

    def merkleTreeFromIterator(chunks: Iterator[Array[Byte]]): MerkleTree = {
        MerkleTree.fromHashes(ArraySeq.from(chunks.map(ByteString.unsafeFromArray)))
    }

    def decrypt(secret: String, publicKeyHex: String, spendIfWrong: Boolean = false): Unit = {
        val preimage = Utils.hexToBytes(secret)
        val preimageHash = ByteString.unsafeFromArray(Utils.sha2_256(preimage))
        val chunks = chunksFromInputStream(System.in).toArray
        val signature = chunks(0) ++ chunks(1) // 64 bytes, 2 chunks
        val publicKeyBytes = Utils.hexToBytes(publicKeyHex)
        val paymentHash = chunks(2) // 32 bytes, 1 chunk
        System.err.println(s"chunks: ${chunks.length}")
        System.err.println(s"Signature: ${Utils.bytesToHex(signature)}")
        System.err.println(
          s"expected preimage hash: ${preimageHash.toHex}, file preimage hash: ${Utils.bytesToHex(paymentHash)}"
        )
        chunks.iterator.take(5).foreach(chunk => println(Utils.bytesToHex(chunk)))
        val fileId = merkleTreeFromIterator(
          chunks.iterator.drop(3).grouped(2).map(it => it(1))
        ).getMerkleRoot
        val encId = merkleTreeFromIterator(chunks.iterator.drop(3)).getMerkleRoot
        System.err.println(s"fileId: ${fileId.toHex}")
        System.err.println(s"encId: ${encId.toHex}")
        val claim = Builtins.appendByteString(encId, preimageHash)
        // Verify the signature
        val isVerified = {
            // Load the public key
            val publicKeyParams = new Ed25519PublicKeyParameters(publicKeyBytes, 0)

            // Prepare the signer for verification
            val signer = new Ed25519Signer()
            signer.init(false, publicKeyParams)
            signer.update(claim.bytes, 0, claim.bytes.length)
            signer.verifySignature(signature)
        }

        if !isVerified then
            System.err.println("Signature mismatch")
            sys.exit(1)

        val decryptedFile = System.out

        chunks.iterator.drop(3).grouped(2).zipWithIndex.foreach { (it, index) =>
            val (encryptedChunk, hash) = (it(0), it(1))
            val decrypted = Encryption.decryptChunk(encryptedChunk, preimage, index)
            val computedHash = Utils.sha2_256(decrypted)
            if !computedHash.sameElements(hash) then {
                val merkleProof =
                    // drop the first layer as it is (enc, hash) pairs
                    // and in BondContract we use hash(enc ++ hash) as the leaf hash
                    merkleTreeFromIterator(chunks.iterator.drop(3))
                        .makeMerkleProof(index * 2)
                        .drop(1)
                System.err.println(
                  s"Computed hash: ${Utils.bytesToHex(computedHash)}, expected: ${Utils.bytesToHex(hash)}"
                )
                System.err.println(s"Merkle inclusion proof $merkleProof")
                System.err.println(s"Index: $index")
                if spendIfWrong then
                    System.err.println("Spending the bond")
                    spendBondWithFraudProof(
                      ByteString.unsafeFromArray(signature),
                      ByteString.unsafeFromArray(preimage),
                      ByteString.unsafeFromArray(encryptedChunk),
                      ByteString.unsafeFromArray(hash),
                      index,
                      encId.toHex,
                      merkleProof
                    )

                sys.exit(1)
            }
            decryptedFile.write(decrypted)
        }
        System.err.println("Successfully decrypted")
    }

    def verify(publicKeyHex: String): Unit = {
        val chunks = chunksFromInputStream(System.in).toArray
        val signature = chunks(0) ++ chunks(1) // 64 bytes, 2 chunks
        val publicKeyBytes = Utils.hexToBytes(publicKeyHex)
        val paymentHash = ByteString.fromArray(chunks(2)) // 32 bytes, 1 chunk
        System.err.println(s"chunks: ${chunks.length}")
        System.err.println(s"Signature: ${Utils.bytesToHex(signature)}")
        val fileId = merkleTreeFromIterator(
          chunks.iterator.drop(3).grouped(2).map(it => it(1))
        ).getMerkleRoot
        val encId = merkleTreeFromIterator(chunks.iterator.drop(3)).getMerkleRoot
        System.err.println(s"fileId: ${fileId.toHex}")
        System.err.println(s"encId: ${encId.toHex}")
        val claim = Builtins.appendByteString(encId, paymentHash)
        // Verify the signature
        val isVerified = {
            // Load the public key
            val publicKeyParams = new Ed25519PublicKeyParameters(publicKeyBytes, 0)

            // Prepare the signer for verification
            val signer = new Ed25519Signer()
            signer.init(false, publicKeyParams)
            signer.update(claim.bytes, 0, claim.bytes.length)
            signer.verifySignature(signature)
        }

        if !isVerified then
            System.err.println("Signature mismatch")
            sys.exit(1)
        System.err.println("Signature verified")

        val bondConfig = BondContract.BondConfig(
          paymentHash,
          encId,
          ByteString.fromArray(publicKeyBytes),
          ByteString.fromArray(blake2b224Hash(publicKeyBytes))
        )
        val plutusScript = PlutusV2Script
            .builder()
            .`type`("PlutusScriptV2")
            .cborHex(bondProgram.doubleCborHex)
            .build();

        val scriptAddress =
            AddressProvider.getEntAddress(plutusScript, Networks.preview()).toBech32()
        val result = findBondUtxo(bondConfig)
        System.err.println(
          s"Looking up for bond UTxO with address ${scriptAddress} and bondConfig: $bondConfig"
        )
        if result.isPresent()
        then System.err.println(s"Found bond utxo: ${result.get()}")
        else
            System.err.println("Bond does not exist")
            sys.exit(1)
    }

    def dataToCardanoClientPlutusData(data: Data): PlutusData = {
        import scala.jdk.CollectionConverters.*
        data match
            case Data.Constr(tag, args) =>
                val convertedArgs = ListPlutusData
                    .builder()
                    .plutusDataList(args.map(dataToCardanoClientPlutusData).asJava)
                    .build()
                ConstrPlutusData
                    .builder()
                    .alternative(tag)
                    .data(convertedArgs)
                    .build()
            case Data.Map(items) =>
                MapPlutusData
                    .builder()
                    .map(
                      items
                          .map { case (k, v) =>
                              (dataToCardanoClientPlutusData(k), dataToCardanoClientPlutusData(v))
                          }
                          .toMap
                          .asJava
                    )
                    .build()
            case Data.List(items) =>
                ListPlutusData
                    .builder()
                    .plutusDataList(items.map(dataToCardanoClientPlutusData).asJava)
                    .build()
            case Data.I(i) =>
                BigIntPlutusData.of(i.bigInteger)
            case Data.B(b) =>
                BytesPlutusData.of(b.bytes)
    }

    def makeBondTx() = {

        val chunks = chunksFromInputStream(System.in).toArray
        val signature = chunks(0) ++ chunks(1) // 64 bytes, 2 chunks
        val paymentHash = ByteString.fromArray(chunks(2)) // 32 bytes, 1 chunk
        val encId = merkleTreeFromIterator(chunks.iterator.drop(3)).getMerkleRoot
        val plutusScript = PlutusV2Script
            .builder()
            .`type`("PlutusScriptV2")
            .cborHex(bondProgram.doubleCborHex)
            .build();
        val scriptAddress =
            AddressProvider.getEntAddress(plutusScript, Networks.preview()).toBech32();

        System.err.println(s"bond contract address: $scriptAddress")

        val sender = new Account(Networks.testnet(), System.getenv("MNEMONIC"))
        val publicKeyBytes = sender.hdKeyPair().getPublicKey().getKeyData()
        val backendService = new BFBackendService(
          Constants.BLOCKFROST_PREVIEW_URL,
          System.getenv("BLOCKFROST_API_KEY")
        )
        val quickTxBuilder = new QuickTxBuilder(backendService)
        val bondConfig = BondContract.BondConfig(
          paymentHash,
          encId,
          ByteString.unsafeFromArray(publicKeyBytes),
          ByteString.unsafeFromArray(sender.hdKeyPair().getPublicKey().getKeyHash())
        )
        val datumData = dataToCardanoClientPlutusData(bondConfig.toData)
        // val datumData = PlutusData.unit()
        val tx = new Tx()
            .payToContract(scriptAddress, Amount.ada(100), datumData)
            .from(sender.getBaseAddress().getAddress())

        val result = quickTxBuilder
            .compose(tx)
            .withSigner(SignerProviders.signerFrom(sender))
            .complete()
        println(result)
    }

    def findBondUtxo(bondConfig: BondConfig) = {
        val plutusScript = PlutusV2Script
            .builder()
            .`type`("PlutusScriptV2")
            .cborHex(bondProgram.doubleCborHex)
            .build();

        val scriptAddress =
            AddressProvider.getEntAddress(plutusScript, Networks.preview()).toBech32()

        val backendService = new BFBackendService(
          Constants.BLOCKFROST_PREVIEW_URL,
          System.getenv("BLOCKFROST_API_KEY")
        )
        val utxoSupplier = new DefaultUtxoSupplier(backendService.getUtxoService())
        val datumData = dataToCardanoClientPlutusData(bondConfig.toData)
        ScriptUtxoFinders.findFirstByInlineDatum(utxoSupplier, scriptAddress, datumData)
    }

    def spendBondWithFraudProof(
        signature: ByteString,
        preimage: ByteString,
        encryptedChunk: ByteString,
        chunkHash: ByteString,
        chunkIndex: BigInt,
        encId: String,
        merkleProof: Seq[ByteString]
    ) = {
        val sender = new Account(Networks.testnet(), System.getenv("MNEMONIC"))
        val paymentHash = ByteString.unsafeFromArray(Utils.sha2_256(preimage.bytes))
        val bondConfig = BondContract.BondConfig(
          paymentHash,
          ByteString.fromHex(encId),
          ByteString.unsafeFromArray(sender.hdKeyPair().getPublicKey().getKeyData()),
          ByteString.unsafeFromArray(sender.hdKeyPair().getPublicKey().getKeyHash())
        )
        System.err.println(s"bondConfig: $bondConfig")
        val fraudProof = BondAction.FraudProof(
          signature = signature,
          preimage = preimage,
          encryptedChunk = encryptedChunk,
          chunkHash = chunkHash,
          chunkIndex = chunkIndex,
          merkleProof = scalus.prelude.List(merkleProof: _*)
        )
        spendBond(sender, bondConfig, fraudProof)
    }

    def withdraw(preimage: String, encId: String) = {
        val sender = new Account(Networks.testnet(), System.getenv("MNEMONIC"))
        val paymentHash = ByteString.unsafeFromArray(Utils.sha2_256(Utils.hexToBytes(preimage)))
        val bondConfig = BondContract.BondConfig(
          paymentHash,
          ByteString.fromHex(encId),
          ByteString.unsafeFromArray(sender.hdKeyPair().getPublicKey().getKeyData()),
          ByteString.unsafeFromArray(sender.hdKeyPair().getPublicKey().getKeyHash())
        )
        spendBond(sender, bondConfig, BondAction.Withdraw(ByteString.fromHex(preimage)))
    }

    def spendBond(sender: Account, bondConfig: BondConfig, bondAction: BondAction) = {
        val plutusScript = PlutusV2Script
            .builder()
            .`type`("PlutusScriptV2")
            .cborHex(bondProgram.doubleCborHex)
            .build();

        val scriptAddress =
            AddressProvider.getEntAddress(plutusScript, Networks.preview()).toBech32()

        val backendService = new BFBackendService(
          Constants.BLOCKFROST_PREVIEW_URL,
          System.getenv("BLOCKFROST_API_KEY")
        )
        val utxoSupplier = new DefaultUtxoSupplier(backendService.getUtxoService())
        val datumData = dataToCardanoClientPlutusData(bondConfig.toData)
        // val datumData = PlutusData.unit()
        val utxo =
            ScriptUtxoFinders.findFirstByInlineDatum(utxoSupplier, scriptAddress, datumData).get

        System.err.println(s"found utxo: $utxo")

        val redeemer = dataToCardanoClientPlutusData(bondAction.toData)
        val scriptTx = new ScriptTx()
            .collectFrom(utxo, redeemer)
            .payToAddress(sender.baseAddress(), utxo.getAmount())
            .attachSpendingValidator(plutusScript)

        val pubKeyHashBytes = sender.hdKeyPair().getPublicKey().getKeyHash()
        val quickTxBuilder = new QuickTxBuilder(backendService)
        val tx = quickTxBuilder
            .compose(scriptTx)
            .feePayer(sender.baseAddress())
            .withSigner(SignerProviders.signerFrom(sender))
            .withRequiredSigners(pubKeyHashBytes)
            .ignoreScriptCostEvaluationError(false)
            .buildAndSign()
        System.err.println(tx.toJson())
        val result = backendService.getTransactionService().submitTransaction(tx.serialize())
        System.err.println(result)
    }

    def showKeys() = {
        val sender = new Account(Networks.testnet(), System.getenv("MNEMONIC"))
        println(s"private key: ${sender.hdKeyPair().getPrivateKey().getKeyData().toHex}")
        println(s"public key: ${sender.publicKeyBytes().toHex}")
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
            case "publish"       => publish()
            case "encrypt"       => encrypt(others.head, encryptIncorrectly = false)
            case "encrypt-wrong" => encrypt(others.head, encryptIncorrectly = true)
            case "decrypt"       => decrypt(others.head, others(1), spendIfWrong = false)
            case "spend-bond"    => decrypt(others.head, others(1), spendIfWrong = true)
            case "verify"        => verify(others.head)
            case "bond"          => makeBondTx()
            case "withdraw"      => withdraw(others.head, others(1))
            case "keys"          => showKeys()

    }
