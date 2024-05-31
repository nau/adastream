package adastream

import adastream.BondContract.BondAction
import adastream.BondContract.BondConfig
import com.bloxbean.cardano.client.account.Account
import com.bloxbean.cardano.client.address.AddressProvider
import com.bloxbean.cardano.client.backend.api.DefaultUtxoSupplier
import com.bloxbean.cardano.client.backend.blockfrost.common.Constants
import com.bloxbean.cardano.client.backend.blockfrost.service.BFBackendService
import com.bloxbean.cardano.client.common.model.Networks
import com.bloxbean.cardano.client.function.helper.ScriptUtxoFinders
import com.bloxbean.cardano.client.function.helper.SignerProviders
import com.bloxbean.cardano.client.plutus.spec.PlutusV2Script
import com.bloxbean.cardano.client.quicktx.QuickTxBuilder
import com.bloxbean.cardano.client.quicktx.ScriptTx
import org.bouncycastle.crypto.digests.SHA256Digest
import org.bouncycastle.crypto.params.Ed25519PrivateKeyParameters
import org.bouncycastle.crypto.signers.Ed25519Signer
import scalus.*
import scalus.bloxbean.Interop
import scalus.bloxbean.ScalusTransactionEvaluator
import scalus.builtin.Builtins.*
import scalus.builtin.ByteString
import scalus.builtin.Data
import scalus.builtin.Data.toData
import scalus.builtin.given
import scalus.utils.Utils

import java.io.InputStream
import java.nio.file.Path
import scala.annotation.tailrec
import scala.collection.immutable.ArraySeq
import scala.collection.mutable.ArrayBuffer
import com.bloxbean.cardano.client.api.model.Utxo

/** Rolling Merkle tree implementation
  */
class MerkleTreeRootBuilder {
    private val levels: ArrayBuffer[ByteString] = ArrayBuffer.empty

    private def addHashAtLevel(hash: ByteString, startingLevel: Int): this.type = {
        var levelHash = hash
        var level = startingLevel

        // Process each level to find a place for the new hash
        while level < levels.length do
            if levels(level) == null then
                // If no hash is present at this level, just add the current hash
                levels(level) = levelHash
                return this
            else
                // If there is a hash, combine it with the current hash and move up one level
                levelHash = sha2_256(levels(level) ++ levelHash)
                levels(level) = null // Clear the hash as it's been moved up
                level += 1

        // If we exit the loop, it means we're adding a new level to the tree
        levels.append(levelHash)
        this
    }

    def addHash(hash: ByteString): this.type = {
        addHashAtLevel(hash, 0)
        this
    }

    def getMerkleRoot: ByteString =
        if levels.isEmpty then ByteString.unsafeFromArray(new Array[Byte](32))
        else if levels.size == 1 then levels.head
        else
            var index = 0
            while index < levels.length do
                if levels(index) != null && index < levels.length - 1
                then addHashAtLevel(levels(index), index)
                index += 1
            levels.last
}

class MerkleTree(private val levels: ArrayBuffer[ArrayBuffer[ByteString]]) {
    def getMerkleRoot: ByteString = {
        levels.last.head
    }

    def makeMerkleProof(index: Int): Seq[ByteString] = {
        val proofSize = levels.length - 1
        val hashesCount = levels.head.length
        assert(index < hashesCount)
        if proofSize == 0 then return ArraySeq.empty

        val proof = ArraySeq.newBuilder[ByteString]
        for level <- 0 until proofSize do
            val levelHashes = levels(level)
            val idx = index / (1 << level)
            val proofHashIdx = if idx % 2 == 0 then idx + 1 else idx - 1
            proof += levelHashes(proofHashIdx)

        proof.result()
    }

    override def toString: String =
        levels.map(_.map(_.toHex.take(8)).mkString(",")).mkString("\n")
}

object MerkleTree {
    def fromHashes(hashes: collection.Seq[ByteString]): MerkleTree = {
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

        if hashes.isEmpty then
            MerkleTree(ArrayBuffer(ArrayBuffer(ByteString.unsafeFromArray(new Array[Byte](32)))))
        else if hashes.length == 1 then MerkleTree(ArrayBuffer(ArrayBuffer.from(hashes)))
        else MerkleTree(buildLevels(ArrayBuffer.from(hashes), ArrayBuffer.empty))
    }

    private def calculateMerkleTreeLevel(
        hashes: ArrayBuffer[ByteString]
    ): ArrayBuffer[ByteString] = {
        val levelHashes = ArrayBuffer.empty[ByteString]
        // Duplicate the last element if the number of elements is odd
        if hashes.length % 2 == 1
        then hashes.addOne(hashes.last)

        for i <- hashes.indices by 2 do
            val combinedHash = hashes(i) ++ hashes(i + 1)
            levelHashes += sha2_256(combinedHash)
        levelHashes
    }

    def calculateMerkleRootFromProof(
        index: Int,
        hash: ByteString,
        proof: Seq[ByteString]
    ): ByteString = {
        var idx = index
        val hasher = new SHA256Digest()
        var currentHash = hash

        for sibling <- proof do
            val combinedHash =
                if idx % 2 == 0 then currentHash ++ sibling
                else sibling ++ currentHash
            currentHash = sha2_256(combinedHash)
            idx /= 2
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

    private def readChunk32(inputStream: InputStream): Array[Byte] = {
        val buffer = new Array[Byte](32)
        val bytesRead = inputStream.read(buffer)
        if bytesRead == -1 then null
        else if bytesRead < 32 then
            // Pad the buffer with zeros if less than chunkSize bytes are read
            java.util.Arrays.fill(buffer, bytesRead, 32, 0.toByte)
            buffer
        else buffer
    }

    def calculateFileIdAndEncId(inputFile: Path, secret: Array[Byte]): (ByteString, ByteString) = {
        import java.io.FileInputStream

        val inputStream = new FileInputStream(inputFile.toFile)
        val hashes = ArraySeq.newBuilder[ByteString]
        val encHashes = ArraySeq.newBuilder[ByteString]
        var index = 0
        while inputStream.available() > 0 do
            val chunk = readChunk32(inputStream)
            val encrypted = encryptChunk(chunk, secret, index)
            val hash = Utils.sha2_256(chunk)
            val encHash = Utils.sha2_256(encrypted ++ hash)
            hashes += ByteString.unsafeFromArray(hash)
            encHashes += ByteString.unsafeFromArray(encHash)
            index += 1
        val fileId = MerkleTree.fromHashes(hashes.result()).getMerkleRoot
        val encId = MerkleTree.fromHashes(encHashes.result()).getMerkleRoot
        (fileId, encId)
    }

    def chunksFromInputStream(inputStream: InputStream): Iterator[Array[Byte]] = {
        new Iterator[Array[Byte]] {
            var nextChunk: Array[Byte] = readChunk32(inputStream)
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
        signer.update(claim.bytes, 0, claim.length)
        ByteString.fromArray(signer.generateSignature())
}

class Tx {
    val plutusScript = PlutusV2Script
        .builder()
        .cborHex(bondProgram.doubleCborHex)
        .build();

    def makeSpendBondScriptTx(
        sender: Account,
        utxo: Utxo,
        bondAction: BondAction
    ): ScriptTx = {
        val redeemer = Interop.toPlutusData(bondAction.toData)
        val scriptTx = new ScriptTx()
            .collectFrom(utxo, redeemer)
            .payToAddress(sender.baseAddress(), utxo.getAmount)
            .attachSpendingValidator(plutusScript)
        scriptTx
    }
}

class TxService(

)