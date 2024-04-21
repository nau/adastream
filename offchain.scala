package adastream

import adastream.BondContract.{BondAction, BondConfig}
import adastream.Encryption.chunksFromInputStream
import com.bloxbean.cardano.client.account.Account
import com.bloxbean.cardano.client.address.AddressProvider
import com.bloxbean.cardano.client.api.model.Amount
import com.bloxbean.cardano.client.backend.api.DefaultUtxoSupplier
import com.bloxbean.cardano.client.backend.blockfrost.common.Constants
import com.bloxbean.cardano.client.backend.blockfrost.service.BFBackendService
import com.bloxbean.cardano.client.common.model.Networks
import com.bloxbean.cardano.client.crypto.cip1852.{CIP1852, DerivationPath}
import com.bloxbean.cardano.client.crypto.config.CryptoConfiguration
import com.bloxbean.cardano.client.function.helper.{ScriptUtxoFinders, SignerProviders}
import com.bloxbean.cardano.client.plutus.spec.*
import com.bloxbean.cardano.client.quicktx.{QuickTxBuilder, ScriptTx, Tx}
import org.bouncycastle.crypto.digests.SHA256Digest
import org.bouncycastle.crypto.params.Ed25519PrivateKeyParameters
import org.bouncycastle.crypto.signers.Ed25519Signer
import scalus.*
import scalus.Compiler.compile
import scalus.builtin.Builtins.*
import scalus.builtin.Data.{ToData, toData}
import scalus.builtin.{ByteString, Data, PlatformSpecific, given}
import scalus.ledger.api.v2.*
import scalus.uplc.{Program, Term}
import scalus.utils.Utils

import java.io.InputStream
import java.nio.file.Path
import scala.annotation.tailrec
import scala.collection.immutable.ArraySeq
import scala.collection.mutable.ArrayBuffer
import scala.util.Random

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

private val ps: PlatformSpecific = summon[PlatformSpecific]
private val compiledBondScript = compile(BondContract.bondContractValidator)
val bondValidator: Term = compiledBondScript.toUplc(generateErrorTraces = true)
val bondProgram: Program = Program((1, 0, 0), bondValidator)
private val compiledHtlcScript = compile(BondContract.makeHtlcContractValidator)
val xorBytesScript: Term = compile(BondContract.xorBytes).toUplc(generateErrorTraces = true)
private val htlcValidator = compiledHtlcScript.toUplc(generateErrorTraces = true)
private val htlcProgram = Program((1, 0, 0), htlcValidator)

lazy val sender = new Account(Networks.testnet(), System.getenv("MNEMONIC"))
lazy val privateKey = ByteString.fromArray(sender.privateKeyBytes)
lazy val publicKey = ByteString.fromArray(sender.publicKeyBytes)
lazy val publicKeyHash = ByteString.fromArray(sender.hdKeyPair.getPublicKey.getKeyHash)

private def publish(): Unit = {
    val is = System.in
    val hashes = Encryption
        .chunksFromInputStream(System.in)
        .map(ch => ByteString.fromArray(Utils.sha2_256(ch)))
    val merkleTree = MerkleTree.fromHashes(ArraySeq.from(hashes))
    println(s"fileId: ${merkleTree.getMerkleRoot.toHex}")
}

private def encrypt(secret: String, encryptIncorrectly: Boolean): Unit = {
    val preimage = Utils.hexToBytes(secret)
    val preimageHash = ByteString.unsafeFromArray(Utils.sha2_256(preimage))
    val encryptedChunks = ArraySeq.newBuilder[Array[Byte]]
    val hashes = ArraySeq.newBuilder[ByteString]
    val encHashes = ArraySeq.newBuilder[ByteString]
    val chunks = chunksFromInputStream(System.in).toArray
    val randomWrongChunkIndex = Random.nextInt(chunks.length)
    System.err.println(s"randomWrongChunkIndex: $randomWrongChunkIndex")
    for (chunk, index) <- chunks.zipWithIndex do
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

    val fileId = MerkleTree.fromHashes(hashes.result()).getMerkleRoot
    val encId = MerkleTree.fromHashes(encHashes.result()).getMerkleRoot
    val claim = encId ++ preimageHash
    val signingProvider = CryptoConfiguration.INSTANCE.getSigningProvider
    val mnemonic = System.getenv("MNEMONIC")

    val hdKeyPair = new CIP1852().getKeyPairFromMnemonic(
      mnemonic,
      DerivationPath.createExternalAddressDerivationPath(0)
    );
    val signature =
        signingProvider.signExtended(claim.bytes, hdKeyPair.getPrivateKey.getKeyData)
    val fileOut = System.out
    fileOut.write(signature)
    fileOut.write(preimageHash.bytes)
    for (enc, hash) <- encryptedChunks.result().zip(hashes.result()) do
        fileOut.write(enc)
        fileOut.write(hash.bytes)
    System.err.println(s"preimage: ${Utils.bytesToHex(preimage)}")
    System.err.println(s"preimageHash: ${preimageHash.toHex}")
    System.err.println(s"pubKey: ${hdKeyPair.getPublicKey.getKeyData.toHex}")
    System.err.println(s"signature: ${signature.toHex}")
    System.err.println(s"fileId: ${fileId.toHex}")
    System.err.println(s"encId: ${encId.toHex}")
}

private def merkleTreeFromIterator(chunks: Iterator[Array[Byte]]): MerkleTree = {
    MerkleTree.fromHashes(ArraySeq.from(chunks.map(ByteString.unsafeFromArray)))
}

private def decrypt(
    secret: String,
    publicKeyHex: String,
    spendIfWrong: Boolean = false
): Unit = {
    val preimage = Utils.hexToBytes(secret)
    val preimageHash = ByteString.unsafeFromArray(Utils.sha2_256(preimage))
    val chunks = chunksFromInputStream(System.in).toArray
    val signature = ByteString.fromArray(chunks(0) ++ chunks(1)) // 64 bytes, 2 chunks
    val publicKey = ByteString.fromHex(publicKeyHex)
    val paymentHash = chunks(2) // 32 bytes, 1 chunk
    System.err.println(s"chunks: ${chunks.length}")
    System.err.println(s"Signature: ${signature.toHex}")
    System.err.println(
      s"expected preimage hash: ${preimageHash.toHex}, file preimage hash: ${paymentHash.toHex}"
    )
    chunks.iterator.take(5).foreach(chunk => println(chunk.toHex))
    val fileId = merkleTreeFromIterator(
      chunks.iterator.drop(3).grouped(2).map(it => it(1))
    ).getMerkleRoot
    val encId = merkleTreeFromIterator(chunks.iterator.drop(3)).getMerkleRoot
    System.err.println(s"fileId: ${fileId.toHex}")
    System.err.println(s"encId: ${encId.toHex}")
    val claim = encId ++ preimageHash
    // Verify the signature
    val isVerified = ps.verifyEd25519Signature(publicKey, claim, signature)

    if !isVerified then
        System.err.println("Signature mismatch")
        sys.exit(1)

    val decryptedFile = System.out

    for (it, index) <- chunks.iterator.drop(3).grouped(2).zipWithIndex do
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
                  signature,
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

    System.err.println("Successfully decrypted")
}

private def verify(publicKeyHex: String): Unit = {
    val chunks = chunksFromInputStream(System.in).toArray
    val signature = ByteString.fromArray(chunks(0) ++ chunks(1)) // 64 bytes, 2 chunks
    val publicKey = ByteString.fromHex(publicKeyHex)
    val paymentHash = ByteString.fromArray(chunks(2)) // 32 bytes, 1 chunk
    System.err.println(s"chunks: ${chunks.length}")
    System.err.println(s"Signature: ${signature.toHex}")
    val fileId = merkleTreeFromIterator(
      chunks.iterator.drop(3).grouped(2).map(it => it(1))
    ).getMerkleRoot
    val encId = merkleTreeFromIterator(chunks.iterator.drop(3)).getMerkleRoot
    System.err.println(s"fileId: ${fileId.toHex}")
    System.err.println(s"encId: ${encId.toHex}")
    val claim = encId ++ paymentHash
    // Verify the signature
    val isVerified = ps.verifyEd25519Signature(publicKey, claim, signature)

    if !isVerified then
        System.err.println("Signature mismatch")
        sys.exit(1)
    System.err.println("Signature verified")

    val bondConfig = BondContract.BondConfig(
      paymentHash,
      encId,
      publicKey,
      ps.blake2b_224(publicKey)
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
    if result.isPresent
    then System.err.println(s"Found bond utxo: ${result.get()}")
    else
        System.err.println("Bond does not exist")
        sys.exit(1)
}

private def dataToCardanoClientPlutusData(data: Data): PlutusData = {
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

private def makeBondTx(): Unit = {

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

    val backendService = new BFBackendService(
      Constants.BLOCKFROST_PREVIEW_URL,
      System.getenv("BLOCKFROST_API_KEY")
    )
    val quickTxBuilder = new QuickTxBuilder(backendService)
    val bondConfig = BondContract.BondConfig(
      paymentHash,
      encId,
      publicKey,
      publicKeyHash
    )
    val datumData = dataToCardanoClientPlutusData(bondConfig.toData)
    // val datumData = PlutusData.unit()
    val tx = new Tx()
        .payToContract(scriptAddress, Amount.ada(100), datumData)
        .from(sender.getBaseAddress.getAddress)

    val result = quickTxBuilder
        .compose(tx)
        .withSigner(SignerProviders.signerFrom(sender))
        .complete()
    println(result)
}

private def findBondUtxo(bondConfig: BondConfig) = {
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
    val utxoSupplier = new DefaultUtxoSupplier(backendService.getUtxoService)
    val datumData = dataToCardanoClientPlutusData(bondConfig.toData)
    ScriptUtxoFinders.findFirstByInlineDatum(utxoSupplier, scriptAddress, datumData)
}

private def spendBondWithFraudProof(
    signature: ByteString,
    preimage: ByteString,
    encryptedChunk: ByteString,
    chunkHash: ByteString,
    chunkIndex: BigInt,
    encId: String,
    merkleProof: Seq[ByteString]
): Unit = {
    val paymentHash = sha2_256(preimage)
    val bondConfig = BondContract.BondConfig(
      paymentHash,
      ByteString.fromHex(encId),
      publicKey,
      publicKeyHash
    )
    System.err.println(s"bondConfig: $bondConfig")
    val fraudProof = BondAction.FraudProof(
      signature = signature,
      preimage = preimage,
      encryptedChunk = encryptedChunk,
      chunkHash = chunkHash,
      chunkIndex = chunkIndex,
      merkleProof = Data.List(merkleProof.map(bData).toList)
    )
    spendBond(sender, bondConfig, fraudProof)
}

def withdraw(preimage: String, encId: String): Unit = {
    val paymentHash = sha2_256(ByteString.fromHex(preimage))
    val bondConfig = BondContract.BondConfig(
      paymentHash,
      ByteString.fromHex(encId),
      publicKey,
      publicKeyHash
    )
    spendBond(sender, bondConfig, BondAction.Withdraw(ByteString.fromHex(preimage)))
}

private def spendBond(sender: Account, bondConfig: BondConfig, bondAction: BondAction): Unit = {
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
    val utxoSupplier = new DefaultUtxoSupplier(backendService.getUtxoService)
    val datumData = dataToCardanoClientPlutusData(bondConfig.toData)
    // val datumData = PlutusData.unit()
    val utxo =
        ScriptUtxoFinders.findFirstByInlineDatum(utxoSupplier, scriptAddress, datumData).get

    System.err.println(s"found utxo: $utxo")

    val redeemer = dataToCardanoClientPlutusData(bondAction.toData)
    val scriptTx = new ScriptTx()
        .collectFrom(utxo, redeemer)
        .payToAddress(sender.baseAddress(), utxo.getAmount)
        .attachSpendingValidator(plutusScript)

    val pubKeyHashBytes = sender.hdKeyPair().getPublicKey.getKeyHash
    val quickTxBuilder = new QuickTxBuilder(backendService)
    val tx = quickTxBuilder
        .compose(scriptTx)
        .feePayer(sender.baseAddress())
        .withSigner(SignerProviders.signerFrom(sender))
        .withRequiredSigners(pubKeyHashBytes)
        .ignoreScriptCostEvaluationError(false)
        .buildAndSign()
    System.err.println(tx.toJson)
    val result = backendService.getTransactionService.submitTransaction(tx.serialize())
    System.err.println(result)
}

private def showKeys(): Unit = {
    println(s"private key: ${privateKey.toHex}")
    println(s"public key: ${publicKey.toHex}")
}

private def server(): Unit = {
    Server.start()
}

@main def main(cmd: String, others: String*): Unit = {
    cmd match
        case "info" =>
            println(compiledBondScript.pretty.render(100))
            // println(bondProgram.doubleCborHex)
            // println(compiledHtlcScript.pretty.render(100))
            // println(htlcProgram.doubleCborHex)
            println(s"bondProgram size: ${bondProgram.doubleCborEncoded.length}")
            println(s"htlcProgram size: ${htlcProgram.doubleCborEncoded.length}")
        case "publish"       => publish()
        case "encrypt"       => encrypt(others.head, encryptIncorrectly = false)
        case "encrypt-wrong" => encrypt(others.head, encryptIncorrectly = true)
        case "decrypt"       => decrypt(others.head, others(1), spendIfWrong = false)
        case "spend-bond"    => decrypt(others.head, others(1), spendIfWrong = true)
        case "verify"        => verify(others.head)
        case "bond"          => makeBondTx()
        case "withdraw"      => withdraw(others.head, others(1))
        case "keys"          => showKeys()
        case "server"        => server()
}
