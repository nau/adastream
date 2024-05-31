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
import scalus.*
import scalus.Compiler.compile
import scalus.builtin.Builtins.*
import scalus.builtin.Data.{ToData, toData}
import scalus.builtin.{ByteString, Data, PlatformSpecific, given}
import scalus.ledger.api.v2.*
import scalus.uplc.{Program, Term}
import scalus.utils.Utils

import java.nio.file.Path
import scala.collection.immutable.ArraySeq
import scala.util.Random
import scalus.bloxbean.Interop
import scalus.bloxbean.ScalusTransactionEvaluator
import scalus.bloxbean.ScriptSupplier
import scalus.bloxbean.NoScriptSupplier
import scalus.bloxbean.EvaluatorMode
import com.bloxbean.cardano.client.common.model.Network

case class Sender(
    network: Network,
    sender: Account
) {
    lazy val privateKey = ByteString.fromArray(sender.privateKeyBytes)
    lazy val publicKey = ByteString.fromArray(sender.publicKeyBytes)
    lazy val publicKeyHash = ByteString.fromArray(sender.hdKeyPair.getPublicKey.getKeyHash)
}

private val ps: PlatformSpecific = summon[PlatformSpecific]
private val compiledBondScript = compile(BondContract.bondContractValidator)
val bondValidator: Term = compiledBondScript.toUplc(generateErrorTraces = true)
val bondProgram: Program = Program((1, 0, 0), bondValidator)
private val compiledHtlcScript = compile(BondContract.makeHtlcContractValidator)
val xorBytesScript: Term = compile(BondContract.xorBytes).toUplc(generateErrorTraces = true)
private val htlcValidator = compiledHtlcScript.toUplc(generateErrorTraces = true)
private val htlcProgram = Program((1, 0, 0), htlcValidator)

lazy val sender = Sender(Networks.preview(), new Account(Networks.preview(), System.getenv("MNEMONIC")))

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
    )
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
    System.err.println(s"pubKeyHash: ${hdKeyPair.getPublicKey.getKeyHash.toHex}")
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
      sender.publicKey,
      sender.publicKeyHash
    )
    val datumData = Interop.toPlutusData(bondConfig.toData)
    // val datumData = PlutusData.unit()
    val tx = new Tx()
        .payToContract(scriptAddress, Amount.ada(100), datumData)
        .from(sender.sender.getBaseAddress.getAddress)

    val result = quickTxBuilder
        .compose(tx)
        .withSigner(SignerProviders.signerFrom(sender.sender))
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
    val datumData = Interop.toPlutusData(bondConfig.toData)
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
      sender.publicKey,
      sender.publicKeyHash
    )
    System.err.println(s"bondConfig: $bondConfig")
    val fraudProof = BondAction.FraudProof(
      signature = signature,
      password = preimage,
      encryptedChunk = encryptedChunk,
      chunkHash = chunkHash,
      chunkIndex = chunkIndex,
      merkleProof = Data.List(merkleProof.map(bData).toList)
    )
    spendBond(sender.sender, bondConfig, fraudProof)
}

def withdraw(preimage: String, encId: String): Unit = {
    val paymentHash = sha2_256(ByteString.fromHex(preimage))
    val bondConfig = BondContract.BondConfig(
      paymentHash,
      ByteString.fromHex(encId),
      sender.publicKey,
      sender.publicKeyHash
    )
    spendBond(sender.sender, bondConfig, BondAction.Withdraw(ByteString.fromHex(preimage)))
}

private def spendBond(sender: Account, bondConfig: BondConfig, bondAction: BondAction): Unit = {
    val plutusScript = PlutusV2Script
        .builder()
        .cborHex(bondProgram.doubleCborHex)
        .build();

    val scriptAddress =
        AddressProvider.getEntAddress(plutusScript, Networks.preview()).toBech32()

    val backendService = new BFBackendService(
      Constants.BLOCKFROST_PREVIEW_URL,
      System.getenv("BLOCKFROST_API_KEY")
    )
    val utxoSupplier = new DefaultUtxoSupplier(backendService.getUtxoService)
    val protocolParams = backendService.getEpochService().getProtocolParameters().getValue()
    val scalusEvaluator = new ScalusTransactionEvaluator(protocolParams, utxoSupplier)
    val datumData = Interop.toPlutusData(bondConfig.toData)
    // val datumData = PlutusData.unit()
    val utxo =
        ScriptUtxoFinders.findFirstByInlineDatum(utxoSupplier, scriptAddress, datumData).get

    System.err.println(s"found utxo: $utxo")

    val redeemer = Interop.toPlutusData(bondAction.toData)
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
        .withTxEvaluator(scalusEvaluator)
        .withRequiredSigners(pubKeyHashBytes)
        .ignoreScriptCostEvaluationError(false)
        .buildAndSign()
    System.err.println(tx.toJson)
    val result = backendService.getTransactionService.submitTransaction(tx.serialize())
    System.err.println(result)
}

private def showKeys(): Unit = {
    println(s"private key: ${sender.privateKey.toHex}")
    println(s"public key: ${sender.publicKey.toHex}")
}

private def server(secret: String, uploadDir: Path): Unit = {
    // val mnemonic = "face reform cry tissue august tell hair dress jungle useful stamp mean traffic donor shy youth engine wine champion chair crush note member window"
    val mnemonic = System.getenv("MNEMONIC")
    val hdKeyPair = new CIP1852()
        .getKeyPairFromMnemonic(mnemonic, DerivationPath.createExternalAddressDerivationPath(0))
    println(s"Starting server with public key: ${hdKeyPair.getPublicKey.getKeyData.toHex}")
    Server(hdKeyPair, ByteString.fromHex(secret), uploadDir).start()
}

@main def main(cmd: String, others: String*): Unit = {
    cmd match
        case "info" =>
            println(compiledBondScript.prettyXTerm.render(100))
            // println(bondProgram.doubleCborHex)
            println(compiledHtlcScript.prettyXTerm.render(100))
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
        case "server"        => server(others.head, Path.of(others(1)))
}
