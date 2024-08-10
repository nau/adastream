package adastream
import adastream.BondContract.BondAction
import adastream.BondContract.BondConfig
import adastream.Encryption.chunksFromInputStream
import com.bloxbean.cardano.client.account.Account
import com.bloxbean.cardano.client.address.AddressProvider
import com.bloxbean.cardano.client.api.model.Amount
import com.bloxbean.cardano.client.backend.api.BackendService
import com.bloxbean.cardano.client.backend.api.DefaultUtxoSupplier
import com.bloxbean.cardano.client.backend.blockfrost.common.Constants
import com.bloxbean.cardano.client.backend.blockfrost.service.BFBackendService
import com.bloxbean.cardano.client.common.model.Network
import com.bloxbean.cardano.client.common.model.Networks
import com.bloxbean.cardano.client.crypto.cip1852.CIP1852
import com.bloxbean.cardano.client.crypto.cip1852.DerivationPath
import com.bloxbean.cardano.client.crypto.config.CryptoConfiguration
import com.bloxbean.cardano.client.function.helper.ScriptUtxoFinders
import com.bloxbean.cardano.client.function.helper.SignerProviders
import com.bloxbean.cardano.client.plutus.spec.*
import com.bloxbean.cardano.client.quicktx.QuickTxBuilder
import com.bloxbean.cardano.client.quicktx.ScriptTx
import com.bloxbean.cardano.client.quicktx.Tx
import com.monovore.decline.*
import scalus.*
import scalus.Compiler.compile
import scalus.bloxbean.EvaluatorMode
import scalus.bloxbean.Interop
import scalus.bloxbean.NoScriptSupplier
import scalus.bloxbean.ScalusTransactionEvaluator
import scalus.bloxbean.ScriptSupplier
import scalus.builtin.Builtins.*
import scalus.builtin.ByteString
import scalus.builtin.Data
import scalus.builtin.Data.ToData
import scalus.builtin.Data.toData
import scalus.builtin.PlatformSpecific
import scalus.builtin.given
import scalus.ledger.api.v2.*
import scalus.sir.RemoveRecursivity
import scalus.uplc.Program
import scalus.uplc.Term
import scalus.utils.Utils

import java.nio.file.Path
import scala.collection.immutable.ArraySeq
import scala.util.Random

case class Sender(account: Account) {
    lazy val privateKey = ByteString.fromArray(account.privateKeyBytes)
    lazy val publicKey = ByteString.fromArray(account.publicKeyBytes)
    lazy val publicKeyHash = ByteString.fromArray(account.hdKeyPair.getPublicKey.getKeyHash)
}

class AppCtx(
    network: Network,
    mnemonic: String,
    blockfrostApiKey: String | Null = System.getenv("BLOCKFROST_API_KEY")
) {
    lazy val sender = Sender(new Account(network, mnemonic))
    lazy val bondPlutusScript = PlutusV2Script
        .builder()
        .`type`("PlutusScriptV2")
        .cborHex(bondProgram.doubleCborHex)
        .build()
        .asInstanceOf[PlutusV2Script]
    lazy val scriptAddress =
        AddressProvider.getEntAddress(bondPlutusScript, network).toBech32()

    lazy val hdKeyPair = new CIP1852().getKeyPairFromMnemonic(
      mnemonic,
      DerivationPath.createExternalAddressDerivationPath(0)
    )

    lazy val backendService: BackendService =
        val url =
            if network == Networks.mainnet() then Constants.BLOCKFROST_MAINNET_URL
            else if network == Networks.preview() then Constants.BLOCKFROST_PREVIEW_URL
            else sys.error(s"Unsupported network: $network")
        Option(blockfrostApiKey)
            .map(new BFBackendService(url, _))
            .getOrElse(sys.error("BLOCKFROST_API_KEY environment variable is not set"))

}

val ps: PlatformSpecific = summon[PlatformSpecific]
private val compiledBondScript =
    compile(BondContract.bondContractValidator) |> RemoveRecursivity.apply
val bondValidator: Term = compiledBondScript.toUplcOptimized(generateErrorTraces = true)
val bondProgram: Program = Program((1, 0, 0), bondValidator)
private val compiledHtlcScript =
    compile(BondContract.makeHtlcContractValidator) |> RemoveRecursivity.apply
val xorBytesScript: Term = compile(BondContract.xorBytes).toUplcOptimized(generateErrorTraces = true)
private val htlcValidator = compiledHtlcScript.toUplcOptimized(generateErrorTraces = true)
private val htlcProgram = Program((1, 0, 0), htlcValidator)

lazy val ctx = AppCtx(
  network = Networks.preview(),
  mnemonic = Option(System.getenv("MNEMONIC")).getOrElse(
    "accident cluster album vacuum witness rather right clown liquid shallow liar myself now okay toy potato toe achieve sphere piano crush drum vivid jungle"
  )
)

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
    val signature =
        signingProvider.signExtended(claim.bytes, ctx.hdKeyPair.getPrivateKey.getKeyData)
    val fileOut = System.out
    fileOut.write(signature)
    fileOut.write(preimageHash.bytes)
    for (enc, hash) <- encryptedChunks.result().zip(hashes.result()) do
        fileOut.write(enc)
        fileOut.write(hash.bytes)
    System.err.println(s"preimage: ${Utils.bytesToHex(preimage)}")
    System.err.println(s"preimageHash: ${preimageHash.toHex}")
    System.err.println(s"pubKey: ${ctx.hdKeyPair.getPublicKey.getKeyData.toHex}")
    System.err.println(s"pubKeyHash: ${ctx.hdKeyPair.getPublicKey.getKeyHash.toHex}")
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
    val result = findBondUtxo(bondConfig)
    System.err.println(
      s"Looking up for bond UTxO with address ${ctx.scriptAddress} and bondConfig: $bondConfig"
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

    System.err.println(s"bond contract address: ${ctx.scriptAddress}")

    val quickTxBuilder = new QuickTxBuilder(ctx.backendService)
    val bondConfig = BondContract.BondConfig(
      paymentHash,
      encId,
      ctx.sender.publicKey,
      ctx.sender.publicKeyHash
    )
    val datumData = Interop.toPlutusData(bondConfig.toData)
    // val datumData = PlutusData.unit()
    val tx = new Tx()
        .payToContract(ctx.scriptAddress, Amount.ada(100), datumData)
        .from(ctx.sender.account.getBaseAddress.getAddress)

    val result = quickTxBuilder
        .compose(tx)
        .withSigner(SignerProviders.signerFrom(ctx.sender.account))
        .complete()
    println(result)
}

private def findBondUtxo(bondConfig: BondConfig) = {
    val utxoSupplier = new DefaultUtxoSupplier(ctx.backendService.getUtxoService)
    val datumData = Interop.toPlutusData(bondConfig.toData)
    ScriptUtxoFinders.findFirstByInlineDatum(utxoSupplier, ctx.scriptAddress, datumData)
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
      ctx.sender.publicKey,
      ctx.sender.publicKeyHash
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
    spendBond(ctx.sender.account, bondConfig, fraudProof)
}

def withdraw(preimage: String, encId: String): Unit = {
    val paymentHash = sha2_256(ByteString.fromHex(preimage))
    val bondConfig = BondContract.BondConfig(
      paymentHash,
      ByteString.fromHex(encId),
      ctx.sender.publicKey,
      ctx.sender.publicKeyHash
    )
    spendBond(ctx.sender.account, bondConfig, BondAction.Withdraw(ByteString.fromHex(preimage)))
}

private def spendBond(
    bondReceiver: Account,
    bondConfig: BondConfig,
    bondAction: BondAction
): Unit = {
    val utxoSupplier = new DefaultUtxoSupplier(ctx.backendService.getUtxoService)
    val protocolParams = ctx.backendService.getEpochService().getProtocolParameters().getValue()
    val scalusEvaluator = new ScalusTransactionEvaluator(protocolParams, utxoSupplier)
    val datumData = Interop.toPlutusData(bondConfig.toData)
    // val datumData = PlutusData.unit()
    val utxo =
        ScriptUtxoFinders.findFirstByInlineDatum(utxoSupplier, ctx.scriptAddress, datumData).get

    System.err.println(s"found utxo: $utxo")

    val redeemer = Interop.toPlutusData(bondAction.toData)
    val scriptTx = new ScriptTx()
        .collectFrom(utxo, redeemer)
        .payToAddress(bondReceiver.baseAddress(), utxo.getAmount)
        .attachSpendingValidator(ctx.bondPlutusScript)
    val pubKeyHashBytes = bondReceiver.hdKeyPair().getPublicKey.getKeyHash
    val quickTxBuilder = new QuickTxBuilder(ctx.backendService)
    val tx = quickTxBuilder
        .compose(scriptTx)
        .feePayer(bondReceiver.baseAddress())
        .withSigner(SignerProviders.signerFrom(bondReceiver))
        .withTxEvaluator(scalusEvaluator)
        .withRequiredSigners(pubKeyHashBytes)
        .ignoreScriptCostEvaluationError(false)
        .buildAndSign()
    System.err.println(tx.toJson)
    val result = ctx.backendService.getTransactionService.submitTransaction(tx.serialize())
    System.err.println(result)
}

private def showKeys(): Unit = {
    println(s"private key: ${ctx.sender.privateKey.toHex}")
    println(s"public key: ${ctx.sender.publicKey.toHex}")
}

private def server(secret: String, uploadDir: Path): Unit = {
    println(s"Starting server with public key: ${ctx.hdKeyPair.getPublicKey.getKeyData.toHex}")
    Server(ctx.hdKeyPair, ByteString.fromHex(secret), uploadDir).start()
}

private def info() = {
    println("AdaStream Bond contract")
    println(compiledBondScript.prettyXTerm.render(100))
    println(bondValidator.prettyXTerm.render(100))
    // println(bondProgram.doubleCborHex)
    println("AdaStream HTLC contract")
    println(compiledHtlcScript.prettyXTerm.render(100))
    println(htlcValidator.prettyXTerm.render(100))
    // println(htlcProgram.doubleCborHex)
    println(s"bondProgram size: ${bondProgram.doubleCborEncoded.length}")
    println(s"htlcProgram size: ${htlcProgram.doubleCborEncoded.length}")
}

enum Cmd:
    case Info, Publish, Bond, Keys
    case Encrypt(secret: String)
    case EncryptWrong(secret: String)
    case Decrypt(secret: String, publicKey: String)
    case Verify(pubKey: String)
    case SpendBond(secret: String, publicKey: String)
    case Withdraw(preimage: String, encId: String)
    case Server(secret: String, uploadDir: Path)

val adastreamCommand =
    import cats.implicits._
    val infoCommand = Opts.subcommand("info", "Prints the contract info") {
        Opts(Cmd.Info)
    }
    val publishCommand = Opts.subcommand("publish", "Computes the EncId and prints it to stdout") {
        Opts(Cmd.Publish)
    }
    val encryptCommand = Opts.subcommand("encrypt", "Encrypts stdin and writes to stdout") {
        Opts.argument[String]("secret").map(Cmd.Encrypt.apply)
    }
    val encryptWrongCommand = Opts.subcommand("encrypt-wrong", "Encrypts stdin incorrectly") {
        Opts.argument[String]("secret").map(Cmd.EncryptWrong.apply)
    }
    val decryptCommand = Opts.subcommand("decrypt", "Decrypts stdin and writes to stdout") {
        (Opts.argument[String]("secret"), Opts.argument[String]("public-key"))
            .mapN(Cmd.Decrypt.apply)
    }
    val spendBondCommand = Opts.subcommand("spend-bond", "Spends a bond") {
        (Opts.argument[String]("secret"), Opts.argument[String]("public-key"))
            .mapN(Cmd.SpendBond.apply)
    }
    val verifyCommand = Opts.subcommand("verify", "Verifies stdin with a public key") {
        Opts.argument[String]("public-key").map(Cmd.Verify.apply)
    }
    val bondCommand = Opts.subcommand("bond", "Creates and submits a bond transaction") {
        Opts(Cmd.Bond)
    }
    val withdrawCommand = Opts.subcommand("withdraw", "Withdraws a bond") {
        (Opts.argument[String]("preimage"), Opts.argument[String]("enc-id"))
            .mapN(Cmd.Withdraw.apply)
    }
    val keysCommand = Opts.subcommand("keys", "Shows keys") {
        Opts(Cmd.Keys)
    }
    val serverCommand = Opts.subcommand("server", "Starts a REST API server") {
        (Opts.argument[String]("secret"), Opts.argument[Path]("upload-dir")).mapN(Cmd.Server.apply)
    }

    Command(name = "adastream", header = "AdaStreams")(
      infoCommand
          orElse publishCommand
          orElse encryptCommand
          orElse encryptWrongCommand
          orElse decryptCommand
          orElse spendBondCommand
          orElse verifyCommand
          orElse bondCommand
          orElse withdrawCommand
          orElse keysCommand
          orElse serverCommand
    )

@main def main(args: String*): Unit = {
    adastreamCommand.parse(args) match
        case Left(help) => println(help)
        case Right(cmd) =>
            cmd match
                case Cmd.Info                      => info()
                case Cmd.Publish                   => publish()
                case Cmd.Encrypt(secret)           => encrypt(secret, encryptIncorrectly = false)
                case Cmd.EncryptWrong(secret)      => encrypt(secret, encryptIncorrectly = true)
                case Cmd.Decrypt(secret, pubKey)   => decrypt(secret, pubKey, spendIfWrong = false)
                case Cmd.SpendBond(secret, pubKey) => decrypt(secret, pubKey, spendIfWrong = true)
                case Cmd.Verify(pubKey)            => verify(pubKey)
                case Cmd.Bond                      => makeBondTx()
                case Cmd.Withdraw(preimage, encId) => withdraw(preimage, encId)
                case Cmd.Keys                      => showKeys()
                case Cmd.Server(secret, uploadDir) => server(secret, uploadDir)
}
