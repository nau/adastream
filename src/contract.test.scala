package adastream

import adastream.BondContract.BondAction
import adastream.BondContract.BondConfig
import com.bloxbean.cardano.client.backend.blockfrost.service.http.TransactionApi
import com.bloxbean.cardano.client.common.ADAConversionUtil
import com.bloxbean.cardano.client.function.TxBuilder
import com.bloxbean.cardano.client.plutus.spec.ExUnits
import com.bloxbean.cardano.client.plutus.spec.PlutusV2Script
import com.bloxbean.cardano.client.plutus.spec.Redeemer
import com.bloxbean.cardano.client.plutus.spec.RedeemerTag
import com.bloxbean.cardano.client.quicktx.QuickTxBuilder
import com.bloxbean.cardano.client.quicktx.ScriptTx
import com.bloxbean.cardano.client.transaction.spec
import com.bloxbean.cardano.client.transaction.spec.Transaction
import com.bloxbean.cardano.client.transaction.spec.TransactionBody
import com.bloxbean.cardano.client.transaction.spec.TransactionInput
import com.bloxbean.cardano.client.transaction.spec.TransactionOutput
import com.bloxbean.cardano.client.transaction.spec.TransactionWitnessSet
import io.bullet.borer.Cbor
import org.bouncycastle.crypto.AsymmetricCipherKeyPair
import org.bouncycastle.crypto.generators.Ed25519KeyPairGenerator
import org.bouncycastle.crypto.params.Ed25519KeyGenerationParameters
import org.bouncycastle.crypto.params.Ed25519PrivateKeyParameters
import org.bouncycastle.crypto.params.Ed25519PublicKeyParameters
import org.scalacheck.Arbitrary
import org.scalacheck.Gen
import org.scalacheck.Prop.*
import org.scalacheck.Shrink
import scalus.bloxbean.Interop
import scalus.bloxbean.SlotConfig
import scalus.builtin.ByteString
import scalus.builtin.ByteString.StringInterpolators
import scalus.builtin.Data
import scalus.builtin.Data.toData
import scalus.builtin.PlatformSpecific
import scalus.builtin.ToDataInstances.given
import scalus.builtin.given
import scalus.ledger.api.v2.*
import scalus.ledger.api.v2.ToDataInstances.given
import scalus.prelude
import scalus.uplc.DeBruijn
import scalus.uplc.Program
import scalus.uplc.Term
import scalus.uplc.TermDSL.{*, given}
import scalus.uplc.UplcParser
import scalus.uplc.eval
import scalus.uplc.eval.*
import scalus.utils.Utils

import java.io.ByteArrayInputStream
import java.math.BigInteger
import java.nio.file.Path
import java.security.SecureRandom
import java.util
import scala.collection.immutable.ArraySeq
import scala.jdk.CollectionConverters.*
import scala.language.implicitConversions
import scala.util.control.NonFatal

case class CekResult(budget: ExBudget, logs: Seq[String])

class ContractTests extends munit.ScalaCheckSuite {
    // generate ed25519 keys
    val RANDOM = new SecureRandom();
    val crypto = summon[PlatformSpecific]
    val keyPairGenerator = new Ed25519KeyPairGenerator();
    keyPairGenerator.init(new Ed25519KeyGenerationParameters(RANDOM));
    val asymmetricCipherKeyPair: AsymmetricCipherKeyPair = keyPairGenerator.generateKeyPair();
    val privateKey: Ed25519PrivateKeyParameters =
        asymmetricCipherKeyPair.getPrivate.asInstanceOf[Ed25519PrivateKeyParameters];
    val publicKeyParams: Ed25519PublicKeyParameters =
        asymmetricCipherKeyPair.getPublic.asInstanceOf[Ed25519PublicKeyParameters];
    val publicKey: ByteString = ByteString.fromArray(publicKeyParams.getEncoded)
    val preimage: ByteString =
        ByteString.fromHex("a64cf172224cab7a1b1da28e14719a810b5de126141d066892dada6b6b6e7ccd")
    val preimageHash: ByteString = crypto.sha2_256(preimage)
    val encryptedChunk: ByteString = crypto.sha2_256(ByteString.fromString("encryptedChunk"))
    val chunkHash: ByteString = crypto.sha2_256(ByteString.fromString("chunkHash"))
    val encId: ByteString = MerkleTree.fromHashes(ArraySeq(encryptedChunk, chunkHash)).getMerkleRoot
    val bondConfig: BondConfig = BondConfig(
      preimageHash,
      encId,
      publicKey,
      crypto.blake2b_224(publicKey)
    )

    test(s"bondProgram size is ${bondProgram.doubleCborEncoded.length}") {
        assertEquals(bondProgram.doubleCborEncoded.length, 1190)
    }

    test(s"htlcProgram size is ${htlcProgram.doubleCborEncoded.length}") {
        assertEquals(htlcProgram.doubleCborEncoded.length, 393)
    }

    test("Server can withdraw with valid preimage and signature") {
        val withdraw = BondAction.Withdraw(preimage)
        evalBondValidator(
          bondConfig,
          withdraw,
          Seq(PubKeyHash(bondConfig.serverPubKeyHash))
        ) {
            case eval.Result.Success(_, budget, _, logs) =>
                assertEquals(budget.cpu, 10_968166L)
                assertEquals(budget.memory, 32160L)
            case res @ eval.Result.Failure(ex, _, _, _) =>
                fail(res.toString, ex)
        }
    }

    test("Server can't withdraw without a signature") {
        val withdraw = BondAction.Withdraw(preimage)
        evalBondValidator(bondConfig, withdraw, Seq.empty) {
            case r: eval.Result.Success                        => fail(s"should fail: $r")
            case eval.Result.Failure(_: BuiltinError, _, _, _) =>
            case r @ eval.Result.Failure(e, _, _, _)           => fail(s"$r", e)
        }
    }

    test("Server can't withdraw with a wrong signature") {
        val withdraw = BondAction.Withdraw(preimage)
        evalBondValidator(
          bondConfig,
          withdraw,
          Seq(PubKeyHash(ByteString.fromString("wrong")))
        ) {
            case r: eval.Result.Success                             => fail(r.toString())
            case eval.Result.Failure(_: EvaluationFailure, _, _, _) =>
            case r @ eval.Result.Failure(e, _, _, _)                => fail(s"$r", e)
        }
    }

    test("Server can't withdraw with a wrong preimage") {
        val withdraw = BondAction.Withdraw(preimage ++ ByteString.fromString("wrong"))
        evalBondValidator(
          bondConfig,
          withdraw,
          Seq(PubKeyHash(bondConfig.serverPubKeyHash))
        ) {
            case r: eval.Result.Success                             => fail(s"should fail: $r")
            case eval.Result.Failure(_: EvaluationFailure, _, _, _) =>
            case r @ eval.Result.Failure(e, _, _, _)                => fail(s"$r", e)
        }
    }

    property("Client can spend with valid fraud proof") {
        val gen = for
            numChuns <- Gen.frequency(
              (500, Gen.choose(1, 1000)),
              (5, Gen.choose(10_000, 100_000))
            )
            wrongChunkIndex <- Gen.choose(0, numChuns - 1)
            randomChunks <- Gen.listOfN(
              numChuns,
              Gen.containerOfN[ArraySeq, Byte](32, Arbitrary.arbitrary[Byte]).map(_.toArray)
            )
        yield (wrongChunkIndex, randomChunks)
        forAll(gen) { (wrongChunkIndex, randomChunks) =>
            collect(randomChunks.size)
            val hashes = ArraySeq.newBuilder[ByteString]
            val encHashes = ArraySeq.newBuilder[ByteString]
            var wrongEncryptedChunk: ByteString = null
            var wrongChunkHash: ByteString = null
            for (chunk, index) <- randomChunks.zipWithIndex do
                val hash = Utils.sha2_256(chunk)
                val encrypted =
                    if index == wrongChunkIndex then
                        val wrong = Utils.sha2_256("wrong".getBytes)
                        wrongEncryptedChunk = ByteString.fromArray(wrong)
                        wrongChunkHash = ByteString.fromArray(hash)
                        wrong
                    else Encryption.encryptChunk(chunk, preimage.bytes, index)
                val encHash = Utils.sha2_256(encrypted ++ hash)
                hashes += ByteString.fromArray(hash)
                encHashes += ByteString.fromArray(encHash)
            val fileId = MerkleTree.fromHashes(hashes.result()).getMerkleRoot
            val merkleTree = MerkleTree.fromHashes(encHashes.result())
            val encId = merkleTree.getMerkleRoot
            val bondConfig = BondConfig(
              preimageHash,
              encId,
              publicKey,
              crypto.blake2b_224(publicKey)
            )
            val claim = bondConfig.encryptedId ++ bondConfig.passwordHash
            val signature = Encryption.signMessage(claim, privateKey)
            val merkleProof = scalus.builtin.Data.List(
              merkleTree.makeMerkleProof(wrongChunkIndex).map(_.toData).toList
            )
            val action =
                BondAction.FraudProof(
                  signature = signature,
                  password = preimage,
                  encryptedChunk = wrongEncryptedChunk,
                  chunkHash = wrongChunkHash,
                  chunkIndex = wrongChunkIndex,
                  merkleProof = merkleProof
                )

            evalBondValidator(bondConfig, action, Seq.empty) {
                case eval.Result.Success(_, budget, _, _) =>
                    assert(budget.cpu < 2_000_000000L)
                    assert(budget.memory < 3_000000L)
                    true
                case r @ eval.Result.Failure(e, _, _, _) =>
                    fail(r.toString, e)
                    false
            }
        }
    }

    def evalBondValidator[A](
        bondConfig: BondConfig,
        withdraw: BondAction,
        signatures: Seq[PubKeyHash]
    )(pf: PartialFunction[eval.Result, A]): A = {
        val datum = bondConfig.toData
        val redeemer = withdraw.toData
        val scriptContext = makeScriptContext(datum, redeemer, signatures)
        val term = bondValidator $ datum $ redeemer $ scriptContext.toData
        val result = VM.evaluateDebug(term)
        pf(result)
    }

    test("calculateFileIdAndEncId") {
        val (fileId, encId) =
            Encryption.calculateFileIdAndEncId(Path.of("bitcoin.pdf"), preimage.bytes)
        assertEquals(
          fileId.toHex,
          "09e15338990511f7e8d8b8e9be27ecc6abe5ce3205e7dff2a597a27c4148d577"
        )
        assertEquals(
          encId.toHex,
          "065d1ebc27e1390c56d5c05275a1fc741f8256e181462605bb76faa94b1d34c3"
        )
    }

    test("xorBytes performance") {
        val term = xorBytesScript $ BigInt(1) $ BigInt(2)
        val result = VM.evaluateDebug(term)
        result match
            case r: eval.Result.Success =>
                assertEquals(r.budget.cpu, 31_043509L)
                assertEquals(r.budget.memory, 55706L)
            case r @ eval.Result.Failure(e, _, _, _) => fail(s"Consumed ${r.budget.showJson}", e)
    }

    property("BondContract.xorBytes is the same as BigInt.xor") {
        forAll { (n1: Int, n2: Int) =>
            val absn1 = n1 & 0xff
            val absn2 = n2 & 0xff
            BondContract.xorBytes(BigInt(absn1), BigInt(absn2)) == (absn1 ^ absn2)
        }
    }

    property("BondContract.xor is the same as BigInt.xor") {
        val gen = for {
            len <- Gen.choose(1, 100)
            ba1 <- Gen.listOfN(len, Arbitrary.arbitrary[Byte]).map(_.toArray)
            ba2 <- Gen.listOfN(len, Arbitrary.arbitrary[Byte]).map(_.toArray)
        } yield (ba1, ba2)
        forAll(gen) { case (ba1, ba2) =>
            val bs1 = ByteString.unsafeFromArray(ba1)
            val bs2 = ByteString.unsafeFromArray(ba2)
            val bi1 = BigInt.apply(bs1.toHex, 16)
            val bi2 = BigInt.apply(bs2.toHex, 16)
            val bs3 = BondContract.xor(bs1, bs2).toHex
            BigInt.apply(bs3, 16) == (bi1 ^ bi2)
        }
    }

    property("integerToByteString is correct") {
        forAll { (n: Int) =>
            val positive = n & 0x7fffffff
            val bs = BondContract.integerToByteString(positive)
            val bi = BigInt.apply(bs.toHex, 16)
            bi == positive
        }
    }

    given Arbitrary[ByteString] = Arbitrary {
        for {
            len <- Gen.choose(1, 100)
            ba <- Gen.listOfN(len, Arbitrary.arbitrary[Byte]).map(_.toArray)
        } yield ByteString.unsafeFromArray(ba)
    }

    property(
      "for any elements their merkle tree root is the same as merkle tree root from a random index merkle proof"
    ) {
        val elementsGen =
            for
                n <- Gen.choose(1, 100)
                index <- Gen.choose(0, n - 1)
                elements <- Gen.containerOfN[ArraySeq, ByteString](
                  n,
                  Arbitrary
                      .arbitrary[ByteString]
                      .map(bs => ByteString.unsafeFromArray(Utils.sha2_256(bs.bytes)))
                )
            yield (elements, index)
        forAll(elementsGen) { (elements: ArraySeq[ByteString], index: Int) =>
            val tree = MerkleTree.fromHashes(elements)
            val root = tree.getMerkleRoot
            val proof = tree.makeMerkleProof(index)
            val result = MerkleTree.calculateMerkleRootFromProof(index, elements(index), proof)
            assert(result == root)
        }
    }

    def makeScriptContext(
        datum: Data,
        redeemer: Data,
        signatories: Seq[PubKeyHash]
    ): ScriptContext =
        val payeeAddress = ctx.sender.account.baseAddress()
        val rdmr =
            Redeemer
                .builder()
                .tag(RedeemerTag.Spend)
                .data(Interop.toPlutusData(redeemer))
                .index(BigInteger.valueOf(0))
                .exUnits(
                  ExUnits
                      .builder()
                      .steps(BigInteger.valueOf(1000))
                      .mem(BigInteger.valueOf(1000))
                      .build()
                )
                .build()

        val input = TransactionInput
            .builder()
            .transactionId("1ab6879fc08345f51dc9571ac4f530bf8673e0d798758c470f9af6f98e2f3982")
            .index(0)
            .build()
        val inputs = util.List.of(input)

        val utxo = Map(
          input -> TransactionOutput
              .builder()
              .value(spec.Value.builder().coin(BigInteger.valueOf(20)).build())
              .address(payeeAddress)
              .inlineDatum(Interop.toPlutusData(datum))
              .build()
        )
        val tx = Transaction
            .builder()
            .body(
              TransactionBody
                  .builder()
                  .fee(ADAConversionUtil.adaToLovelace(0.2))
                  .inputs(inputs)
                  .requiredSigners(signatories.map(_.hash.bytes).asJava)
                  .build()
            )
            .witnessSet(
              TransactionWitnessSet
                  .builder()
                  .plutusV2Scripts(util.List.of(ctx.bondPlutusScript))
                  .redeemers(util.List.of(rdmr))
                  .build()
            )
            .build()

        val purpose = Interop.getScriptPurpose(
          rdmr,
          tx.getBody().getInputs(),
          util.List.of(),
          util.List.of(),
          util.List.of()
        )
        val datumCbor = ByteString.fromArray(Cbor.encode(datum).toByteArray)
        val datumHash = crypto.blake2b_256(datumCbor)
        val datums = Seq((datumHash, datum))
        val protocolVersion = 8
        val txInfo = Interop.getTxInfoV2(tx, datums, utxo, SlotConfig.default, protocolVersion)
        val scriptContext = ScriptContext(txInfo, purpose)
        scriptContext
}
