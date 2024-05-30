package adastream

import adastream.BondContract.BondAction
import adastream.BondContract.BondConfig
import org.bouncycastle.crypto.AsymmetricCipherKeyPair
import org.bouncycastle.crypto.generators.Ed25519KeyPairGenerator
import org.bouncycastle.crypto.params.Ed25519KeyGenerationParameters
import org.bouncycastle.crypto.params.Ed25519PrivateKeyParameters
import org.bouncycastle.crypto.params.Ed25519PublicKeyParameters
import org.scalacheck.Arbitrary
import org.scalacheck.Gen
import org.scalacheck.Prop.*
import org.scalacheck.Shrink
import scalus.builtin.ByteString
import scalus.builtin.ByteString.StringInterpolators
import scalus.builtin.Data.toData
import scalus.builtin.PlatformSpecific
import scalus.builtin.ToDataInstances.given
import scalus.builtin.given
import scalus.ledger.api.v2.*
import scalus.ledger.api.v2.ToDataInstances.given
import scalus.uplc.DeBruijn
import scalus.uplc.Program
import scalus.uplc.Term
import scalus.uplc.TermDSL.{*, given}
import scalus.uplc.UplcParser
import scalus.uplc.eval.*
import scalus.utils.Utils

import java.io.ByteArrayInputStream
import java.nio.file.Path
import java.security.SecureRandom
import scala.collection.immutable.ArraySeq
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
        assert(bondProgram.doubleCborEncoded.length == 1063)
    }

    test("Server can withdraw with valid preimage and signature") {
        val withdraw = BondAction.Withdraw(preimage)
        evalBondValidator(
          bondConfig,
          withdraw,
          scalus.prelude.List(PubKeyHash(bondConfig.serverPubKeyHash))
        ) {
            case Right(CekResult(budget, logs)) =>
                assert(0 < budget.cpu && budget.cpu < 14_000000L)
                assert(0 < budget.memory && budget.memory < 50000L)
            case Left((e, res)) =>
                fail(s"Consumed ${showBudget(res.budget)}\nLogs: ${res.logs.mkString("\n")}", e)
        }
    }

    val newValue = {
        val withdraw = BondAction.Withdraw(preimage)
        evalBondValidator(bondConfig, withdraw, scalus.prelude.List.empty) {
            case Right(_)                   => fail(s"should fail")
            case Left((_: BuiltinError, _)) =>
            case Left((e, r))               => fail(s"Unexpected error with $r", e)
        }
    }
    test("Server can't withdraw without a signature")(newValue)

    test("Server can't withdraw with a wrong signature") {
        val withdraw = BondAction.Withdraw(preimage)
        evalBondValidator(
          bondConfig,
          withdraw,
          scalus.prelude.List(PubKeyHash(ByteString.fromString("wrong")))
        ) {
            case Right(_)                        => fail(s"should fail")
            case Left((_: EvaluationFailure, _)) =>
            case Left((e, r))                    => fail(s"Unexpected error with $r", e)
        }
    }

    test("Server can't withdraw with a wrong preimage") {
        val withdraw = BondAction.Withdraw(preimage ++ ByteString.fromString("wrong"))
        evalBondValidator(
          bondConfig,
          withdraw,
          scalus.prelude.List(PubKeyHash(bondConfig.serverPubKeyHash))
        ) {
            case Right(_)                        => fail(s"should fail")
            case Left((_: EvaluationFailure, _)) =>
            case Left((e, r))                    => fail(s"Unexpected error with $r", e)
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

            evalBondValidator(bondConfig, action, scalus.prelude.List.empty) {
                case Right(CekResult(budget, _)) =>
                    assert(budget.cpu < 2_000_000000L)
                    assert(budget.memory < 3_000000L)
                    true
                case Left((e, r)) =>
                    fail(r.toString, e)
                    false
            }
        }
    }

    def evalTerm(term: Term): Either[(Throwable, CekResult), CekResult] =
        val tallyingBudgetSpender = TallyingBudgetSpender(CountingBudgetSpender())
        val logger = Log()
        val cekMachine = CekMachine(
          MachineParams.defaultParams,
          tallyingBudgetSpender,
          logger,
          summon[PlatformSpecific]
        )
        val debruijnedTerm = DeBruijn.deBruijnTerm(term)
        try
            cekMachine.evaluateTerm(debruijnedTerm)
            val budget = tallyingBudgetSpender.budgetSpender.getSpentBudget
            Right(CekResult(budget, logger.getLogs.toSeq))
        catch
            case NonFatal(e) =>
                val budget = tallyingBudgetSpender.budgetSpender.getSpentBudget
                Left((e, CekResult(budget, logger.getLogs.toSeq)))

    def evalBondValidator[A](
        bondConfig: BondConfig,
        withdraw: BondAction,
        signatures: scalus.prelude.List[PubKeyHash]
    )(pf: PartialFunction[Either[(Throwable, CekResult), CekResult], A]): A = {
        val scriptContext = makeScriptContext(signatures)
        val term =
            bondValidator $ bondConfig.toData $ withdraw.toData $ makeScriptContext(
              signatures
            ).toData
        val result = evalTerm(term)
        pf(result)
    }

    private def showBudget(budget: ExBudget): String =
        s"%.6f / %.6f".format(budget.cpu / 1000000d, budget.memory / 1000000d)

    private def showTallyingBudgetSpender(tallyingBudgetSpender: TallyingBudgetSpender): String =
        tallyingBudgetSpender.costs.toArray
            .sortBy(_._1.toString())
            .map { case (k, v) =>
                s"$k: ${showBudget(v)}"
            }
            .mkString("\n")

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
        val result = evalTerm(term)
        result match
            case Right(r) =>
                assertEquals(r.budget.cpu, 31_043509L)
                assertEquals(r.budget.memory, 55706L)
            case Left((e, r)) => fail(s"Consumed ${showBudget(r.budget)}", e)
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

    def makeScriptContext(signatories: scalus.prelude.List[PubKeyHash]): ScriptContext =
        ScriptContext(
          TxInfo(
            inputs = scalus.prelude.List.Nil,
            referenceInputs = scalus.prelude.List.Nil,
            outputs = scalus.prelude.List.Nil,
            fee = Value.lovelace(BigInt("188021")),
            mint = Value.zero,
            dcert = scalus.prelude.List.Nil,
            withdrawals = scalus.prelude.AssocMap.empty,
            validRange = Interval.always,
            signatories = signatories,
            redeemers = scalus.prelude.AssocMap.empty,
            data = scalus.prelude.AssocMap.empty,
            id = TxId(hex"1e0612fbd127baddfcd555706de96b46c4d4363ac78c73ab4dee6e6a7bf61fe9")
          ),
          ScriptPurpose.Spending(
            TxOutRef(
              TxId(hex"1ab6879fc08345f51dc9571ac4f530bf8673e0d798758c470f9af6f98e2f3982"),
              0
            )
          )
        )
}
