package adastream

import adastream.BondContract.{BondAction, BondConfig}
import org.bouncycastle.crypto.AsymmetricCipherKeyPair
import org.bouncycastle.crypto.generators.Ed25519KeyPairGenerator
import org.bouncycastle.crypto.params.{
    Ed25519KeyGenerationParameters,
    Ed25519PrivateKeyParameters,
    Ed25519PublicKeyParameters
}
import org.scalacheck.Prop.*
import org.scalacheck.{Arbitrary, Gen, Shrink}
import scalus.builtin.ByteString.StringInterpolators
import scalus.builtin.Data.toData
import scalus.builtin.ToDataInstances.given
import scalus.builtin.{ByteString, PlatformSpecific, given}
import scalus.ledger.api.v2.*
import scalus.ledger.api.v2.ToDataInstances.given
import scalus.uplc.TermDSL.{*, given}
import scalus.uplc.eval.*
import scalus.uplc.{DeBruijn, Program, Term, UplcParser}
import scalus.utils.Utils

import java.io.ByteArrayInputStream
import java.nio.file.Path
import java.security.SecureRandom
import scala.collection.immutable.ArraySeq
import scala.util.control.NonFatal

class ContractTests extends munit.ScalaCheckSuite {
    // generate ed25519 keys
    val RANDOM = new SecureRandom();
    val ps: PlatformSpecific = summon[PlatformSpecific]
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
    val preimageHash: ByteString = ByteString.unsafeFromArray(Utils.sha2_256(preimage.bytes))
    val encryptedChunk: ByteString = ByteString.fromArray(Utils.sha2_256("encryptedChunk".getBytes))
    val chunkHash: ByteString = ByteString.fromArray(Utils.sha2_256("chunkHash".getBytes))
    val encId: ByteString = MerkleTree.fromHashes(ArraySeq(encryptedChunk, chunkHash)).getMerkleRoot
    val bondConfig: BondConfig = BondConfig(
      preimageHash,
      encId,
      publicKey,
      ps.blake2b_224(publicKey)
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
            case UplcEvalResult.Success(term, budget, logs) =>
                assert(0 < budget.cpu && budget.cpu < 14_000000L)
                assert(0 < budget.memory && budget.memory < 50000L)
            case UplcEvalResult.UplcFailure(errorCode, error) =>
                fail(s"UplcFailure: $errorCode, $error")
        }
    }

    test("Server can't withdraw without a signature") {
        val withdraw = BondAction.Withdraw(preimage)
        evalBondValidator(bondConfig, withdraw, scalus.prelude.List.empty) {
            case UplcEvalResult.Success(term, _, _)           => fail(s"should fail")
            case UplcEvalResult.UplcFailure(errorCode, error) =>
        }
    }

    test("Server can't withdraw with a wrong signature") {
        val withdraw = BondAction.Withdraw(preimage)
        evalBondValidator(
          bondConfig,
          withdraw,
          scalus.prelude.List(PubKeyHash(ByteString.fromString("wrong")))
        ) {
            case UplcEvalResult.Success(term, _, _)           => fail(s"should fail")
            case UplcEvalResult.UplcFailure(errorCode, error) =>
        }
    }

    test("Server can't withdraw with a wrong preimage") {
        val withdraw = BondAction.Withdraw(preimage ++ ByteString.fromString("wrong"))
        evalBondValidator(
          bondConfig,
          withdraw,
          scalus.prelude.List(PubKeyHash(bondConfig.serverPubKeyHash))
        ) {
            case UplcEvalResult.Success(term, _, logs) =>
                fail(s"should fail but got result $term with logs $logs")
            case UplcEvalResult.UplcFailure(errorCode, error) =>
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
              ps.blake2b_224(publicKey)
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
                case UplcEvalResult.Success(term, budget, _) =>
                    assert(budget.cpu < 2_000_000000L)
                    assert(budget.memory < 3_000000L)
                    true
                case UplcEvalResult.UplcFailure(errorCode, error) =>
                    fail(s"errorCode: $errorCode, error: $error")
                    false
            }
        }
    }

    def evalBondValidator[A](
        bondConfig: BondConfig,
        withdraw: BondAction,
        signatures: scalus.prelude.List[PubKeyHash]
    )(pf: PartialFunction[UplcEvalResult, A]): A = {
        val scriptContext = makeScriptContext(signatures)
        val term =
            bondValidator $ bondConfig.toData $ withdraw.toData $ makeScriptContext(
              signatures
            ).toData
        val result = PlutusUplcEval.evalFlat(Program((1, 0, 0), term))
        val tallyingBudgetSpender = TallyingBudgetSpender(CountingBudgetSpender())
        val logger = Log()
        val cekMachine = CekMachine(
          MachineParams.defaultParams,
          tallyingBudgetSpender,
          logger,
          summon[PlatformSpecific]
        )
        val debruijnedTerm = DeBruijn.deBruijnTerm(term)
        try cekMachine.evaluateTerm(debruijnedTerm)
        catch case NonFatal(e) => ()
        val r = tallyingBudgetSpender.budgetSpender.getSpentBudget
        def showBudget(budget: ExBudget): String =
            s"%.6f / %.6f".format(budget.cpu / 1000000d, budget.memory / 1000000d)
        result match
            case UplcEvalResult.TermParsingError(error) => fail(s"TermParsingError: $error")
            case UplcEvalResult.Success(_, budget, logs) =>
//                println(logs)
//                println(s"budget: ${showBudget(budget)}, scalus budget: ${showBudget(r)}")
//                if budget != r then
//                    println(s"diff: ${budget.cpu - r.cpu}, ${budget.memory - r.memory}")
                /*println(
                  s"Execution stats:\n${tallyingBudgetSpender.costs.toArray
                          .sortBy(_._1.toString())
                          .map { case (k, v) =>
                              s"$k: ${showBudget(v)}"
                          }
                          .mkString("\n")}"
                )*/
                pf(result)
            case other => pf(other)
    }

    test("calculateFileIdAndEncId") {
        val (fileId, encId) =
            Encryption.calculateFileIdAndEncId(Path.of("bitcoin.pdf"), preimage.bytes)
        assertEquals(
          fileId.toHex,
          "09E15338990511F7E8D8B8E9BE27ECC6ABE5CE3205E7DFF2A597A27C4148D577"
        )
        assertEquals(
          encId.toHex,
          "065D1EBC27E1390C56D5C05275A1FC741F8256E181462605BB76FAA94B1D34C3"
        )
    }

    test("xorBytes performance") {
        val term = xorBytesScript $ BigInt(1) $ BigInt(2)
        val result = PlutusUplcEval.evalFlat(Program((1, 0, 0), term))
        result match
            case UplcEvalResult.Success(term, budget, logs)   =>
                assertEquals(budget.cpu, 31_043509L)
                assertEquals(budget.memory, 55706L)
            case UplcEvalResult.TermParsingError(error)       => fail(s"TermParsingError: $error")
            case UplcEvalResult.UplcFailure(errorCode, error) => fail(s"error: $error")
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

enum UplcEvalResult:
    case Success(term: Term, budget: ExBudget, logs: String = "")
    case UplcFailure(errorCode: Int, error: String)
    case TermParsingError(error: String)

object PlutusUplcEval:
    def evalFlat(program: Program): UplcEvalResult =
        import cats.implicits.toShow
        val flat = program.flatEncoded
        // println(s"Flat size: ${flat.length}}")
        import scala.sys.process.*
        val cmd =
            "uplc evaluate --input-format flat --trace-mode LogsWithBudgets -c --print-mode Debug"
        var out = ""
        val retCode = cmd.#<(new ByteArrayInputStream(flat)).!(ProcessLogger(o => out += o + "\n"))
        if retCode == 0 then
            UplcParser.term.parse(out) match
                case Right(remaining, term) =>
                    val budget = raw"(?s)CPU budget:\s+(\d+)\RMemory budget:\s+(\d+)\R(.+)".r
                    remaining match
                        case budget(cpu, memory, logs) =>
                            UplcEvalResult.Success(
                              term,
                              ExBudget.fromCpuAndMemory(cpu.toLong, memory.toLong),
                              logs
                            )
                        case _ => UplcEvalResult.Success(term, ExBudget.zero, remaining)
                case Left(err) => UplcEvalResult.TermParsingError(err.show)
        else UplcEvalResult.UplcFailure(retCode, out)
