//> using scala 3.3.0
//> using test.dep org.scalameta::munit::1.0.0-M10
//> using test.dep org.scalameta::munit-scalacheck::1.0.0-M10
//> using test.dep org.scalacheck::scalacheck::1.17.0
//> using dep org.scalus:scalus_3:0.3.0
//> using dep org.bouncycastle:bcprov-jdk18on:1.76
//> using dep com.bloxbean.cardano:cardano-client-lib:0.5.0

package adastream

import org.scalacheck.Prop.*
import scalus.builtins.ByteString
import org.scalacheck.Gen
import org.scalacheck.Arbitrary
import java.io.ByteArrayInputStream
import scalus.builtins.Builtins
import scalus.toUplc
import scalus.uplc.Data.toData
import scalus.utils.Utils
import scalus.uplc.Program
import scalus.uplc.TermDSL.{*, given}
import scalus.uplc.ToDataInstances.given
import scalus.ledger.api.v2.ToDataInstances.given
import adastream.BondContract.BondConfig
import adastream.BondContract.BondAction
import scalus.ledger.api.v1.PubKeyHash
import scalus.ledger.api.v2.*
import scalus.builtins.ByteString.StringInterpolators
import scalus.ledger.api.v1.PubKeyHash
import scalus.uplc.Term
import scalus.uplc.UplcParser
import scala.util.matching.Regex
import java.security.SecureRandom
import org.bouncycastle.crypto.generators.Ed25519KeyPairGenerator
import org.bouncycastle.crypto.params.Ed25519KeyGenerationParameters
import org.bouncycastle.crypto.params.Ed25519PrivateKeyParameters
import org.bouncycastle.crypto.params.Ed25519PublicKeyParameters
import org.bouncycastle.crypto.signers.Ed25519Signer
import java.nio.charset.StandardCharsets
import com.bloxbean.cardano.client.crypto.api.impl.EdDSASigningProvider
import org.bouncycastle.crypto.digests.Blake2bDigest
import scala.collection.immutable.ArraySeq
import org.scalacheck.Shrink

class ContractTests extends munit.ScalaCheckSuite {
    // generate ed25519 keys
    val RANDOM = new SecureRandom();
    val keyPairGenerator = new Ed25519KeyPairGenerator();
    keyPairGenerator.init(new Ed25519KeyGenerationParameters(RANDOM));
    val asymmetricCipherKeyPair = keyPairGenerator.generateKeyPair();
    val privateKey =
        asymmetricCipherKeyPair.getPrivate().asInstanceOf[Ed25519PrivateKeyParameters];
    val publicKey =
        asymmetricCipherKeyPair.getPublic().asInstanceOf[Ed25519PublicKeyParameters];

    val preimage = ByteString.fromString("preimage")
    val preimageHash = ByteString.unsafeFromArray(Utils.sha2_256(preimage.bytes))
    val encryptedChunk = ByteString.fromArray(Utils.sha2_256("encryptedChunk".getBytes))
    val chunkHash = ByteString.fromArray(Utils.sha2_256("chunkHash".getBytes))
    val encId = MerkleTree.fromHashes(ArraySeq(encryptedChunk, chunkHash)).getMerkleRoot
    val bondConfig = BondConfig(
      preimageHash,
      encId,
      ByteString.fromArray(publicKey.getEncoded()),
      ByteString.fromArray(blake2b224Hash(publicKey.getEncoded()))
    )

    test(s"bondProgram size is ${Bond.bondProgram.doubleCborEncoded.size}".ignore) {
        assert(Bond.bondProgram.doubleCborEncoded.size == 938)
    }

    test("Server can withdraw with valid preimage and signature") {
        val withdraw = BondAction.Withdraw(ByteString.fromString("preimage"))
        evalBondValidator(
          bondConfig,
          withdraw,
          scalus.prelude.List(PubKeyHash(bondConfig.serverPkh))
        ) {
            case UplcEvalResult.Success(term, budget, logs) =>
                println(budget)
                println(logs)
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
        val withdraw =
            BondAction.Withdraw(Builtins.appendByteString(preimage, ByteString.fromString("wrong")))
        evalBondValidator(
          bondConfig,
          withdraw,
          scalus.prelude.List(PubKeyHash(bondConfig.serverPkh))
        ) {
            case UplcEvalResult.Success(term, _, _)           => fail(s"should fail")
            case UplcEvalResult.UplcFailure(errorCode, error) =>
        }
    }

    test("Client can spend with valid fraud proof") {
        val claim = Builtins.appendByteString(bondConfig.encId, bondConfig.preimageHash)
        val signer = new Ed25519Signer();
        signer.init(true, privateKey);
        signer.update(claim.bytes, 0, claim.bytes.length);
        val signature = ByteString.fromArray(signer.generateSignature())
        val action =
            BondAction.FraudProof(
              signature = signature,
              preimage = preimage,
              encryptedChunk = encryptedChunk,
              chunkHash = chunkHash,
              chunkIndex = 0,
              merkleProof = scalus.prelude.List.empty
            )
        evalBondValidator(bondConfig, action, scalus.prelude.List.empty) {
            case UplcEvalResult.Success(term, budget, _) =>
                println(budget)
                assert(budget.cpu < 10_000_000000L)
                assert(budget.memory < 14_000000L)
            case UplcEvalResult.UplcFailure(errorCode, error) =>
                fail(s"errorCode: $errorCode, error: $error")
        }
    }

    def evalBondValidator(
        bondConfig: BondConfig,
        withdraw: BondAction,
        signatures: scalus.prelude.List[PubKeyHash]
    )(pf: PartialFunction[UplcEvalResult, Any]) = {
        val scriptContext = makeScriptContext(signatures)
        val term =
            Bond.bondValidator $ bondConfig.toData $ withdraw.toData $ makeScriptContext(
              signatures
            ).toData
        val result = PlutusUplcEval.evalFlat(Program((2, 0, 0), term))
        result match
            case UplcEvalResult.TermParsingError(error) => fail(s"TermParsingError: $error")
            case other                                  => pf(other)
    }

    test("xorBytes performance".ignore) {
        val term = Bond.xorBytesScript $ BigInt(1) $ BigInt(2)
        val result = PlutusUplcEval.evalFlat(Program((2, 0, 0), term))
        result match
          case UplcEvalResult.Success(term, budget, logs) => println(s"$term => $budget, $logs")
          case UplcEvalResult.TermParsingError(error) => fail(s"TermParsingError: $error")
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

    property("verifyPreimage is correct".ignore) {
        val verifyPreimage =
            scalus.Compiler.compile(BondContract.verifyPreimage).toUplc(generateErrorTraces = true)
        forAll { (bytes: Array[Byte]) =>
            val preimage = ByteString.unsafeFromArray(bytes)
            val hash = ByteString.unsafeFromArray(Utils.sha2_256(bytes))
            val wrongHash = ByteString.unsafeFromArray(Utils.sha2_256(bytes ++ Array(0.toByte)))
            val result =
                PlutusUplcEval.evalFlat(Program((2, 0, 0), verifyPreimage $ preimage $ hash))
            val wrongResult =
                PlutusUplcEval.evalFlat(Program((2, 0, 0), verifyPreimage $ preimage $ wrongHash))
            result match
                case UplcEvalResult.Success(term, _, _) =>
                case UplcEvalResult.UplcFailure(errorCode, error) =>
                    fail(s"UplcFailure: $errorCode, $error")
                case UplcEvalResult.TermParsingError(error) => fail(s"TermParsingError: $error")

            wrongResult match
                case UplcEvalResult.Success(term, _, _) => fail(s"wrongResult should fail")
                case UplcEvalResult.UplcFailure(errorCode, error) =>
                case UplcEvalResult.TermParsingError(error) => fail(s"TermParsingError: $error")
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

    def makeScriptContext(signatories: scalus.prelude.List[PubKeyHash]) =
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

    def blake2b224Hash(data: Array[Byte]): Array[Byte] = {
        val digest = new Blake2bDigest(224) // 224 bits
        digest.update(data, 0, data.length)
        val hash = new Array[Byte](digest.getDigestSize)
        digest.doFinal(hash, 0)
        hash
    }
}

case class Budget(cpu: Double, memory: Double)

enum UplcEvalResult:
    case Success(term: Term, budget: Budget, logs: String = "")
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
        val retCode = cmd.#<(new ByteArrayInputStream(flat)).!(ProcessLogger(o => out += o))
        if retCode == 0 then
            UplcParser.term.parse(out) match
                case Right(remaining, term) =>
                    val budget = raw"CPU budget:\s+(\d+)Memory budget:\s+(\d+)(.+)".r
                    println(remaining)
                    remaining match
                        case budget(cpu, memory, logs) =>
                            UplcEvalResult.Success(
                              term,
                              Budget(cpu.toDouble / 1000000, memory.toDouble / 1000000),
                              logs
                            )
                        case _ => UplcEvalResult.Success(term, Budget(0, 0), remaining)
                case Left(err) => UplcEvalResult.TermParsingError(err.show)
        else UplcEvalResult.UplcFailure(retCode, out)