//> using scala 3.3.0
//> using test.dep org.scalameta::munit::1.0.0-M10
//> using test.dep org.scalameta::munit-scalacheck::1.0.0-M10
//> using test.dep org.scalacheck::scalacheck::1.17.0
//> using dep org.scalus:scalus_3:0.3.0

package adastream

import org.scalacheck.Prop.*
import scalus.builtins.ByteString
import org.scalacheck.Gen
import org.scalacheck.Arbitrary
import scalus.builtins.Builtins
import scalus.toUplc
import scalus.uplc.Data.toData
import scalus.utils.Utils
import scalus.uplc.PlutusUplcEval
import scalus.uplc.Program
import scalus.uplc.TermDSL.{*, given}
import scalus.uplc.UplcEvalResult
import scalus.uplc.ToDataInstances.given
import scalus.ledger.api.v2.ToDataInstances.given
import adastream.BondContract.BondConfig
import adastream.BondContract.BondAction
import scalus.ledger.api.v1.PubKeyHash
import scalus.ledger.api.v2.*
import scalus.builtins.ByteString.StringInterpolators
import scalus.ledger.api.v1.PubKeyHash

class ContractTests extends munit.ScalaCheckSuite {
    test(s"bondProgram size is ${Bond.bondProgram.doubleCborEncoded.size}") {
        assert(Bond.bondProgram.doubleCborEncoded.size == 938)
    }

    val preimage = ByteString.fromString("preimage")
    val hash = ByteString.unsafeFromArray(Utils.sha2_256(preimage.bytes))
    val bondConfig = BondConfig(
      hash,
      ByteString.empty,
      ByteString.empty,
      ByteString.fromString("Server PubKeyHash")
    )

    test("Server can withdraw with valid preimage and signature") {
        val withdraw = BondAction.Withdraw(ByteString.fromString("preimage"))
        evalBondValidator(
          bondConfig,
          withdraw,
          scalus.prelude.List(PubKeyHash(bondConfig.serverPkh))
        ) {
            case UplcEvalResult.Success(term) =>
            case UplcEvalResult.UplcFailure(errorCode, error) =>
                fail(s"UplcFailure: $errorCode, $error")
        }
    }

    test("Server can't withdraw without a signature") {
        val withdraw = BondAction.Withdraw(preimage)
        evalBondValidator(bondConfig, withdraw, scalus.prelude.List.empty) {
            case UplcEvalResult.Success(term)                 => fail(s"should fail")
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
            case UplcEvalResult.Success(term)                 => fail(s"should fail")
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
            case UplcEvalResult.Success(term)                 => fail(s"should fail")
            case UplcEvalResult.UplcFailure(errorCode, error) =>
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

    property("verifyPreimage is correct") {
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
                case UplcEvalResult.Success(term) =>
                case UplcEvalResult.UplcFailure(errorCode, error) =>
                    fail(s"UplcFailure: $errorCode, $error")
                case UplcEvalResult.TermParsingError(error) => fail(s"TermParsingError: $error")

            wrongResult match
                case UplcEvalResult.Success(term) => fail(s"wrongResult should fail")
                case UplcEvalResult.UplcFailure(errorCode, error) =>
                case UplcEvalResult.TermParsingError(error) => fail(s"TermParsingError: $error")
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
}
