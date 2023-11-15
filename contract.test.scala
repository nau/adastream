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
import scalus.utils.Utils
import scalus.uplc.PlutusUplcEval
import scalus.uplc.Program
import scalus.uplc.UplcEvalResult

class ContractTests extends munit.ScalaCheckSuite {
    test(s"bondProgram size is ${Bond.bondProgram.doubleCborEncoded.size}") {
        assert(Bond.bondProgram.doubleCborEncoded.size == 938)
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
        import scalus.toUplc
        import scalus.uplc.TermDSL.{*, given}
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
}
