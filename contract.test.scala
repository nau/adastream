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

class ContractTests extends munit.ScalaCheckSuite {
    test("foo") {
        println(s"bondProgram size: ${Bond.bondProgram.doubleCborEncoded.size}")
        assert(2 + 2 == 4)
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
}
