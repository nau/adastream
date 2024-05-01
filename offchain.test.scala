package adastream

import org.scalacheck.Prop.*
import org.scalacheck.{Arbitrary, Shrink}
import scalus.builtin.Builtins.*
import scalus.builtin.{ByteString, PlatformSpecific, given}

class MerkleTreeTests extends munit.ScalaCheckSuite {
    property(s"test") {
        forAll: (chunks: List[String]) =>
            val hashes = chunks.map(ByteString.fromString).map(sha2_256)
            val root = MerkleTree.fromHashes(hashes).getMerkleRoot
            val builder = MerkleTreeRootBuilder()
            for hash <- hashes do builder.addHash(hash)
            builder.getMerkleRoot == root
    }
}
