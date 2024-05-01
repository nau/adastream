package adastream

import adastream.Encryption.chunksFromInputStream
import scalus.builtin.Builtins.sha2_256
import scalus.builtin.{ByteString, given}
import sttp.tapir.*
import sttp.tapir.server.netty.sync.{Id, NettySyncServer}
import sttp.tapir.swagger.bundle.SwaggerInterpreter
import sttp.tapir.files.*

import java.nio.file.{Files, Path, StandardOpenOption}
import scala.util.Using
import com.bloxbean.cardano.client.crypto.cip1852.CIP1852
import com.bloxbean.cardano.client.crypto.cip1852.DerivationPath
import com.bloxbean.cardano.client.crypto.bip32.HdKeyPair
import com.bloxbean.cardano.client.crypto.config.CryptoConfiguration
import java.io.InputStream
import java.io.File
import scala.util.Failure
import scala.util.Success
import scala.util.Try

class Server(
    val hdKeyPair: HdKeyPair,
    secret: ByteString,
    val filesDirectory: Path = Files.createTempDirectory("adastream")
):
    val preimage = secret
    val preimageHash = sha2_256(preimage)
    val signingProvider = CryptoConfiguration.INSTANCE.getSigningProvider

    val upload =
        endpoint.put
            .in("upload")
            .in(inputStreamBody)
            .out(stringJsonBody)
            .serverLogicSuccess[Id](uploadFile)

    val download =
        endpoint.get
            .in("download" / path[String]("fileId"))
            .out(fileBody)
            .errorOut(stringBody.map[Throwable](sys.error)(_.getMessage))
            .serverLogic[Id](downloadFile)

    val stream =
        endpoint.get
            .in("stream" / path[String]("fileId"))
            .in(query[String]("secret"))
            .out(inputStreamBody)
            .serverLogicSuccess[Id](streamFile)

    val apiEndpoints = List(upload, download, stream)
    val swaggerEndpoints =
        SwaggerInterpreter().fromEndpoints[Id](apiEndpoints.map(_.endpoint), "AdaStream", "0.1")

    def uploadFile(stream: InputStream): String =
        // write stream to file
        val path = Files.createTempFile("adastream-", ".tmp")
        println(s"uploading to $path")
        path.toFile.deleteOnExit()
        val fos = Files.newOutputStream(path, StandardOpenOption.CREATE)
        val fileIdBuilder = MerkleTreeRootBuilder()
        val encIdBuilder = MerkleTreeRootBuilder()
        Using(Files.newOutputStream(path, StandardOpenOption.CREATE)): fos =>
            for (chunk, index) <- Encryption.chunksFromInputStream(stream).zipWithIndex do
                val chunkByteString = ByteString.fromArray(chunk)
                val chunkHash = sha2_256(chunkByteString)
                val encrypted = ByteString.fromArray(
                  Encryption.encryptChunk(chunk, preimage.bytes, index)
                )
                val encHash = sha2_256(encrypted ++ chunkHash)
                fileIdBuilder.addHash(chunkHash)
                encIdBuilder.addHash(encHash)
                fos.write(encrypted.bytes)
                fos.write(chunkHash.bytes)

        val fileIdHex = fileIdBuilder.getMerkleRoot.toHex
        val encId = encIdBuilder.getMerkleRoot
        val encIdHex = encId.toHex
        val target = filesDirectory.resolve(fileIdHex)
        println(s"moving to $target")
        if Files.exists(target)
        then Files.delete(path)
        else Files.move(path, target)
        val claim = encId ++ preimageHash
        val signature =
            signingProvider.signExtended(claim.bytes, hdKeyPair.getPrivateKey.getKeyData)
        val json = ujson
            .Obj(
              "fileId" -> fileIdHex,
              "encId" -> encIdHex,
              "signature" -> signature.toHex,
              "preimageHash" -> preimageHash.toHex
            )
            .toString
        println(json)
        json

    def downloadFile(fileId: String): Id[Either[Throwable, File]] =
        Try {
            val path = filesDirectory.resolve(fileId)
            path.toFile
        }.toEither

    def streamFile(input: (String, String)): Id[InputStream] =
        val (fileId, secret) = input
        val path = filesDirectory.resolve(fileId)
        val is = Files.newInputStream(path)
        val decryptedChunks =
            val chunks = chunksFromInputStream(is)
            for (it, index) <- chunks.iterator.grouped(2).zipWithIndex
            yield
                val (encryptedChunk, hash) = (it(0), it(1))
                val decrypted = Encryption.decryptChunk(encryptedChunk, preimage.bytes, index)
                val chunkHash = sha2_256(ByteString.fromArray(decrypted))
                if chunkHash.bytes.sameElements(hash)
                then decrypted
                else throw new RuntimeException("Chunk hash mismatch")

        new InputStream {
            var current: Array[Byte] = null
            var index = 0
            val iterator: Iterator[Array[Byte]] = decryptedChunks

            override def read(): Int =
                current match
                    case null =>
                        if iterator.hasNext
                        then
                            current = iterator.next()
                            read()
                        else -1
                    case arr =>
                        if index < arr.length
                        then
                            val byte = arr(index)
                            index += 1
                            byte
                        else
                            current = null
                            index = 0
                            read()
        }

    def start(): Unit =
        NettySyncServer()
            .port(8080)
            .addEndpoints(apiEndpoints ++ swaggerEndpoints)
            .startAndWait()
