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

class Server(
    val hdKeyPair: HdKeyPair,
    secret: ByteString,
    val filesDirectory: Path = Files.createTempDirectory("adastream")
):
    val preimage = secret
    val preimageHash = sha2_256(preimage)
    val signingProvider = CryptoConfiguration.INSTANCE.getSigningProvider
    val getKeys =
        endpoint.get
            .in("keys")
            .out(stringJsonBody)
            .serverLogicSuccess[Id](name =>
                ujson
                    .Obj("publicKey" -> publicKey.toHex, "privateKey" -> privateKey.toHex)
                    .toString
            )
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
            .serverLogicSuccess[Id](downloadFile)
    val apiEndpoints = List(getKeys, upload, download)
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

    def downloadFile(fileId: String): Id[File] =
        val path = filesDirectory.resolve(fileId)
        path.toFile

    def start(): Unit =
        NettySyncServer()
            .port(8080)
            .addEndpoints(apiEndpoints ++ swaggerEndpoints)
            .startAndWait()
