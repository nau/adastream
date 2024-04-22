package adastream

import sttp.tapir.swagger.bundle.SwaggerInterpreter
import java.nio.file.Files
import java.nio.file.Path

object Server:
    import sttp.tapir.*
    import sttp.tapir.server.netty.sync.{Id, NettySyncServer}
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
            .serverLogicSuccess[Id]: stream =>
                // write stream to file
                Files.copy(stream, Path.of("uploaded"))
                ujson.Str("uploaded").toString

    val download =
        endpoint.get
            .in("download")
            .out(stringJsonBody)
            .serverLogicSuccess[Id](name => ujson.Str("downloaded").toString)
    val apiEndpoints = List(getKeys, upload, download)
    val swaggerEndpoints =
        SwaggerInterpreter().fromEndpoints[Id](apiEndpoints.map(_.endpoint), "AdaStream", "0.1")

    def start(): Unit =
        NettySyncServer().port(8080).addEndpoints(apiEndpoints ++ swaggerEndpoints).startAndWait()
