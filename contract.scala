//> using scala 3.3.0
//> using plugin org.scalus:scalus-plugin_3:0.3.0
//> using dep org.scalus:scalus_3:0.3.0

package adastream

import io.bullet.borer.Cbor
import scalus.*
import scalus.Compile
import scalus.Compiler.compile
import scalus.builtins.Builtins
import scalus.builtins.ByteString
import scalus.ledger.api.v2.FromDataInstances.given
import scalus.ledger.api.v2.ScriptPurpose.*
import scalus.ledger.api.v2.*
import scalus.prelude.AssocMap
import scalus.prelude.List
import scalus.prelude.Maybe.*
import scalus.prelude.Prelude.===
import scalus.prelude.Prelude.given
import scalus.pretty
import scalus.sir.SIR
import scalus.sir.SimpleSirToUplcLowering
import scalus.uplc.Cek
import scalus.uplc.Data
import scalus.uplc.Data.fromData
import scalus.uplc.Program
import scalus.uplc.ProgramFlatCodec
import scalus.uplc.Term
import scalus.utils.Utils

@Compile
object BondContract {
  import List.*

  def bondContractValidator(
      txId: ByteString, // TxId and output index we must spend to mint tokens
      txOutIdx: BigInt,
      tokensToMint: AssocMap[ByteString, BigInt]
  ) = (datum: Unit, redeemer: Unit, ctxData: Data) => {
    throw new Exception("TODO")
  }
}

@main def main() = {
  val compiledScript = compile(BondContract.bondContractValidator)
  val validator = compiledScript.toUplc(generateErrorTraces = true)
  val program = Program((2, 0, 0), validator)
  println(compiledScript.pretty.render(100))
  println(program.doubleCborHex)
}


