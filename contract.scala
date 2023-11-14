//> using scala 3.3.0
//> using plugin org.scalus:scalus-plugin_3:0.3.0
//> using dep org.scalus:scalus_3:0.3.0

package adastream

import io.bullet.borer.Cbor
import scalus.*
import scalus.Compile
import scalus.Compiler.compile
import scalus.Compiler.fieldAsData
import scalus.builtins.Builtins
import scalus.builtins.ByteString
import scalus.ledger.api.v1.FromDataInstances.given
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
import scalus.uplc.FromDataInstances.given
import scalus.uplc.Term
import scalus.utils.Utils
import scalus.ledger.api.v1.POSIXTime
import scalus.ledger.api.v1.Extended

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

  /*
   * HTLC contract validator
   */
  def makeHtlcContractValidator(clientPubKeyHash: Data, expiration: POSIXTime, hash: ByteString) =
    (datum: Data, redeemer: Data, ctxData: Data) => {
      val validPreimage = Builtins.equalsByteString(hash, Builtins.sha2_256(Builtins.unsafeDataAsB(redeemer)))
      val expired = {
        val txInfoData = fieldAsData[ScriptContext](_.txInfo)(ctxData)
        val signatoriesData = fieldAsData[TxInfo](_.signatories)(txInfoData)
        val txtime = fromData[POSIXTimeRange]( fieldAsData[TxInfo](_.validRange)(txInfoData) )
        txtime.from.extended match
          case Extended.Finite(txtime) =>
            val expired = expiration < txtime
            val signedByClient = {
              val signaturePubKeyHashData = Builtins.unsafeDataAsList(signatoriesData).head
              Builtins.equalsData(signaturePubKeyHashData, clientPubKeyHash)
            }
            expired && signedByClient
          case _ => false
      }
      if validPreimage || expired then () else throw new Exception()
  }
}

@main def main() = {
  val compiledBondScript = compile(BondContract.bondContractValidator)
  val bondValidator = compiledBondScript.toUplc(generateErrorTraces = true)
  val bondProgram = Program((2, 0, 0), bondValidator)
  val compiledHtlcScript = compile(BondContract.makeHtlcContractValidator)
  val htlcValidator = compiledHtlcScript.toUplc(generateErrorTraces = true)
  val htlcProgram = Program((2, 0, 0), htlcValidator)
  println(compiledBondScript.pretty.render(100))
  println(bondProgram.doubleCborHex)
  println(compiledHtlcScript.pretty.render(100))
  println(htlcProgram.doubleCborHex)
  println(s"bondProgram size: ${bondProgram.doubleCborEncoded.size}")
  println(s"htlcProgram size: ${htlcProgram.doubleCborEncoded.size}")
}
