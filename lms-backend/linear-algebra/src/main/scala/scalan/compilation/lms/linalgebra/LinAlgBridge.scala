package scalan.compilation.lms.linalgebra

import scalan.compilation.lms.collections.CollectionsBridgeScala
import scalan.compilation.lms.{CoreBridge, CoreLmsBackend}
import scalan.linalgebra.LADslExp

trait LinAlgBridge extends CoreBridge {
  override val scalan: LADslExp
  import scalan._

  val lms: CoreLmsBackend with VectorOpsExp

  override protected def lmsMethodName(d: Def[_], primitiveName: String): String = d match {
    case _: DotSparse[_] => "array_dotProductSparse"
    case _ => super.lmsMethodName(d, primitiveName)
  }
}

trait LinAlgBridgeScala extends CollectionsBridgeScala with LinAlgBridge
