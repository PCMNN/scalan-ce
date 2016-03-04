package scalan.compilation.lms.linalgebra

import scalan.compilation.lms.collections.CollectionsBridgeScala
import scalan.compilation.lms.{CoreBridge, CoreLmsBackend}
import scalan.linalgebra.{VectorsDslExp, LinAlgMethodMappingDSL}

trait LinAlgBridge extends CoreBridge with LinAlgMethodMappingDSL {
  override val scalan: VectorsDslExp
  import scalan._

  val lms: CoreLmsBackend with VectorOpsExp

  override protected def lmsMethodName(d: Def[_], primitiveName: String): String = {
    d match {
      case _: DotSparse[_] => "array_dotProductSparse"
      case _: ArrayInnerJoin[_, _, _, _] =>
        println("*******************************")
        println("*******************************")
        println("*******************************")
        println("\tlmsMethodName: " + d)
        println("*******************************")
        println("*******************************")
        println("\tGotIt!")
        println("*******************************")
        println("*******************************")
        println("*******************************")
        "innerJoin"
      case _: ArrayOuterJoin[_, _, _, _] => "outerJoin"
      case _ => super.lmsMethodName(d, primitiveName)
    }
  }

  override protected def transformDef[T](m: LmsMirror, g: AstGraph, sym: Exp[T], d: Def[T]) = {
    d match {
      case u: ArrayInnerJoin[k, b, c, r] =>
        println("===============================")
        println("===============================")
        println("===============================")
        println("\ttransformDef: " + ((d, u)))
        println("===============================")
        println("===============================")
        println("===============================")
        val xs = u.xs.asInstanceOf[lms.Rep[Array[(k, b)]]]
        println("xs: " + xs)
        val ys = u.ys.asInstanceOf[lms.Rep[Array[(k, c)]]]
        println("ys: " + ys)
        val f = u.f.asInstanceOf[lms.Rep[((b, c)) => r]]
        println("f: " + f)
        val oK = u.ordK
        val nK = u.nK
        val mK = elemToManifest(u.eK).asInstanceOf[Manifest[k]]
        val mB = elemToManifest(u.eB).asInstanceOf[Manifest[b]]
        val mC = elemToManifest(u.eC).asInstanceOf[Manifest[c]]
        val mR = elemToManifest(u.eR).asInstanceOf[Manifest[r]]
        val exp = lms.innerJoin[k, b, c, r](xs, ys, f)(u.ordK, u.nK, mK, mB, mC, mR)
        println("exp: " + exp)
        m.addSym(sym, exp)
      case _ => super.transformDef(m, g, sym, d)
    }
  }
}

trait LinAlgBridgeScala extends CollectionsBridgeScala with LinAlgBridge
