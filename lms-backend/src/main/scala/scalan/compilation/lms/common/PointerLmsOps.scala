package scalan.compilation.lms.common

import scala.lms.common._
import scalan.compilation.lms.cxx.sharedptr.CxxShptrCodegen

trait PointerLmsOps extends Base {
  trait Scalar[A]
  trait Pointer[A]
}

trait PointerLmsOpsExp
  extends PointerLmsOps
  with LoopsFatExp
  with IfThenElseExp
  with EqualExpBridge
  with FunctionsExp
  with BaseExp {

  // note: m: Manifest[A] need to distinct objects CreateScalar[Int](0) and CreateScalar[Double](0.0), when 0 == 0.0
  case class CreateScalar[A](source: Exp[A], m: Manifest[A]) extends Def[Scalar[A]]
  def create_scalar[A: Manifest](source: Exp[A]): Exp[Scalar[A]] = CreateScalar(source, manifest[A])

  // note: m: Manifest[A] need to distinct objects NullPtr[Int] and NullPtr[Double] to be correct type for result pointer
  case class NullPtr[A](m: Manifest[A]) extends Def[Pointer[A]]
  def null_ptr[A: Manifest]: Exp[Pointer[A]] = NullPtr(manifest[A])

  case class ScalarPtr[A: Manifest](xScalar: Exp[Scalar[A]]) extends Def[Pointer[A]]
  def scalar_ptr[A: Manifest](xScalar: Exp[Scalar[A]]): Exp[Pointer[A]] = ScalarPtr(xScalar)

  case class ArrayPtr[A: Manifest](xs: Rep[Array[A]]) extends Def[Pointer[A]]
  def array_ptr[A: Manifest](xs: Exp[Array[A]]): Exp[Pointer[A]] = ArrayPtr(xs)
}

trait CxxShptrGenPointer extends CxxShptrCodegen {
  val IR: PointerLmsOpsExp
  import IR._

  override def remap[A](m: Manifest[A]): String = {
    m.runtimeClass match {
      case c if c == classOf[Scalar[_]] => remap(m.typeArguments(0))
      case c if c == classOf[Pointer[_]] => s"${remap(m.typeArguments(0))}*"
      case _ =>
        super.remap(m)
    }
  }

  override def wrapSharedPtr: PartialFunction[Manifest[_],Manifest[_]] = {
    case m if m.runtimeClass == classOf[Scalar[_]] => m
    case m if m.runtimeClass == classOf[Pointer[_]] => m
    case m => super.wrapSharedPtr(m)
  }

  override def emitNode(sym: Sym[Any], rhs: Def[Any]) = rhs match {
    case CreateScalar(x, _) =>
      emitValDef(sym, quote(x))

    case NullPtr(_) =>
      emitValDef(sym, "nullptr")

    case ScalarPtr(xScalar) =>
      emitValDef(sym, src"std::addressof($xScalar)")

    case ArrayPtr(xs) =>
      emitValDef(sym, src"std::addressof((*$xs)[0])")

    case _ =>
      super.emitNode(sym, rhs)
  }
}
