package scalan.compilation.lms.cxx

import scala.collection.mutable
import scala.virtualization.lms.common.{ArrayBuilderOpsExp, CLikeGenEffect, BaseGenArrayBuilderOps}

trait CXXGenArrayBuilderOps  extends CXXCodegen with BaseGenArrayBuilderOps with CLikeGenEffect {
  val IR: ArrayBuilderOpsExp
  import IR._

  override def remap[A](m: Manifest[A]): String = {
    m.runtimeClass match {
      case c if c == classOf[mutable.ArrayBuilder[_]] =>
        val mA = m.typeArguments(0)
        remap(Manifest.arrayType(mA))
      case _ =>
        super.remap(m)
    }
  }

  override def traverseStm(stm: Stm): Unit = {
    stm match {
      case TP(sym,rhs) =>
        rhs match {
          case ArrayBuilderMake() =>
              moveableSyms += sym
          case _ =>
            ()
        }
      case _ =>
        ()
    }
    super.traverseStm(stm)
  }


  override def emitNode(sym: Sym[Any], rhs: Def[Any]) = rhs match {
    case a@ArrayBuilderMake() =>
      emitVarDecl(sym)
    case ArrayBuilderAppend(l, e) =>
//      emitValDef(sym, src"$l += $e")
      stream.println(s"${quote(l)}.push_back(${quote(e)});")
    case ArrayBuilderClear(l) =>
//      emitValDef(sym, src"$l.clear()")
      stream.println(s"${quote(l)}.clear();")
    case ArrayBuilderResult(x) =>
      emitVarDef(sym, s"${quoteMove(x)}")
    case _ =>
      super.emitNode(sym, rhs)
  }
}
