package scalan.compilation.lms.common

import scala.lms.common._
import scala.lms.internal.Transforming
import scala.reflect.SourceContext
import scalan.compilation.lms.LmsBackendFacade
import scalan.compilation.lms.cxx.sharedptr.CxxShptrCodegen

trait ArrayJoins extends Variables {

  def innerJoin[K, B, C, R](xs: Rep[Array[(K, B)]], ys: Rep[Array[(K, C)]], f: Rep[((B, C)) => R])
                                    (implicit ordK: Ordering[K], nK: Numeric[K], mK: Manifest[K],
                                     mB: Manifest[B], mC: Manifest[C], mR: Manifest[R]): Rep[Array[(K, R)]]

  def outerJoin[K, B, C, R](xs: Rep[Array[(K, B)]], ys: Rep[Array[(K, C)]], f: Rep[((B, C)) => R],
                                     f1: Rep[B => R], f2: Rep[C => R])
                                    (implicit ordK: Ordering[K], nK: Numeric[K], mK: Manifest[K],
                                     mB: Manifest[B], mC: Manifest[C], mR: Manifest[R]): Rep[Array[(K, R)]]
}

trait ArrayJoinsExp extends ArrayJoins with EffectExp with VariablesExp with Transforming { self: LmsBackendFacade =>

  case class ArrayInnerJoin[K, B, C, R](xs: Exp[Array[(K, B)]], ys: Exp[Array[(K, C)]], f: Exp[((B, C)) => R])
                                       (implicit val ordK: Ordering[K], val nK: Numeric[K], val mK: Manifest[K],
                                        val mB: Manifest[B], val mC: Manifest[C], val mR: Manifest[R])
    extends Def[Array[(K, R)]]
  case class ArrayOuterJoin[K, B, C, R](xs: Exp[Array[(K, B)]], ys: Exp[Array[(K, C)]], f: Exp[((B, C)) => R],
                                        f1: Exp[B => R], f2: Exp[C => R])(implicit val ordK: Ordering[K],
                                        val nK: Numeric[K], val mK: Manifest[K], val mB: Manifest[B],
                                        val mC: Manifest[C], val mR: Manifest[R])
    extends Def[Array[(K, R)]]

  def innerJoin[K, B, C, R](xs: Rep[Array[(K, B)]], ys: Rep[Array[(K, C)]], f: Rep[((B, C)) => R])
                                    (implicit ordK: Ordering[K], nK: Numeric[K], mK: Manifest[K],
                                     mB: Manifest[B], mC: Manifest[C], mR: Manifest[R]) = {
    ArrayInnerJoin(xs, ys, f)(ordK, nK, mK, mB, mC, mR)
  }

  def outerJoin[K, B, C, R](xs: Rep[Array[(K, B)]], ys: Rep[Array[(K, C)]], f: Rep[((B, C)) => R],
                                     f1: Rep[B => R], f2: Rep[C => R])
                                    (implicit ordK: Ordering[K], nK: Numeric[K], mK: Manifest[K],
                                     mB: Manifest[B], mC: Manifest[C], mR: Manifest[R]) = {
    ArrayOuterJoin(xs, ys, f, f1, f2)(ordK, nK, mK, mB, mC, mR)
  }

  override def mirror[A:Manifest](e: Def[A], f: Transformer)(implicit pos: SourceContext): Exp[A] = e match {
    case dp @ ArrayInnerJoin(xs, ys, g) =>
      innerJoin(f(xs), f(ys), f(g))(dp.ordK, dp.nK, mtype(dp.mK), mtype(dp.mB), mtype(dp.mC), mtype(dp.mR))
    case dp @ ArrayOuterJoin(xs, ys, g, g1, g2) =>
      outerJoin(f(xs), f(ys), f(g), f(g1), f(g2))(dp.ordK, dp.nK,
        mtype(dp.mK), mtype(dp.mB), mtype(dp.mC), mtype(dp.mR))
    case _ => super.mirror(e, f)
  }
}

trait ScalaGenArrayJoins extends ScalaGenBase {
  val IR: ArrayJoinsExp
  import IR._

  override def emitNode(sym: Sym[Any], rhs: Def[Any]) = rhs match {
    case ds @ ArrayInnerJoin(xs, ys, f) =>
      // existence of implicit Numeric[A] ensures we can have + and *
      stream.println(
        src"""
           |{
           |// generating inner join
           |    val xIter = $xs.arr.iterator
           |    val yIter = $ys.arr.iterator
           |
           |    val buffer = mutable.ArrayBuffer[(K, R)]()
           |
           |    @tailrec
           |    def go(keyX: K, keyY: K, valueX: B, valueY: C) {
           |      val cmp = ordK.compare(keyX, keyY)
           |      if (cmp == 0) {
           |        // keyX == keyY
           |        val value = $f((valueX, valueY))
           |        buffer.append((keyX, value))
           |        if (xIter.hasNext && yIter.hasNext) {
           |          val (keyX1, valueX1) = xIter.next()
           |          val (keyY1, valueY1) = yIter.next()
           |          go(keyX1, keyY1, valueX1, valueY1)
           |        }
           |      } else if (cmp < 0) {
           |        // keyX < keyY
           |        if (xIter.hasNext) {
           |          val (keyX1, valueX1) = xIter.next()
           |          go(keyX1, keyY, valueX1, valueY)
           |        }
           |      } else {
           |        // keyY < keyX
           |        if (yIter.hasNext) {
           |          val (keyY1, valueY1) = yIter.next()
           |          go(keyX, keyY1, valueX, valueY1)
           |        }
           |      }
           |    }
           |    if (xIter.hasNext && yIter.hasNext) {
           |      val (keyX1, valueX1) = xIter.next()
           |      val (keyY1, valueY1) = yIter.next()
           |      go(keyX1, keyY1, valueX1, valueY1)
           |    }
           |    buffer.toArray
           |}
           """.stripMargin)
    case _ => super.emitNode(sym, rhs)
  }

}

trait CxxShptrGenArrayJoins extends CxxShptrCodegen {
  val IR: ArrayJoinsExp
  import IR._

  override def emitNode(sym: Sym[Any], rhs: Def[Any]) = rhs match {
    case dp @ ArrayInnerJoin(xs, ys, g) =>
      stream.println("\t++++++++++++++++++++++++ArrayInnerJoin")
    case dp @ ArrayOuterJoin(xs, ys, g, g1, g2) =>
      stream.println("\t++++++++++++++++++++++++ArrayOuterJoin")
    /*case ds @ ArrayDotProdSparse(idxs1, vals1, idxs2, vals2) =>
      // += and * operators are assumed to be defined, since A is a numeric type
      stream.println("// generating dot product")
      emitConstruct(sym)
      stream.println(
        src""" {
           |  auto idxs1 = $idxs1;
           |  auto idxs2 = $idxs2;
           |  auto vals1 = $vals1;
           |  auto vals2 = $vals2;
           |  size_t i1 = 0;
           |  size_t i2 = 0;
           |  while (i1 < idxs1->size() && i2 < idxs2->size()) {
           |    auto ind1 = (*idxs1)[i1];
           |    auto ind2 = (*idxs2)[i2];
           |    if (ind1 == ind2) {
           |      $sym += (*vals1)[i1] * (*vals2)[i2];
           |      i1 += 1;
           |      i2 += 1;
           |    } else if (ind1 < ind2) {
           |      i1 += 1;
           |    } else {
           |      i2 += 1;
           |    }
           |  };
           |}
           """.stripMargin)*/
    case _ => super.emitNode(sym, rhs)
  }

}
