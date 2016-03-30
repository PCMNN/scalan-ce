package scalan.arrays

import scalan.staged.BaseExp
import scalan.ScalanExp

trait Joins extends BaseExp { self: ScalanExp =>

  case class InnerJoin[A, B, K, R](xs: Exp[Array[A]], ys: Exp[Array[B]], a: Rep[A => K], b: Rep[B => K], f: Rep[((A, B)) => R])
                                  (implicit val ordK: Ordering[K], val nK: Numeric[K], val st: Elem[Array[(K, R)]],
                                   val eA: Elem[A], val eB: Elem[B], val eK: Elem[K], val eR: Elem[R]) extends ArrayDef[(K, R)]

  case class OuterJoin[A, B, K, R](xs: Exp[Array[A]], ys: Exp[Array[B]], a: Rep[A => K], b: Rep[B => K], f: Rep[((A, B)) => R], f1: Rep[A => R], f2: Rep[B => R])
                                  (implicit val ordK: Ordering[K], val nK: Numeric[K], val st: Elem[Array[(K, R)]],
                                   val eA: Elem[A], val eB: Elem[B], val eK: Elem[K], val eR: Elem[R]) extends ArrayDef[(K, R)]
}
