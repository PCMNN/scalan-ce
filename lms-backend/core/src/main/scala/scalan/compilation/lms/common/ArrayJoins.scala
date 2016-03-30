package scalan.compilation.lms.common

import scala.lms.common._
import scalan.compilation.lms.LmsBackendFacade

trait ArrayJoins extends Base {

  def inner_join[A, B, K, R](xs: Rep[Array[A]], ys: Rep[Array[B]], a: Rep[A => K], b: Rep[B => K], f: Rep[((A, B)) => R])
                                  (implicit ordK: Ordering[K], nK: Numeric[K], selfType: Manifest[Array[(K, R)]],
                                   eA: Manifest[A], eB: Manifest[B], eK: Manifest[K], eR: Manifest[R]): Rep[Array[(K, R)]]

  def outer_join[A, B, K, R](xs: Rep[Array[A]], ys: Rep[Array[B]], a: Rep[A => K], b: Rep[B => K],
                                   f: Rep[((A, B)) => R], f1: Rep[A => R], f2: Rep[B => R])
                                  (implicit ordK: Ordering[K], nK: Numeric[K], selfType: Manifest[Array[(K, R)]],
                                   eA: Manifest[A], eB: Manifest[B], eK: Manifest[K], eR: Manifest[R]): Rep[Array[(K, R)]]
}

trait ArrayJoinsExp extends ArrayJoins with ArrayBuilderOpsExp { self: LmsBackendFacade =>

  def inner_join[A, B, K, R](xs: Exp[Array[A]], ys: Exp[Array[B]], a: Rep[A => K], b: Rep[B => K], f: Rep[((A, B)) => R])
                                  (implicit ordK: Ordering[K], nK: Numeric[K], selfType: Manifest[Array[(K, R)]],
                                   eA: Manifest[A], eB: Manifest[B], eK: Manifest[K], eR: Manifest[R]): Rep[Array[(K, R)]] = {
    val res = ArrayBuilder.make[(K, R)]
    var i1 = 0
    var i2 = 0
    val n1 = xs.length
    val n2 = ys.length
    while (readVar(i1) < n1 && readVar(i2) < n2) {
      val x = xs.at(readVar(i1))
      val y = ys.at(readVar(i2))
      val i = a(x)
      val j = b(y)
      if (i == j) {
        res += (i, f((x, y)))
        i1 = readVar(i1) + 1
        i2 = readVar(i2) + 1
      } else if (i < j) i1 = readVar(i1) + 1 else i2 = readVar(i2) + 1
    }
    res.result
  }

  def outer_join[A, B, K, R](xs: Exp[Array[A]], ys: Exp[Array[B]], a: Rep[A => K], b: Rep[B => K],
                                   f: Rep[((A, B)) => R], f1: Rep[A => R], f2: Rep[B => R])
                                  (implicit ordK: Ordering[K], nK: Numeric[K], selfType: Manifest[Array[(K, R)]],
                                   eA: Manifest[A], eB: Manifest[B], eK: Manifest[K], eR: Manifest[R]): Rep[Array[(K, R)]] = {
    val res = ArrayBuilder.make[(K, R)]
    var i1 = 0
    var i2 = 0
    val n1 = xs.length
    val n2 = ys.length
    while (readVar(i1) < n1 || readVar(i2) < n2) {
      val i = readVar(i1)
      val j = readVar(i2)
      if (i == n1) {
        val y = ys.at(j)
        res += (b(y), f2(y))
        i2 = j + 1
      } else if (j == n2) {
        val x = xs.at(i)
        res += (a(x), f1(x))
        i1 = i + 1
      } else {
        val x = xs.at(i)
        val y = ys.at(j)
        val iX = a(x)
        val jY = b(y)
        if (iX == jY) {
          res += (iX, f((x, y)))
          i1 = i + 1
          i2 = j + 1
        } else if (iX < jY) {
          res += (a(x), f1(x))
          i1 = i + 1
        } else {
          res += (b(y), f2(y))
          i2 = j + 1
        }
      }
    }
    res.result
  }
}
