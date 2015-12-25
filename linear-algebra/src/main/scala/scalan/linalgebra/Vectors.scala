package scalan.linalgebra

/**
 * Created by Victor Smirnov on 3/12/15.
 */

import scalan._
import scalan.collections.{CollectionsDsl, CollectionsDslSeq, CollectionsDslExp}
import scalan.common.OverloadHack.{Overloaded2, Overloaded1}
import scala.annotation.unchecked.uncheckedVariance

trait Vectors { self: LADsl =>

  type Vector[T] = Rep[AbstractVector[T]]

  trait AbstractVector[T] extends Def[AbstractVector[T]] {

    def length: IntRep
    def items: Coll[T]
    def nonZeroIndices: Coll[Int]
    def nonZeroValues:  Coll[T]
    def nonZeroItems: Coll[(Int, T)]
    implicit def eT: Elem[T]
    def zeroValue: Rep[T] = eT.defaultRepValue
    def constItem: Rep[T]

    def apply(i: IntRep): Rep[T]
    @OverloadId("apply_by_collection")
    def apply(is: Coll[Int])(implicit o: Overloaded1): Vector[T]

    //def mapBy[R: Elem](f: Rep[T => R @uncheckedVariance]): Vector[R]
    def filterBy(f: Rep[T @uncheckedVariance => Boolean]): Vector[T]

    def +^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T]
    @OverloadId("elementwise_sum_collection")
    def +^(coll: Coll[T])(implicit n: Numeric[T], o: Overloaded1): Vector[T] = self +^ DenseVector(coll)
    @OverloadId("elementwise_sum_value")
    def +^(value: Rep[T])(implicit n: Numeric[T], o: Overloaded2): Vector[T] = self +^ ConstVector(value, length)

    def -^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T]
    @OverloadId("elementwise_diff_collection")
    def -^(coll: Coll[T])(implicit n: Numeric[T], o: Overloaded1): Vector[T] = self -^ DenseVector(coll)
    @OverloadId("elementwise_diff_value")
    def -^(value: Rep[T])(implicit n: Numeric[T], o: Overloaded2): Vector[T] = self -^ ConstVector(value, length)

    def *^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T]
    @OverloadId("elementwise_mult_collection")
    def *^(coll: Coll[T])(implicit n: Numeric[T], o: Overloaded1): Vector[T] = self *^ DenseVector(coll)
    @OverloadId("elementwise_mult_value")
    def *^(value: Rep[T])(implicit n: Numeric[T], o: Overloaded2): Vector[T] = self *^ ConstVector(value, length)

    def /^(vector: Vector[T])(implicit f: Fractional[T]): Vector[T]
    @OverloadId("elementwise_div_collection")
    def /^(coll: Coll[T])(implicit f: Fractional[T], o: Overloaded1): Vector[T] = self /^ DenseVector(coll)
    @OverloadId("elementwise_div_value")
    def /^(value: Rep[T])(implicit f: Fractional[T], o: Overloaded2): Vector[T] = self /^ ConstVector(value, length)

    def *(matrix: Matrix[T])(implicit n: Numeric[T]): Vector[T]

    def pow_^(order: Rep[Double])(implicit n: Numeric[T], o: Overloaded2): Vector[T]

    def euclideanNorm(implicit num: Numeric[T]): DoubleRep

    def sum(implicit n: Numeric[T]): Rep[T]
    def reduce(implicit m: RepMonoid[T]): Rep[T]
    def dot(vector: Vector[T])(implicit n: Numeric[T]): Rep[T]

    def nonZeroesLength: IntRep = nonZeroItems.length
  }

  abstract class DenseVector[T](val items: Coll[T])(implicit val eT: Elem[T])
    extends AbstractVector[T] {

    def length = items.length
    def nonZeroIndices = nonZeroItems.as
    def nonZeroValues = items.filter(v => v !== zeroValue)
    def nonZeroItems = (Collection.indexRange(length) zip items).filter { case Pair(i, v) => v !== zeroValue }
    def constItem = zeroValue

    def apply(i: IntRep): Rep[T] = items(i)
    @OverloadId("apply_by_collection")
    def apply(is: Coll[Int])(implicit o: Overloaded1): Vector[T] = DenseVector(items(is))

    //def mapBy[R: Elem](f: Rep[T => R @uncheckedVariance]): Vector[R] = DenseVector(items.mapBy(f))
    def filterBy(f: Rep[T @uncheckedVariance => Boolean]): Vector[T] = {
      val filtered = (Collection.indexRange(length) zip items).filter(p => f(p._2))
      SparseVectorBoxed(filtered, length)
    }

    def +^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      def updates = (items(vector.nonZeroIndices) zip vector.nonZeroValues).map { case Pair(v1, v2) => v1 + v2 }
      def updatedFlatItems = items.updateMany(vector.nonZeroIndices, updates)
      def shiftedFlatItems = ((self +^ vector.constItem).items).updateMany(vector.nonZeroIndices, updates)
      vector match {
        case DenseVectorMatcher(_) => DenseVector((items zip vector.items).map { case Pair(v1, v2) => v1 + v2 })
        case ConstVectorMatcher(cv, _) => DenseVector(items.map(v => v + cv))
        case SparseVectorMatcher(_, _, _) => DenseVector(updatedFlatItems)
        case SparseVectorBoxedMatcher(_, _) => DenseVector(updatedFlatItems)
        case ShiftVectorMatcher(_, _, _, _) => DenseVector(shiftedFlatItems)
        case ShiftVectorBoxedMatcher(_, _, _) => DenseVector(shiftedFlatItems)
        case _ => !!!("matcher for @vector argument in DenseVector.+^(vector: Vector[T]) is not specified.")
      }
    }
    def -^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      def updates = (items(vector.nonZeroIndices) zip vector.nonZeroValues).map { case Pair(v1, v2) => v1 - v2 }
      def updatedFlatItems = items.updateMany(vector.nonZeroIndices, updates)
      def shiftedFlatItems = ((self +^ vector.constItem).items).updateMany(vector.nonZeroIndices, updates)
      vector match {
        case DenseVectorMatcher(_) => DenseVector((items zip vector.items).map { case Pair(v1, v2) => v1 - v2 })
        case ConstVectorMatcher(cv, _) => DenseVector(items.map(v => v - cv))
        case SparseVectorMatcher(_, _, _) => DenseVector(updatedFlatItems)
        case SparseVectorBoxedMatcher(_, _) => DenseVector(updatedFlatItems)
        case ShiftVectorMatcher(_, _, _, _) => DenseVector(shiftedFlatItems)
        case ShiftVectorBoxedMatcher(_, _, _) => DenseVector(shiftedFlatItems)
        case _ => !!!("matcher for @vector argument in DenseVector.-^(vector: Vector[T]) is not specified.")
      }
    }
    def *^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      lazy val (is, vs) = (vector.nonZeroIndices, vector.nonZeroValues)
      def newValues = (items(is) zip vs).map { case Pair(v1, v2) => v1 * v2 }
      def newItems = (vector.nonZeroItems zip items(is)).map { case Pair(Pair(i, v1), v2) => (i, v1 * v2) }
      def shiftedFlatItems = ((self *^ vector.constItem).items).updateMany(is, newValues)
      vector match {
        case DenseVectorMatcher(_) => DenseVector((items zip vector.items).map { case Pair(v1, v2) => v1 * v2 })
        case ConstVectorMatcher(cv, _) => DenseVector(items.map(v => v * cv))
        case SparseVectorMatcher(_, _, _) => SparseVector(is, newValues, length)
        case SparseVectorBoxedMatcher(_, _) => SparseVectorBoxed(newItems, length)
        case ShiftVectorMatcher(_, _, _, _) => DenseVector(shiftedFlatItems)
        case ShiftVectorBoxedMatcher(_, _, _) => DenseVector(shiftedFlatItems)
        case _ => !!!("matcher for @vector argument in DenseVector.*^(vector: Vector[T]) is not specified.")
      }
    }
    def /^(vector: Vector[T])(implicit f: Fractional[T]): Vector[T] = {
      lazy val (is, vs) = (vector.nonZeroIndices, vector.nonZeroValues)
      def updates = (items(is) zip vs).map { case Pair(v1, v2) => v1 / v2 }
      def updatedFlatItems = (items zip vector.items).map { case Pair(v1, v2) => v1 / v2 }
      def shiftedFlatItems = ((self /^ vector.constItem).items).updateMany(is, updates)
      vector match {
        case DenseVectorMatcher(_) => DenseVector(updatedFlatItems)
        case ConstVectorMatcher(value, _) => DenseVector(items.map(v => v / value))
        case SparseVectorMatcher(_, _, _) => DenseVector(updatedFlatItems)
        case SparseVectorBoxedMatcher(_, _) => DenseVector(updatedFlatItems)
        case ShiftVectorMatcher(_, _, _, _) => DenseVector(shiftedFlatItems)
        case ShiftVectorBoxedMatcher(_, _, _) => DenseVector(shiftedFlatItems)
        case _ => !!!("matcher for @vector argument in DenseVector.*^(vector: Vector[T]) is not specified.")
      }
    }
    def dot(vector: Vector[T])(implicit n: Numeric[T]): Rep[T] = {
      def const = ConstVector(vector.constItem, length)
      def sparse = SparseVector(vector.nonZeroIndices, vector.nonZeroValues.map(v => v - vector.constItem), length)
      def sparseBoxed = SparseVectorBoxed(vector.nonZeroItems.map(v => (v._1, v._2 - vector.constItem)), length)
      vector match {
        case ConstVectorMatcher(cv, _) => self.reduce * cv
        case SparseVectorMatcher(_, _, _) => (self *^ vector).nonZeroValues.reduce
        case SparseVectorBoxedMatcher(_, _) => (self *^ vector).nonZeroValues.reduce
        case ShiftVectorMatcher(_, _, _, _) => (self dot sparse) + (self dot const)
        case ShiftVectorBoxedMatcher(_, _, _) => (self dot sparseBoxed) + (self dot const)
        case _ => (self *^ vector).reduce
      }
    }
    def *(matrix: Matrix[T])(implicit n: Numeric[T]): Vector[T] = {
      def mV = CompoundMatrix(items.map(v => ConstVector(v, length)), matrix.numRows)
      def standart = (matrix *^^ mV).sumByColumns
      matrix match {
        case DenseFlatMatrixMatcher(_, _) => standart
        case CompoundMatrixMatcher(_, _) => standart
        case ConstMatrixMatcher(value, _, _) => ConstVector(sum * value, length)
        case DiagonalMatrixMatcher(diagonalValues) => self *^ DenseVector(diagonalValues)
        case ConstDiagonalMatrixMatcher(diagonalValue, _) => self *^ diagonalValue
        case _ => !!!("matcher for @matrix argument in DenseFlatMatrix.*(matrix: Matrix[T]) is not specified.")
      }
    }

    def pow_^(order: DoubleRep)(implicit n: Numeric[T], o: Overloaded2): Vector[T] = {
      // TODO: match element[T]
      DenseVector(items.map(v => Math.pow(v.toDouble, order).asRep[T]))
    }

    def sum(implicit n: Numeric[T]): Rep[T] = reduce
    def reduce(implicit m: RepMonoid[T]): Rep[T] = items.reduce(m)

    def euclideanNorm(implicit num: Numeric[T]): DoubleRep = Math.sqrt(items.map(v => v * v).reduce.toDouble)
  }

  abstract class ConstVector[T](val constItem: Rep[T], val length: IntRep)(implicit val eT: Elem[T])
    extends AbstractVector[T] {

    def items: Coll[T] = Collection.replicate(length, constItem)
    def nonZeroIndices: Coll[Int] = IF (constItem !== zeroValue) THEN Collection.indexRange(length) ELSE Collection.empty[Int]
    def nonZeroValues:  Coll[T] =  IF (constItem !== zeroValue) THEN items ELSE Collection.empty[T]
    def nonZeroItems:   Coll[(Int, T)] = nonZeroIndices zip nonZeroValues

    def apply(i: IntRep): Rep[T] = constItem
    @OverloadId("apply_by_collection")
    def apply(is: Coll[Int])(implicit o: Overloaded1): Vector[T] = ConstVector(constItem, is.length)

    //def mapBy[R: Elem](f: Rep[T => R @uncheckedVariance]): Vector[R] = ConstVector(f(constItem), length)
    def filterBy(f: Rep[T @uncheckedVariance => Boolean]): Vector[T] = IF (f(constItem)) THEN ConstVector(constItem, length) ELSE ConstVector(constItem, 0)

    def +^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      def newValues = vector.nonZeroValues.map(v => v + constItem)
      def newItems = vector.nonZeroItems.map { case Pair(i, v) => (i, v + constItem) }
      vector match {
        case ConstVectorMatcher(cv, _) => ConstVector(constItem + cv, length)
        case SparseVectorMatcher(is, _, _) => ShiftVector(is, newValues, constItem, length)
        case SparseVectorBoxedMatcher(_, _) => ShiftVectorBoxed(newItems, constItem, length)
        case ShiftVectorMatcher(is, _, cv, _) => ShiftVector(is, newValues, constItem + cv, length)
        case ShiftVectorBoxedMatcher(_, cv, _) => ShiftVectorBoxed(newItems, constItem + cv, length)
        case _ => vector +^ self
      }
    }
    def -^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      def newValues = vector.nonZeroValues.map(v => constItem - v)
      def newItems = vector.nonZeroItems.map { case Pair(i, v) => (i, constItem - v) }
      vector match {
        case DenseVectorMatcher(vs) => DenseVector(vs.map(v => constItem - v))
        case ConstVectorMatcher(cv, _) => ConstVector(constItem - cv, length)
        case SparseVectorMatcher(is, _, _) => ShiftVector(is, newValues, constItem, length)
        case SparseVectorBoxedMatcher(_, _) => ShiftVectorBoxed(newItems, constItem, length)
        case ShiftVectorMatcher(is, _, cv, _) => ShiftVector(is, newValues, constItem - cv, length)
        case ShiftVectorBoxedMatcher(_, cv, _) => ShiftVectorBoxed(newItems, constItem - cv, length)
        case _ => !!!("matcher for @vector argument in ConstVector.-^(vector: Vector[T]) is not specified.")
      }
    }
    def *^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      def newValues = vector.nonZeroValues.map(v => v * constItem)
      def newItems = vector.nonZeroItems.map { case Pair(i, v) => (i, v * constItem) }
      vector match {
        case ConstVectorMatcher(cv, _) => ConstVector(constItem * cv, length)
        case SparseVectorMatcher(is, _, _) => SparseVector(is, newValues, length)
        case SparseVectorBoxedMatcher(_, _) => SparseVectorBoxed(newItems, length)
        case ShiftVectorMatcher(is, _, cv, _) => ShiftVector(is, newValues, constItem * cv, length)
        case ShiftVectorBoxedMatcher(_, cv, _) => ShiftVectorBoxed(newItems, constItem * cv, length)
        case _ => vector *^ self
      }
    }
    def /^(vector: Vector[T])(implicit f: Fractional[T]): Vector[T] = {
      def flatItems = vector.items.map(v => constItem / v)
      def newItems = vector.nonZeroItems.map { case Pair(i, v) => (i, constItem / v) }
      vector match {
        case DenseVectorMatcher(_) => DenseVector(flatItems)
        case ConstVectorMatcher(cv, _) => ConstVector(constItem / cv, length)
        case SparseVectorMatcher(_, _, _) => DenseVector(flatItems)
        case SparseVectorBoxedMatcher(_, _) => DenseVector(flatItems)
        case ShiftVectorMatcher(is, vs, cv, _) => ShiftVector(is, vs.map(v => constItem / v), constItem / cv, length)
        case ShiftVectorBoxedMatcher(_, cv, _) => ShiftVectorBoxed(newItems, constItem / cv, length)
        case _ => !!!("matcher for @vector argument in ConstVector./^(vector: Vector[T]) is not specified.")
      }
    }
    def dot(vector: Vector[T])(implicit n: Numeric[T]): Rep[T] = {
      def sum = vector.nonZeroValues.reduce
      def shift = (vector.length - vector.nonZeroValues.length).to[T] * vector.constItem
      vector match {
        case ConstVectorMatcher(cv, _) => constItem * cv * length.to[T]
        case SparseVectorMatcher(_, _, _) => constItem * sum
        case SparseVectorBoxedMatcher(_, _) => constItem * sum
        case ShiftVectorMatcher(_, _, _, _) => constItem * (sum + shift)
        case ShiftVectorBoxedMatcher(_, _, _) => constItem * (sum + shift)
        case _ => vector dot self
      }
    }
    def *(matrix: Matrix[T])(implicit n: Numeric[T]): Vector[T] = ???

    def pow_^(order: DoubleRep)(implicit n: Numeric[T], o: Overloaded2): Vector[T] = {
      ConstVector(Math.pow(constItem.toDouble, order).asRep[T], length)
    }
    def sum(implicit n: Numeric[T]): Rep[T] = constItem * length.to[T]
    // TODO: need some monoid matching or optimization rule
    def reduce(implicit m: RepMonoid[T]): Rep[T] = items.reduce(m)

    def euclideanNorm(implicit num: Numeric[T]): DoubleRep = Math.sqrt(items.map(v => v * v).reduce.toDouble)
  }

  abstract class SparseVector[T](val nonZeroIndices: Coll[Int], val nonZeroValues: Coll[T],
                                 val length: IntRep)(implicit val eT: Elem[T])
    extends AbstractVector[T] {

    def items: Coll[T] = Collection.replicate(length, zeroValue).updateMany(nonZeroIndices, nonZeroValues)
    def constItem = zeroValue
    def nonZeroItems: Coll[(Int, T)] = nonZeroIndices zip nonZeroValues

    def apply(i: IntRep): Rep[T] = {
      val zero = toRep(0)
      IF (nonZeroIndices.length > zero) THEN {
        val k = binarySearch(i, nonZeroIndices)
        IF (k >= zero) THEN nonZeroValues(k) ELSE zeroValue
      } ELSE zeroValue
    }

    @OverloadId("apply_by_collection")
    def apply(is: Coll[Int])(implicit o: Overloaded1): Vector[T] = ??? // TODO: need efficient way to get value by index

    //def mapBy[R: Elem](f: Rep[T => R @uncheckedVariance]): Vector[R] = {
    //  IF (f(zeroValue) === element[R].defaultRepValue) THEN {
    //    SparseVector(nonZeroIndices, nonZeroValues.mapBy(f), length)
    //  } ELSE {
    //    ???
    //  }
    //}
    def filterBy(f: Rep[T @uncheckedVariance => Boolean]): Vector[T] = {
      // TODO: need to consider f(zeroValue) === FALSE
      val filteredItems = nonZeroItems.filter { v => f(v._2) }
      SparseVector(filteredItems.as, filteredItems.bs, length)
    }

    def +^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      val (is1, vs1, x1, x2, c2) = (nonZeroIndices, nonZeroValues, nonZeroItems, vector.nonZeroItems, vector.constItem)
      def newItems = x1 outerSum x2
      def shiftedItems = (x1 outerSum x2.map(v => (v._1, v._2 - c2))).map(v => (v._1, v._2 + c2))
      vector match {
        case SparseVectorMatcher(_, _, _) => SparseVector(newItems.as, newItems.bs, length)
        case SparseVectorBoxedMatcher(_, _) => SparseVectorBoxed(newItems, length)
        case ShiftVectorMatcher(_, _, _, _) => ShiftVector(shiftedItems.as, shiftedItems.bs, c2, length)
        case ShiftVectorBoxedMatcher(_, _, _) => ShiftVectorBoxed(shiftedItems, c2, length)
        case _ => vector +^ self
      }
    }
    def -^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      val (is1, vs1, x1, x2, c2) = (nonZeroIndices, nonZeroValues, nonZeroItems, vector.nonZeroItems, vector.constItem)
      def newItems = x1 outerSubtr x2
      def shiftedItems = (x1 outerSubtr x2.map(v => (v._1, v._2 - c2))).map(v => (v._1, v._2 - c2))
      vector match {
        case DenseVectorMatcher(vs) => DenseVector(vs.map(-_).updateMany(is1, (vs1 zip vs(is1)).map(v => v._1 - v._2)))
        case ConstVectorMatcher(_, _) => ShiftVector(is1, vs1.map(v => v - c2), -c2, length)
        case SparseVectorMatcher(_, _, _) => SparseVector(newItems.as, newItems.bs, length)
        case SparseVectorBoxedMatcher(_, _) => SparseVectorBoxed(newItems, length)
        case ShiftVectorMatcher(_, _, _, _) => ShiftVector(shiftedItems.as, shiftedItems.bs, - c2, length)
        case ShiftVectorBoxedMatcher(_, _, _) => ShiftVectorBoxed(shiftedItems, - c2, length)
        case _ => !!!("matcher for @vector argument in SparseVector.-^(vector: Vector[T]) is not specified.")
      }
    }
    def *^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      lazy val (x1, x2, c2) = (nonZeroItems, vector.nonZeroItems, vector.constItem)
      def newItems = x1 innerMult x2
      def shiftedItems = (x1 innerMult x2.map(v => (v._1, v._2 - c2))) outerSum (x1.map(v => (v._1, v._2 * c2)))
      vector match {
        case SparseVectorMatcher(_, _, _) => SparseVector(newItems.as, newItems.bs, length)
        case SparseVectorBoxedMatcher(_, _) => SparseVectorBoxed(newItems, length)
        case ShiftVectorMatcher(_, _, _, _) => ShiftVector(shiftedItems.as, shiftedItems.bs, constItem * c2, length)
        case ShiftVectorBoxedMatcher(_, _, _) => ShiftVectorBoxed(shiftedItems, constItem * c2, length)
        case _ => vector *^ self
      }
    }
    def /^(vector: Vector[T])(implicit f: Fractional[T]): Vector[T] = {
      lazy val (is, vs) = (nonZeroIndices, nonZeroValues)
      def newValues = (vs zip vector.items(is)).map { case Pair(v1, v2) => v1 / v2 }
      // TODO: ShiftVectors can be more optimal in this case
      vector match {
        case DenseVectorMatcher(_) => SparseVector(is, newValues, length)
        case ConstVectorMatcher(cv, _) => SparseVector(is, vs.map(v => v / cv), length)
        case SparseVectorMatcher(_, _, _) => SparseVector(is, newValues, length)
        case SparseVectorBoxedMatcher(_, _) => SparseVector(is, newValues, length)
        case ShiftVectorMatcher(_, _, _, _) => SparseVector(is, newValues, length)
        case ShiftVectorBoxedMatcher(_, _, _) => SparseVector(is, newValues, length)
        case _ => !!!("matcher for @vector argument in SparseVector./^(vector: Vector[T]) is not specified.")
      }
    }
    def dot(vector: Vector[T])(implicit n: Numeric[T]): Rep[T] = {
      lazy val (sum, c2, len) = (nonZeroValues.reduce, vector.constItem, vector.length)
      def sparse = SparseVector(vector.nonZeroIndices, vector.nonZeroValues.map(v => v - c2), len)
      def sparseBoxed = SparseVectorBoxed(vector.nonZeroItems.map(v => (v._1, v._2 - c2)), len)
      vector match {
        case SparseVectorMatcher(_, _, _) => (self *^ vector).nonZeroValues.reduce
        case SparseVectorBoxedMatcher(_, _) => (self *^ vector).nonZeroValues.reduce
        case ShiftVectorMatcher(_, _, _, _) => (self dot sparse) + sum * c2
        case ShiftVectorBoxedMatcher(_, _, _) => (self dot sparseBoxed) + sum * c2
        case _ => vector dot self
      }
    }
    def *(matrix: Matrix[T])(implicit n: Numeric[T]): Vector[T] = ???

    def pow_^(order: DoubleRep)(implicit n: Numeric[T], o: Overloaded2): Vector[T] = {
      SparseVector(nonZeroIndices, nonZeroValues.map(v => Math.pow(v.toDouble, order).asRep[T]), length)
    }

    def sum(implicit n: Numeric[T]): Rep[T] = nonZeroValues.reduce
    def reduce(implicit m: RepMonoid[T]): Rep[T] = {
      if (m.zero == zeroValue) nonZeroValues.reduce(m) else items.reduce(m)
    }  //TODO: it's inefficient

    def euclideanNorm(implicit num: Numeric[T]): DoubleRep = Math.sqrt(nonZeroValues.map(v => v * v).reduce.toDouble)
  }

  abstract class SparseVectorBoxed[T](val nonZeroItems: Coll[(Int, T)], val length: IntRep)(implicit val eT: Elem[T])
    extends AbstractVector[T] {

    def items: Coll[T] = Collection.replicate(length, zeroValue).updateMany(nonZeroIndices, nonZeroValues)
    def constItem = zeroValue
    def nonZeroIndices: Coll[Int] = nonZeroItems.as
    def nonZeroValues: Coll[T] = nonZeroItems.bs

    def apply(i: IntRep): Rep[T] = {
      val zero = toRep(0)
      IF (nonZeroIndices.length > zero) THEN {
        val k = binarySearch(i, nonZeroIndices)
        IF (k >= zero) THEN nonZeroValues(k) ELSE zeroValue
      } ELSE zeroValue
    }

    @OverloadId("apply_by_collection")
    def apply(is: Coll[Int])(implicit o: Overloaded1): Vector[T] = ??? // TODO: need efficient way to get value by index

    //def mapBy[R: Elem](f: Rep[T => R @uncheckedVariance]): Vector[R] = {
    //  IF (f(zeroValue) === element[R].defaultRepValue) THEN {
    //    SparseVector(nonZeroIndices, nonZeroValues.mapBy(f), length)
    //  } ELSE {
    //    ???
    //  }
    //}
    def filterBy(f: Rep[T @uncheckedVariance => Boolean]): Vector[T] = {
      val filteredItems = nonZeroItems.filter { v => f(v._2) }
      SparseVectorBoxed(filteredItems, length)
    }

    def +^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      val (x1, x2, c2) = (nonZeroItems, vector.nonZeroItems, vector.constItem)
      def shiftedItems = (x1 outerSum x2.map(v => (v._1, v._2 - c2))).map(v => (v._1, v._2 + c2))
      vector match {
        case SparseVectorBoxedMatcher(_, _) => SparseVectorBoxed(x1 outerSum x2, length)
        case ShiftVectorMatcher(_, _, _, _) => ShiftVector(shiftedItems.as, shiftedItems.bs, c2, length)
        case ShiftVectorBoxedMatcher(_, _, _) => ShiftVectorBoxed(shiftedItems, c2, length)
        case _ => vector +^ self
      }
    }
    def -^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      val (is1, vs1, x1, x2, c2) = (nonZeroIndices, nonZeroValues, nonZeroItems, vector.nonZeroItems, vector.constItem)
      def newItems = x1 outerSubtr x2
      def shiftedItems = (x1 outerSubtr x2.map(v => (v._1, v._2 - c2))).map(v => (v._1, v._2 - c2))
      vector match {
        case DenseVectorMatcher(vs) => DenseVector(vs.updateMany(is1, (vs1 zip vs(is1)).map(v => v._1 - v._2)))
        case ConstVectorMatcher(_, _) => ShiftVector(is1, vs1.map(v => v - c2), -c2, length)
        case SparseVectorMatcher(_, _, _) => SparseVector(newItems.as, newItems.bs, length)
        case SparseVectorBoxedMatcher(_, _) => SparseVectorBoxed(newItems, length)
        case ShiftVectorMatcher(_, _, _, _) => ShiftVector(shiftedItems.as, shiftedItems.bs, - c2, length)
        case ShiftVectorBoxedMatcher(_, _, _) => ShiftVectorBoxed(shiftedItems, - c2, length)
        case _ => !!!("matcher for @vector argument in SparseVector.-^(vector: Vector[T]) is not specified.")
      }
    }
    def *^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      lazy val (x1, x2, c2) = (nonZeroItems, vector.nonZeroItems, vector.constItem)
      def newItems = x1 innerMult x2
      def shiftedItems = (x1 innerMult x2.map(v => (v._1, v._2 - c2))) outerSum (x1.map(v => (v._1, v._2 * c2)))
      vector match {
        case SparseVectorMatcher(_, _, _) => SparseVector(newItems.as, newItems.bs, length)
        case SparseVectorBoxedMatcher(_, _) => SparseVectorBoxed(newItems, length)
        case ShiftVectorMatcher(_, _, _, _) => ShiftVector(shiftedItems.as, shiftedItems.bs, constItem * c2, length)
        case ShiftVectorBoxedMatcher(_, _, _) => ShiftVectorBoxed(shiftedItems, constItem * c2, length)
        case _ => vector *^ self
      }
    }
    def /^(vector: Vector[T])(implicit f: Fractional[T]): Vector[T] = {
      lazy val (is, vs) = (nonZeroIndices, nonZeroValues)
      def newValues = (vs zip vector.items(is)).map { case Pair(v1, v2) => v1 / v2 }
      // TODO: ShiftVectors can be more optimal in this case
      vector match {
        case DenseVectorMatcher(_) => SparseVector(is, newValues, length)
        case ConstVectorMatcher(cv, _) => SparseVector(is, vs.map(v => v / cv), length)
        case SparseVectorMatcher(_, _, _) => SparseVector(is, newValues, length)
        case SparseVectorBoxedMatcher(_, _) => SparseVector(is, newValues, length)
        case ShiftVectorMatcher(_, _, cv, _) => SparseVector(is, newValues, length)
        case ShiftVectorBoxedMatcher(_, cv, _) => SparseVector(is, newValues, length)
        case _ => !!!("matcher for @vector argument in SparseVector./^(vector: Vector[T]) is not specified.")
      }
    }
    def dot(vector: Vector[T])(implicit n: Numeric[T]): Rep[T] = {
      lazy val (sum, c2, len) = (nonZeroValues.reduce, vector.constItem, vector.length)
      def sparse = SparseVector(vector.nonZeroIndices, vector.nonZeroValues.map(v => v - c2), len)
      def sparseBoxed = SparseVectorBoxed(vector.nonZeroItems.map(v => (v._1, v._2 - c2)), len)
      vector match {
        case SparseVectorMatcher(_, _, _) => (self *^ vector).nonZeroValues.reduce
        case SparseVectorBoxedMatcher(_, _) => (self *^ vector).nonZeroValues.reduce
        case ShiftVectorMatcher(_, _, _, _) => (self dot sparse) + sum * c2
        case ShiftVectorBoxedMatcher(_, _, _) => (self dot sparseBoxed) + sum * c2
        case _ => vector dot self
      }
    }
    def *(matrix: Matrix[T])(implicit n: Numeric[T]): Vector[T] = ???

    def pow_^(order: DoubleRep)(implicit n: Numeric[T], o: Overloaded2): Vector[T] = {
      SparseVectorBoxed(nonZeroIndices zip nonZeroValues.map(v => Math.pow(v.toDouble, order).asRep[T]), length)
    }

    def sum(implicit n: Numeric[T]): Rep[T] = nonZeroValues.reduce
    def reduce(implicit m: RepMonoid[T]): Rep[T] = items.reduce(m)  //TODO: it's inefficient

    def euclideanNorm(implicit num: Numeric[T]): DoubleRep = Math.sqrt(nonZeroValues.map(v => v * v).reduce.toDouble)
  }

  abstract class ShiftVector[T](val nonZeroIndices: Coll[Int], val nonZeroValues: Coll[T],
                                val constItem: Rep[T], val length: IntRep)(implicit val eT: Elem[T])
    extends AbstractVector[T] {

    def items: Coll[T] = {
      Collection.replicate(length, constItem).updateMany(nonZeroIndices, nonZeroValues)
    }
    def nonZeroItems: Coll[(Int, T)] = nonZeroIndices zip nonZeroValues

    def apply(i: IntRep): Rep[T] = {
      val zero = toRep(0)
      IF (nonZeroIndices.length > zero) THEN {
        val k = binarySearch(i, nonZeroIndices)
        IF (k >= zero) THEN nonZeroValues(k) ELSE constItem
      } ELSE constItem
    }

    @OverloadId("apply_by_collection")
    def apply(is: Coll[Int])(implicit o: Overloaded1): Vector[T] = ??? // TODO: need efficient way to get value by index

    //def mapBy[R: Elem](f: Rep[T => R @uncheckedVariance]): Vector[R] = {
    //  IF (f(zeroValue) === element[R].defaultRepValue) THEN {
    //    SparseVector(nonZeroIndices, nonZeroValues.mapBy(f), length)
    //  } ELSE {
    //    ???
    //  }
    //}
    def filterBy(f: Rep[T @uncheckedVariance => Boolean]): Vector[T] = {
      val filteredItems = nonZeroItems.filter { v => f(v._2) }
      SparseVector(filteredItems.as, filteredItems.bs, length)
    }

    def +^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      lazy val (is1, is2, vs1, vs2) = (nonZeroIndices, vector.nonZeroIndices, nonZeroValues, vector.nonZeroValues)
      lazy val (x1, x2) = (vs1.map(v => v - constItem), vs2.map(v => v - vector.constItem))
      def shiftedItems = ((is1 zip x1) outerSum (is2 zip x2)).map(v => (v._1, v._2 + constItem + vector.constItem))
      vector match {
        case ShiftVectorMatcher(_, _, cv, _) => ShiftVector(shiftedItems.as, shiftedItems.bs, constItem + cv, length)
        case ShiftVectorBoxedMatcher(_, cv, _) => ShiftVectorBoxed(shiftedItems, constItem + cv, length)
        case _ => vector +^ self
      }
    }
    def -^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      lazy val (c1, c2, x1c, x2c) = (constItem, vector.constItem, nonZeroItems, vector.nonZeroItems)
      lazy val (x1, x2) = (x1c.map(v => (v._1, v._2 - c1)), x2c.map(v => (v._1, v._2 - c2)))
      def updates = (nonZeroValues zip vector.items(nonZeroIndices)).map { case Pair(v1, v2) => v1 - v2 }
      def newItems = (x1 outerSubtr x2c).map(v => (v._1, v._2 + c1))
      def shiftedItems = (x1 outerSubtr x2).map(v => (v._1, v._2 + c1 - c2))
      vector match {
        case DenseVectorMatcher(_) => DenseVector(vector.items.map(v => c1 - v).updateMany(nonZeroIndices, updates))
        case ConstVectorMatcher(_, _) => ShiftVector(nonZeroIndices, nonZeroValues.map(v => v - c2), c1 - c2, length)
        case SparseVectorMatcher(_, _, _) => ShiftVector(newItems.as, newItems.bs, c1, length)
        case SparseVectorBoxedMatcher(_, _) => ShiftVectorBoxed(newItems, c1, length)
        case ShiftVectorMatcher(_, _, _, _) => ShiftVector(shiftedItems.as, shiftedItems.bs, c1 - c2, length)
        case ShiftVectorBoxedMatcher(_, _, _) => ShiftVectorBoxed(shiftedItems, c1 - c2, length)
        case _ => !!!("matcher for @vector argument in ShiftVector.-^(vector: Vector[T]) is not specified.")
      }
    }
    def *^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      lazy val (c1, c2, x1c, x2c) = (constItem, vector.constItem, nonZeroItems, vector.nonZeroItems)
      lazy val (x1, x2) = (x1c.map(v => (v._1, v._2 - c1)), x2c.map(v => (v._1, v._2 - c2)))
      lazy val (x1_c2, x2_c1) = (x1.map(v => (v._1, v._2 * c2)), x2.map(v => (v._1, v._2 * c1)))
      def shiftedItems = ((x1 innerMult x2) outerSum x1_c2 outerSum x2_c1).map(v => (v._1, v._2 + c1 * c2))
      vector match {
        case ShiftVectorMatcher(_, _, _, _) => ShiftVector(shiftedItems.as, shiftedItems.bs, c1 * c2, length)
        case ShiftVectorBoxedMatcher(_, _, _) => ShiftVectorBoxed(shiftedItems, c1 * c2, length)
        case _ => vector *^ self
      }
    }
    def /^(vector: Vector[T])(implicit f: Fractional[T]): Vector[T] = {
      lazy val (is, vs, c1) = (nonZeroIndices, nonZeroValues, constItem)
      def updates = (vs zip vector.items(is)).map { case Pair(v1, v2) => v1 / v2 }
      def shiftedItems = vector.items.map(v => c1 / v).updateMany(is, updates)
      vector match {
        case DenseVectorMatcher(_) => DenseVector(shiftedItems)
        case ConstVectorMatcher(c2, _) => ShiftVector(is, vs.map(v => v / c2), c1 / c2, length)
        case SparseVectorMatcher(_, _, _) => DenseVector(shiftedItems)
        case SparseVectorBoxedMatcher(_, _) => DenseVector(shiftedItems)
        case ShiftVectorMatcher(_, _, _, _) => DenseVector(shiftedItems)
        case ShiftVectorBoxedMatcher(_, _, _) => DenseVector(shiftedItems)
        case _ => !!!("matcher for @vector argument in ShiftVector./^(vector: Vector[T]) is not specified.")
      }
    }
    def dot(vector: Vector[T])(implicit n: Numeric[T]): Rep[T] = {
      lazy val (c1, c2, len) = (constItem, vector.constItem, vector.length)
      def sparse = SparseVector(vector.nonZeroIndices, vector.nonZeroValues.map(v => v - c2), len)
      def sparseBoxed = SparseVectorBoxed(vector.nonZeroItems.map(v => (v._1, v._2 - c2)), len)
      def shift = (nonZeroValues.reduce + (len - nonZeroValues.length).to[T] * c1) * c2
      vector match {
        case ShiftVectorMatcher(_, _, _, _) => (self dot sparse) + shift
        case ShiftVectorBoxedMatcher(_, _, _) => (self dot sparseBoxed) + shift
        case _ => vector dot self
      }
    }
    def *(matrix: Matrix[T])(implicit n: Numeric[T]): Vector[T] = ???

    def pow_^(order: DoubleRep)(implicit n: Numeric[T], o: Overloaded2): Vector[T] = {
      SparseVector(nonZeroIndices, nonZeroValues.map(v => Math.pow(v.toDouble, order).asRep[T]), length)
    }

    def sum(implicit n: Numeric[T]): Rep[T] = nonZeroValues.reduce + constItem
    def reduce(implicit m: RepMonoid[T]): Rep[T] = {
      if (m.zero == zeroValue) nonZeroValues.reduce(m) else items.reduce(m)
    }  //TODO: it's inefficient

    def euclideanNorm(implicit num: Numeric[T]): DoubleRep = Math.sqrt(nonZeroValues.map(v => v * v).reduce.toDouble)
  }

  abstract class ShiftVectorBoxed[T](val nonZeroItems: Coll[(Int, T)], val constItem: Rep[T], 
                                     val length: IntRep)(implicit val eT: Elem[T])
    extends AbstractVector[T] {

    def items = Collection.replicate(length, constItem).updateMany(nonZeroIndices, nonZeroValues)
    def nonZeroIndices = nonZeroItems.as
    def nonZeroValues = nonZeroItems.bs

    def apply(i: IntRep) = {
      val zero = toRep(0)
      IF (nonZeroIndices.length > zero) THEN {
        val k = binarySearch(i, nonZeroIndices)
        IF (k >= zero) THEN nonZeroValues(k) ELSE zeroValue
      } ELSE zeroValue
    }

    @OverloadId("apply_by_collection")
    def apply(is: Coll[Int])(implicit o: Overloaded1): Vector[T] = ??? // TODO: need efficient way to get value by index

    //def mapBy[R: Elem](f: Rep[T => R @uncheckedVariance]): Vector[R] = {
    //  IF (f(zeroValue) === element[R].defaultRepValue) THEN {
    //    SparseVector(nonZeroIndices, nonZeroValues.mapBy(f), length)
    //  } ELSE {
    //    ???
    //  }
    //}
    def filterBy(f: Rep[T @uncheckedVariance => Boolean]): Vector[T] = {
      val filteredItems = nonZeroItems.filter { v => f(v._2) }
      SparseVectorBoxed(filteredItems, length)
    }

    def +^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      lazy val (c1, c2) = (constItem, vector.constItem)
      lazy val (x1, x2) = (nonZeroItems.map(v => (v._1, v._2 - c1)), vector.nonZeroItems.map(v => (v._1, v._2 - c2)))
      def shiftedItems = (x1 outerSum x2).map(v => (v._1, v._2 + constItem + vector.constItem))
      vector match {
        case ShiftVectorBoxedMatcher(_, cv, _) => ShiftVectorBoxed(shiftedItems, constItem + cv, length)
        case _ => vector +^ self
      }
    }
    def -^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      lazy val (c1, c2, x2c) = (constItem, vector.constItem, vector.nonZeroItems)
      lazy val (x1, x2) = (nonZeroItems.map(v => (v._1, v._2 - c1)), x2c.map(v => (v._1, v._2 - c2)))
      def updates = (nonZeroValues zip vector.items(nonZeroIndices)).map { case Pair(v1, v2) => v1 - v2 }
      def newItems = (x1 outerSubtr x2c).map(v => (v._1, v._2 + c1))
      def shiftedItems = (x1 outerSubtr x2).map(v => (v._1, v._2 + c1 - c2))
      vector match {
        case DenseVectorMatcher(vs) => DenseVector(vs.map(v => c1 - v).updateMany(nonZeroIndices, updates))
        case ConstVectorMatcher(_, _) => ShiftVectorBoxed(nonZeroItems.map(v => (v._1, v._2 - c2)), c1 - c2, length)
        case SparseVectorMatcher(_, _, _) => ShiftVectorBoxed(newItems, -c2, length)
        case SparseVectorBoxedMatcher(_, _) => ShiftVectorBoxed(newItems, -c2, length)
        case ShiftVectorMatcher(_, _, _, _) => ShiftVectorBoxed(shiftedItems, c1 - c2, length)
        case ShiftVectorBoxedMatcher(_, _, _) => ShiftVectorBoxed(shiftedItems, c1 - c2, length)
        case _ => !!!("matcher for @vector argument in ShiftVectorBoxed.-^(vector: Vector[T]) is not specified.")
      }
    }
    def *^(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      lazy val (c1, c2) = (constItem, vector.constItem)
      lazy val (x1, x2) = (nonZeroItems.map(v => (v._1, v._2 - c1)), vector.nonZeroItems.map(v => (v._1, v._2 - c2)))
      lazy val (x1_c2, x2_c1) = (x1.map(v => (v._1, v._2 * c2)), x2.map(v => (v._1, v._2 * c1)))
      def outerItems = (x1 innerMult x2) outerSum x1_c2 outerSum x2_c1
      def shiftedItems = outerItems.map(v => (v._1, v._2 + c1 * c2))
      vector match {
        case ShiftVectorBoxedMatcher(_, _, _) => ShiftVectorBoxed(shiftedItems, c1 * c2, length)
        case _ => vector *^ self
      }
    }
    def /^(vector: Vector[T])(implicit f: Fractional[T]): Vector[T] = {
      def updates = (nonZeroValues zip vector.items(nonZeroIndices)).map { case Pair(v1, v2) => v1 / v2 }
      def shiftedItems = vector.items.map(v => constItem / v).updateMany(nonZeroIndices, updates)
      def newItems = nonZeroItems.map(v => (v._1, v._2 / vector.constItem))
      vector match {
        case DenseVectorMatcher(_) => DenseVector(shiftedItems)
        case ConstVectorMatcher(c2, _) => ShiftVectorBoxed(newItems, constItem / c2, length)
        case SparseVectorMatcher(_, _, _) => DenseVector(shiftedItems)
        case SparseVectorBoxedMatcher(_, _) => DenseVector(shiftedItems)
        case ShiftVectorMatcher(_, _, _, _) => DenseVector(shiftedItems)
        case ShiftVectorBoxedMatcher(_, _, _) => DenseVector(shiftedItems)
        case _ => !!!("matcher for @vector argument in ShiftVectorBoxed./^(vector: Vector[T]) is not specified.")
      }
    }
    def dot(vector: Vector[T])(implicit n: Numeric[T]): Rep[T] = {
      lazy val (c1, c2, len) = (constItem, vector.constItem, vector.length)
      def sparseBoxed = SparseVectorBoxed(vector.nonZeroItems.map(v => (v._1, v._2 - c2)), len)
      def shift = (nonZeroValues.reduce + (len - nonZeroValues.length).to[T] * c1) * c2
      vector match {
        case ShiftVectorBoxedMatcher(_, _, _) => (self dot sparseBoxed) + shift
        case _ => vector dot self
      }
    }
    def *(matrix: Matrix[T])(implicit n: Numeric[T]): Vector[T] = ???

    def pow_^(order: DoubleRep)(implicit n: Numeric[T], o: Overloaded2): Vector[T] = {
      SparseVectorBoxed(nonZeroIndices zip nonZeroValues.map(v => Math.pow(v.toDouble, order).asRep[T]), length)
    }

    def sum(implicit n: Numeric[T]): Rep[T] = ???
    def reduce(implicit m: RepMonoid[T]): Rep[T] = items.reduce(m)  //TODO: it's inefficient

    def euclideanNorm(implicit num: Numeric[T]): DoubleRep = Math.sqrt(nonZeroValues.map(v => v * v).reduce.toDouble)
  }

  trait AbstractVectorCompanion extends TypeFamily1[AbstractVector] {
    def zero[T: Elem](len: IntRep): Vector[T] = ??? //DenseVector.zero[T](len)
    def fromSparseData[T: Elem](nonZeroIndices: Coll[Int],
                                nonZeroValues: Coll[T], length: IntRep): Vector[T] = ???
  }

  trait DenseVectorCompanion extends ConcreteClass1[DenseVector] {
    def zero[T: Elem](len: IntRep): Vector[T] = {
      val zeroV = element[T].defaultRepValue
      DenseVector(Collection.replicate(len, zeroV))
    }
    def fromSparseData[T: Elem](nonZeroIndices: Coll[Int],
                                nonZeroValues: Coll[T], length: IntRep): Vector[T] = ???
  }
  trait ConstVectorCompanion extends ConcreteClass1[ConstVector] {
    def zero[T: Elem](len: IntRep): Vector[T] = {
      val zeroV = element[T].defaultRepValue
      ConstVector(zeroV, len)
    }
    def fromSparseData[T: Elem](nonZeroIndices: Coll[Int],
                                         nonZeroValues: Coll[T], length: IntRep): Vector[T] = ???
  }
  trait SparseVectorCompanion extends ConcreteClass1[SparseVector] {
    def apply[T: Elem](items: Coll[T])(implicit n: Numeric[T], o: Overloaded1): Rep[SparseVector[T]] = {
      val nonZeroItems =
        (Collection.indexRange(items.length) zip items).filter { case Pair(i, v) => v !== n.zero }
      SparseVector(nonZeroItems, items.length)
    }
    @OverloadId("SparseVectorCompanion_apply_nonZeroItems")
    def apply[T: Elem](nonZeroItems: Coll[(Int, T)], length: IntRep)
                      (implicit n: Numeric[T], o: Overloaded2): Rep[SparseVector[T]] = {
      SparseVector(nonZeroItems.as, nonZeroItems.bs, length)
    }
    def zero[T: Elem](len: IntRep) = SparseVector(emptyColl[Int], emptyColl[T], len)
    def fromSparseData[T: Elem](nonZeroIndices: Coll[Int], nonZeroValues: Coll[T],
                                         length: IntRep): Vector[T] = SparseVector(nonZeroIndices, nonZeroValues, length)
  }
  trait SparseVectorBoxedCompanion extends ConcreteClass1[SparseVectorBoxed] {
    def apply[T: Elem](items: Coll[T])(implicit n: Numeric[T], o: Overloaded1): Rep[SparseVectorBoxed[T]] = {
      val nonZeroItems =
        (Collection.indexRange(items.length) zip items).filter { case Pair(i, v) => v !== n.zero }
      SparseVectorBoxed(nonZeroItems, items.length)
    }
    @OverloadId("SparseVector1Companion_apply_nonZeroItems")
    def apply[T: Elem](nonZeroIndices: Coll[Int], nonZeroValues: Coll[T], length: IntRep)
                      (implicit n: Numeric[T], o: Overloaded2): Rep[SparseVectorBoxed[T]] = {
      SparseVectorBoxed(nonZeroIndices zip nonZeroValues, length)
    }
    def zero[T: Elem](len: IntRep) = SparseVector(emptyColl[Int], emptyColl[T], len)
    def fromSparseData[T: Elem](nonZeroIndices: Coll[Int], nonZeroValues: Coll[T], length: IntRep): Vector[T] = SparseVectorBoxed(nonZeroIndices zip nonZeroValues, length)
  }
}

trait VectorsDsl extends CollectionsDsl with impl.VectorsAbs { self: LADsl =>

  type VectorCompanion = Rep[AbstractVectorCompanion]

  def dotSparse[T: Elem](xIndices: Coll[Int], xValues: Coll[T], yIndices: Coll[Int], yValues: Coll[T])
                        (implicit n: Numeric[T]): Rep[T]

  def dotMerge[T: Elem](xItems: Coll[T], yIndices: Coll[Int], yValues: Coll[T])
                       (implicit n: Numeric[T]): Rep[T] = {
    (xItems(yIndices) zip yValues).map { case Pair(x, y) => x * y }.reduce
  }

  /*def innerJoin[T: Elem](xIndices: Coll[Int], xValues: Coll[T], yIndices: Coll[Int], yValues: Coll[T],
                         f: Rep[((T, T)) => T])(implicit n: Numeric[T]): PairColl[Int, T] =
    (xIndices zip xValues).innerJoin(yIndices zip yValues, f)

  def outerJoin[T: Elem](xIndices: Coll[Int], xValues: Coll[T], yIndices: Coll[Int], yValues: Coll[T],
                         f: Rep[((T, T)) => T])(implicit n: Numeric[T]): PairColl[Int, T] =
     (xIndices zip xValues).outerJoin(yIndices zip yValues, f)*/

  def binarySearch(index: IntRep, indices: Coll[Int]): IntRep

  implicit class VectorExtensions[T](vector: Vector[T]) {
    implicit def eItem: Elem[T] = vector.selfType1.asInstanceOf[AbstractVectorElem[T, _]].eT

    //def map[R: Elem](f: Rep[T] => Rep[R]): Vector[R] = vector.mapBy(fun(f))

    def filter(f: Rep[T] => Rep[Boolean]): Vector[T] = vector.filterBy(fun(f))
  }
}

trait VectorsDslSeq extends CollectionsDslSeq with impl.VectorsSeq { self: LADslSeq =>

  def dotSparse[T: Elem](xIndices: Coll[Int], xValues: Coll[T], yIndices: Coll[Int], yValues: Coll[T])
                        (implicit n: Numeric[T]): Rep[T] = {
    var result = n.zero
    val yMap = yIndices.arr.zip(yValues.arr).toMap
    xIndices.arr.zip(xValues.arr).foldLeft(n.zero) {
      case (acc, (i, x)) =>
      yMap.get(i) match {
        case Some(y) => acc + x * y
        case None => acc
      }
    }
  }

  def binarySearch(index: IntRep, indices: Coll[Int]): IntRep = {
    val zero = 0
    val one = 1
    val two = 2
    def check(start: Int, end: Int): Int = {
      if (end - start < two) {
        if (index === indices(start)) start else {
          if (index === indices(end)) end else -1
        }
      } else {
        val middle = (start + end) div two
        if (index === indices(middle)) middle else {
          if (index < indices(middle)) check(start, middle - one) else check(middle + one, end)
        }
      }
    }
    check(zero, Math.min(index, indices.length - one))
  }
}

trait VectorsDslExp extends CollectionsDslExp with impl.VectorsExp { self: LADslExp =>

  def dotSparse[T: Elem](xIndices: Coll[Int], xValues: Coll[T], yIndices: Coll[Int], yValues: Coll[T])
                        (implicit n: Numeric[T]): Rep[T] = {
    DotSparse(xIndices.arr, xValues.arr, yIndices.arr, yValues.arr)
  }

  case class DotSparse[T](xIndices: Arr[Int], xValues: Arr[T], yIndices: Arr[Int], yValues: Arr[T])
                         (implicit val n: Numeric[T], selfType: Elem[T]) extends BaseDef[T]

  def binarySearch(index: IntRep, indices: Coll[Int]): IntRep = array_binary_search(index, indices.arr)
}
