package scalan.linalgebra

/**
  * Created by Victor Smirnov on 3/12/15.
  */

import scalan._
import scalan.common.OverloadHack.{Overloaded2, Overloaded1}
import scala.annotation.unchecked.uncheckedVariance

trait Matrices extends Vectors { self: LADsl =>

  type Matrix[T] = Rep[AbstractMatrix[T]]

  trait AbstractMatrix[T] extends Def[AbstractMatrix[T]] {
    def numColumns: Rep[Int]
    def numRows: Rep[Int]
    implicit def eT: Elem[T]
    def rows: Rep[Collection[AbstractVector[T]]]
    def columns: Rep[Collection[AbstractVector[T]]]
    def rmValues: Rep[Collection[T]]
    def zeroValue = eT.defaultRepValue
    def constItem: Rep[T]
    def diagonalValues: Rep[Collection[T]]
    def replicatedRow: Vector[T]

    @OverloadId("rowsByVector")
    def apply(vector: Vector[Int])(implicit o: Overloaded2): Matrix[T] = apply(vector.items)
    @OverloadId("rows")
    def apply(iRows: Coll[Int])(implicit o: Overloaded1): Matrix[T]
    @OverloadId("row")
    def apply(row: Rep[Int]): Vector[T]
    def apply(row: Rep[Int], column: Rep[Int]): Rep[T]

    //def mapBy[R: Elem](f: Rep[T => R @uncheckedVariance]): Matrix[R]
    def mapRowsBy[R: Elem](f: Rep[AbstractVector[T] => AbstractVector[R] @uncheckedVariance]): Matrix[R]

    def transpose(implicit n: Numeric[T]): Matrix[T]
    // TODO: implement sumByRows and sumByColumns in specializations.
    def reduceByRows(implicit m: RepMonoid[T]): Vector[T] = {
      // TODO: no way it's good, specialize over classes
      DenseVector(rows.map(row => row.nonZeroValues.reduce))
    }
    def reduceByColumns(implicit m: RepMonoid[T], n: Numeric[T]): Vector[T]
    def sumByRows(implicit n: Numeric[T]): Vector[T]
    def sumByColumns(implicit n: Numeric[T]): Vector[T]

    def countNonZeroesByColumns(implicit n: Numeric[T]): Vector[Int] = {
      /*val zero = elem.defaultRepValue
      lazy val NonZeroesMonoid = RepMonoid[T]("NonZeroesMonoid", 0, false) {
        case (x1, x2) => (x1 !== zero).toInt + (x2 !== zero).toInt
      }*/
      val mT = transpose
      DenseVector(mT.rows.map(row => row.nonZeroIndices.length))
    }

    def +(matrix: Matrix[T])(implicit n: Numeric[T]): Matrix[T] = self +^^ matrix
    @OverloadId("matrix")
    def *(matrix: Matrix[T])(implicit n: Numeric[T], o: Overloaded1): Matrix[T]
    def *(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = DenseVector(rows.map(r => r dot vector))
    @OverloadId("matrix")
    def +^^(matrix: Matrix[T])(implicit n: Numeric[T]): Matrix[T]
    def +^^(value: Rep[T])(implicit n: Numeric[T], o: Overloaded1): Matrix[T] = {
      self +^^ ConstMatrix(value, numColumns, numRows)
    }
    @OverloadId("matrix")
    def *^^(matrix: Matrix[T])(implicit n: Numeric[T]): Matrix[T]
    def *^^(value: Rep[T])(implicit n: Numeric[T], o: Overloaded1): Matrix[T] = {
      self +^^ ConstMatrix(value, numColumns, numRows)
    }
    def average(implicit f: Fractional[T], m: RepMonoid[T]): Rep[T]
  }

  abstract class DenseFlatMatrix[T](val rmValues: Rep[Collection[T]], val numColumns: Rep[Int])
                                   (implicit val eT: Elem[T]) extends AbstractMatrix[T] {

    def items = rmValues
    def constItem = zeroValue
    def numRows: Rep[Int] = rmValues.length /! numColumns
    def columns: Rep[Collection[AbstractVector[T]]] = {
      Collection.indexRange(numColumns).map(i => DenseVector(Collection(rmValues.arr.stride(i, numRows, numColumns))))
    }
    def rows: Coll[DenseVector[T]] = Collection(rmValues.arr.grouped(numColumns).map(vs => DenseVector(Collection(vs))))
    def diagonalValues = rmValues(Collection.indexRange(Math.min(numRows, numColumns)).map(i => i * numColumns + i))
    def replicatedRow: Vector[T] = ConstVector(zeroValue, numColumns) // TODO: create ZeroVector if it's introduced

    @OverloadId("rows")
    def apply(iRows: Coll[Int])(implicit o: Overloaded1): Matrix[T] = {
      DenseFlatMatrix(iRows.map(i => items.slice(numColumns * i, numColumns)).flatMap(v => v), numColumns)
    }
    @OverloadId("row")
    def apply(row: Rep[Int]): Vector[T] = DenseVector(rmValues.slice(row * numColumns, numColumns))
    def apply(row: Rep[Int], column: Rep[Int]): Rep[T] = items(toCellIndex(row, column))

    def mapRowsBy[R: Elem](f: Rep[AbstractVector[T] => AbstractVector[R] @uncheckedVariance]): Matrix[R] = {
      DenseFlatMatrix.fromRows(rows.mapBy(f), numColumns)
    }

    def fromCellIndex(iCell: Rep[Int]): Rep[(Int, Int)] = Pair(iCell /! numColumns, iCell % numColumns)
    def toCellIndex(iRow: Rep[Int], iCol: Rep[Int]): Rep[Int] = numColumns * iRow + iCol

    @OverloadId("block_size")
    def transpose(blockSize: Rep[Int])(implicit n: Numeric[T]): Matrix[T] = {
      DenseFlatMatrix(columns.flatMap(col => col.items), numRows)
    }
    def transpose(implicit n: Numeric[T]): Matrix[T] = transpose(10)

    def reduceByColumns(implicit m: RepMonoid[T], n: Numeric[T]): Vector[T] = {
      DenseVector(Collection.indexRange(numColumns).map(column => rows.map(row => row(column)).reduce(m)))
    }
    def sumByRows(implicit n: Numeric[T]): Vector[T] = ???
    def sumByColumns(implicit n: Numeric[T]): Vector[T] = ???

    @OverloadId("matrix")
    def *(matrix: Matrix[T])(implicit n: Numeric[T], o: Overloaded1): Matrix[T] = {
      def mT = matrix.transpose
      def direct = rows.flatMap { row => (mT * row).items}
      matrix match {
        case DenseFlatMatrix(_, width) =>
          DenseFlatMatrix(direct, width)
        case CompoundMatrix(_, width) =>
          DenseFlatMatrix(direct, width)
        case ConstMatrix(value, width, _) =>
          val rowsConstant = (reduceByRows *^ value).items.map(v => ConstVector(v, width))
          CompoundMatrix(rowsConstant, width)
        case DiagonalMatrix(diagonalValues) =>
          val diagonalReplicated = Collection.replicate(numRows, diagonalValues).flatMap(coll => coll)
          DenseFlatMatrix((DenseVector(rmValues) *^ DenseVector(diagonalReplicated)).items, numColumns)
        case ConstDiagonalMatrix(diagonalValue, _) =>
          DenseFlatMatrix((DenseVector(rmValues) *^ diagonalValue).items, numColumns)
        case _ => !!!("matcher for @matrix argument in DenseFlatMatrix.*(matrix: Matrix[T]) is not specified.")
      }
    }

    @OverloadId("matrix")
    def +^^(matrix: Matrix[T])(implicit n: Numeric[T]): Matrix[T] = {
      matrix match {
        case DenseFlatMatrix(rmValues1, _) =>
          DenseFlatMatrix((DenseVector(rmValues) +^ DenseVector(rmValues1)).items, numColumns)
        case CompoundMatrix(rows1, _) =>
          DenseFlatMatrix((rows zip rows1).flatMap { case Pair(v1, v2) => (v1 +^ v2).items }, numColumns)
        case ConstMatrix(value, _, _) =>
          DenseFlatMatrix((DenseVector(rmValues) +^ value).items, numColumns)
        case DiagonalMatrix(diagonal) =>
          val width = diagonal.length
          val mainDiagonalIndices = Collection.indexRange(width).map(i => i * width + i)
          val newValues = (diagonal zip rmValues(mainDiagonalIndices)).map { case Pair(d, v) => d + v }
          DenseFlatMatrix(rmValues.updateMany(mainDiagonalIndices, newValues), numColumns)
        case ConstDiagonalMatrix(diagonalValue, width) =>
          val mainDiagonalIndices = Collection.indexRange(width).map(i => i * width + i)
          val newValues = rmValues(mainDiagonalIndices).map(v => diagonalValue + v)
          DenseFlatMatrix(rmValues.updateMany(mainDiagonalIndices, newValues), numColumns)
        case _ => !!!("matcher for @matrix argument in DenseFlatMatrix.+^^(matrix: Matrix[T]) is not specified.")
      }
    }

    @OverloadId("matrix")
    def *^^(matrix: Matrix[T])(implicit n: Numeric[T]): Matrix[T] = {
      matrix match {
        case DenseFlatMatrix(rmValues1, _) =>
          DenseFlatMatrix((DenseVector(rmValues) *^ DenseVector(rmValues1)).items, numColumns)
        case CompoundMatrix(rows1, _) =>
          CompoundMatrix((rows zip rows1).map { case Pair(v1, v2) => v1 *^ v2 }, numColumns)
        case ConstMatrix(value, _, _) =>
          DenseFlatMatrix((DenseVector(rmValues) *^ value).items, numColumns)
        case DiagonalMatrix(diagonalValues) =>
          val width = diagonalValues.length
          val mainDiagonalIndices = Collection.indexRange(width).map(i => i * width + i)
          DiagonalMatrix((DenseVector(rmValues(mainDiagonalIndices)) *^ DenseVector(diagonalValues)).items)
        case ConstDiagonalMatrix(diagonalValue, width) =>
          val mainDiagonalIndices = Collection.indexRange(width).map(i => i * width + i)
          DiagonalMatrix((DenseVector(rmValues(mainDiagonalIndices)) *^ diagonalValue).items)
        case _ => !!!("matcher for @matrix argument in DenseFlatMatrix.*^^(matrix: Matrix[T]) is not specified.")
      }
    }

    def average(implicit f: Fractional[T], m: RepMonoid[T]): Rep[T] = {
      items.reduce / items.length.to[T]
    }
  }
/*
  abstract class ReplicatedMatrix[T](val replicatedRow: Vector[T], val numRows: Rep[Int])
                                    (implicit val eT: Elem[T]) extends AbstractMatrix[T] {

    def rows = Collection.replicate(numRows, replicatedRow)
    def columns = Collection.indexRange(numColumns).map(j => ConstVector(replicatedRow(j), numRows))
    def numColumns = replicatedRow.length
    def rmValues = rows.flatMap(row => row.items)
    def constItem = zeroValue
    def diagonalValues = Collection.indexRange(Math.min(numRows, numColumns)).map(i => replicatedRow(i))

    @OverloadId("rows") 
    def apply(iRows: Coll[Int])(implicit o: Overloaded1): Matrix[T] = {
      ReplicatedMatrix(replicatedRow, iRows.length)
    }
    @OverloadId("row")
    def apply(row: Rep[Int]): Vector[T] = replicatedRow
    def apply(row: Rep[Int], column: Rep[Int]): Rep[T] = replicatedRow(column)

    def mapRowsBy[R: Elem](f: Rep[AbstractVector[T] => AbstractVector[R] @uncheckedVariance]): Matrix[R] = {
      // no effects supported in lambda @f!
      val resultRows = Collection.singleton(replicatedRow).mapBy(f) // TODO: not the most elegant solution
      ReplicatedMatrix(resultRows(toRep(0)), numRows)
    }

    def transpose(implicit n: Numeric[T]): Matrix[T] = CompoundMatrix(columns, numRows)

    def reduceByColumns(implicit m: RepMonoid[T], n: Numeric[T]): Vector[T] = {
      DenseVector(columns.map(col => col.reduce(m)))
    }

    @OverloadId("matrix")
    def *(matrix: Matrix[T])(implicit n: Numeric[T], o: Overloaded1): Matrix[T] = {
      matrix match {
        case DenseFlatMatrix(rmValuesB, numColumnsB) =>
          val rowsNew = rows.map { vA =>
            // TODO: rewrite with respect towards type vectors in @self (if sparse - make it efficient)
            val itemsA = vA.items.flatMap(a => Collection.replicate(numColumnsB, a))
            DenseFlatMatrix((itemsA zip rmValuesB).map { case Pair(v1, v2) => v1 * v2 }, numColumnsB).reduceByColumns
          }
          CompoundMatrix(rowsNew, numColumnsB)
        case CompoundMatrix(rowsB, numColumnsB) =>
          val (is, vs) = (replicatedRow.nonZeroIndices, replicatedRow.nonZeroValues)
          val res = CompoundMatrix((vs zip rowsB(is)).map { case Pair(a, vB) => vB *^ a }, numColumnsB).reduceByColumns
          // TODO: find a proper way to carry over type of vector (Sparse or Dense)
          ReplicatedMatrix(res, numRows)
        case ReplicatedMatrix(rowsB, numColumnsB) =>
          val vs = matrix.replicatedRow
          val res = CompoundMatrix((vs zip rowsB(is)).map { case Pair(a, vB) => vB *^ a }, numColumnsB).reduceByColumns

        case ConstMatrix(value, width, _) =>
          val rowsConstant = (reduceByRows *^ value).items.map(v => ConstVector(v, width))
          CompoundMatrix(rowsConstant, width)
        case DiagonalMatrix(diagonalValues) =>
          val diagonalVector = DenseVector(diagonalValues)
          CompoundMatrix(rows.map(row => row *^ diagonalVector), numColumns)
        case ConstDiagonalMatrix(diagonalValue, _) =>
          CompoundMatrix(rows.map(row => row *^ diagonalValue), numColumns)
        case _ => !!!("matcher for @matrix argument in CompoundMatrix.*(matrix: Matrix[T]) is not specified.")
      }
    }

    @OverloadId("matrix")
    def +^^(matrix: Matrix[T])(implicit n: Numeric[T]): Matrix[T] = {
      def res = CompoundMatrix((rows zip matrix.rows).map { case Pair(v, s) => v +^ s }, numColumns)
      matrix match {
        case CompoundMatrix(_, _) => res
        case ConstMatrix(_, _, _) => res
        case DiagonalMatrix(_) => res
        case ConstDiagonalMatrix(_, _) => res
        case _ => matrix +^^ self
      }
    }

    @OverloadId("matrix")
    def *^^(matrix: Matrix[T])(implicit n: Numeric[T]): Matrix[T] = {
      def res = CompoundMatrix((rows zip matrix.rows).map { case Pair(v, s) => v *^ s }, numColumns)
      matrix match {
        case CompoundMatrix(_, _) => res
        case ConstMatrix(_, _, _) => res
        case DiagonalMatrix(diagonal) =>
          DiagonalMatrix((diagonalValues zip diagonal).map { case Pair(v, d) => v * d })
        case ConstDiagonalMatrix(diagonalValue, width) =>
          DiagonalMatrix(diagonalValues.map(v => v * diagonalValue))
        case _ => matrix *^^ self
      }
    }

    def average(implicit f: Fractional[T], m: RepMonoid[T]): Rep[T] = {
      val items = rows.flatMap(v => v.nonZeroValues)
      items.reduce / (numRows * numColumns).to[T]
    }
  }
*/
  abstract class CompoundMatrix[T](val rows: Rep[Collection[AbstractVector[T]]], val numColumns: Rep[Int])
                                  (implicit val eT: Elem[T]) extends AbstractMatrix[T] {

    def columns: Rep[Collection[AbstractVector[T]]] = {
      // TODO: inefficient
      Collection(SArray.tabulate(numColumns) { j => DenseVector(rows.map(_(j)))})
    }
    def numRows = rows.length
    def rmValues: Rep[Collection[T]] = rows.flatMap(row => row.items)
    def constItem = zeroValue
    def diagonalValues = {
      val width = Math.min(numRows, numColumns)
      Collection.indexRange(width).map(i => rows(i)(i))
    }
    def replicatedRow: Vector[T] = ConstVector(zeroValue, numColumns) // TODO: create ZeroVector if it's introduced

    @OverloadId("rows") 
    def apply(iRows: Coll[Int])(implicit o: Overloaded1): Matrix[T] = {
      CompoundMatrix(iRows.map(i => rows(i)), numColumns)
    }
    @OverloadId("row")
    def apply(row: Rep[Int]): Vector[T] = rows(row)
    def apply(row: Rep[Int], column: Rep[Int]): Rep[T] = apply(row)(column)

    def mapRowsBy[R: Elem](f: Rep[AbstractVector[T] => AbstractVector[R] @uncheckedVariance]): Matrix[R] = {
      CompoundMatrix(rows.mapBy(f), numColumns)
    }

    def transpose(implicit n: Numeric[T]): Matrix[T] = transposeDirect(self)

    def reduceByColumns(implicit m: RepMonoid[T], n: Numeric[T]): Vector[T] = {
      // TODO: inefficient
      val coll = Collection.indexRange(numColumns).map { column =>
        Collection.indexRange(numRows).map { row => rows(row)(column) }.reduce
      }
      DenseVector(coll)
      /*lazy val zeroVector = SparseVector(Collection(SArray.empty[Int]), Collection(SArray.empty[T]), length)
      lazy val VectorMonoid = RepMonoid[SparseVector[T]]("Vector", zeroVector, true) { (t1, t2) => t1 +^ t2 }
      rows.reduce(VectorMonoid)*/
    }
    def sumByRows(implicit n: Numeric[T]): Vector[T] = ???
    def sumByColumns(implicit n: Numeric[T]): Vector[T] = ???

    @OverloadId("matrix")
    def *(matrix: Matrix[T])(implicit n: Numeric[T], o: Overloaded1): Matrix[T] = {
      matrix match {
        case DenseFlatMatrix(rmValuesB, numColumnsB) =>
          val rowsNew = rows.map { vA =>
            // TODO: rewrite with respect towards type vectors in @self (if sparse - make it efficient)
            val itemsA = vA.items.flatMap(a => Collection.replicate(numColumnsB, a))
            DenseFlatMatrix((itemsA zip rmValuesB).map { case Pair(v1, v2) => v1 * v2 }, numColumnsB).reduceByColumns
          }
          CompoundMatrix(rowsNew, numColumnsB)
        case CompoundMatrix(rowsB, numColumnsB) =>
          val rowsNew = rows.map { vA =>
            val (is, vs) = (vA.nonZeroIndices, vA.nonZeroValues)
            val res = CompoundMatrix((vs zip rowsB(is)).map { case Pair(a, vB) => vB *^ a }, numColumnsB).reduceByColumns
            // TODO: find a proper way to carry over type of vector (Sparse or Dense)
            res//.convertTo(vA.element)
          }
          CompoundMatrix(rowsNew, numColumnsB)
        case ConstMatrix(value, width, _) =>
          val rowsConstant = (reduceByRows *^ value).items.map(v => ConstVector(v, width))
          CompoundMatrix(rowsConstant, width)
        case DiagonalMatrix(diagonalValues) =>
          val diagonalVector = DenseVector(diagonalValues)
          CompoundMatrix(rows.map(row => row *^ diagonalVector), numColumns)
        case ConstDiagonalMatrix(diagonalValue, _) =>
          CompoundMatrix(rows.map(row => row *^ diagonalValue), numColumns)
        case _ => !!!("matcher for @matrix argument in CompoundMatrix.*(matrix: Matrix[T]) is not specified.")
      }
    }

    @OverloadId("matrix")
    def +^^(matrix: Matrix[T])(implicit n: Numeric[T]): Matrix[T] = {
      def res = CompoundMatrix((rows zip matrix.rows).map { case Pair(v, s) => v +^ s }, numColumns)
      matrix match {
        case CompoundMatrix(_, _) => res
        case ConstMatrix(_, _, _) => res
        case DiagonalMatrix(_) => res
        case ConstDiagonalMatrix(_, _) => res
        case _ => matrix +^^ self
      }
    }

    @OverloadId("matrix")
    def *^^(matrix: Matrix[T])(implicit n: Numeric[T]): Matrix[T] = {
      def res = CompoundMatrix((rows zip matrix.rows).map { case Pair(v, s) => v *^ s }, numColumns)
      matrix match {
        case CompoundMatrix(_, _) => res
        case ConstMatrix(_, _, _) => res
        case DiagonalMatrix(diagonal) =>
          DiagonalMatrix((diagonalValues zip diagonal).map { case Pair(v, d) => v * d })
        case ConstDiagonalMatrix(diagonalValue, width) =>
          DiagonalMatrix(diagonalValues.map(v => v * diagonalValue))
        case _ => matrix *^^ self
      }
    }

    def average(implicit f: Fractional[T], m: RepMonoid[T]): Rep[T] = {
      val items = rows.flatMap(v => v.nonZeroValues)
      items.reduce / (numRows * numColumns).to[T]
    }
  }

  abstract class ConstMatrix[T](val constItem: Rep[T], val numColumns: Rep[Int], val numRows: Rep[Int])
                               (implicit val eT: Elem[T]) extends AbstractMatrix[T] {

    def rmValues = Collection.replicate(numColumns * numRows, constItem)
    def items = rmValues
    def columns = Collection.replicate(numColumns, ConstVector(constItem, numRows))
    def rows = Collection.replicate(numRows, ConstVector(constItem, numColumns))
    def diagonalValues = Collection.replicate(Math.min(numRows, numColumns), constItem)
    def replicatedRow: Vector[T] = ConstVector(zeroValue, numColumns) // TODO: create ZeroVector if it's introduced

    @OverloadId("rows")
    def apply(iRows: Coll[Int])(implicit o: Overloaded1): Matrix[T] = {
      ConstMatrix(constItem, numColumns, iRows.length)
    }
    @OverloadId("row")
    def apply(row: Rep[Int]): Vector[T] = ConstVector(constItem, numColumns)
    def apply(row: Rep[Int], column: Rep[Int]): Rep[T] = constItem

    def mapRowsBy[R: Elem](f: Rep[AbstractVector[T] => AbstractVector[R] @uncheckedVariance]): Matrix[R] = {
      // TODO: need a way to check @f for closure & effectfulness
      // TODO: in opposite case we can optimize this map due to constant input
      // TODO: -OR- we can use optimization rules in lower levels of Scalan
      // TODO: replicated rows for now, (possible) effects are ignored
      CompoundMatrix(rows.mapBy(f), numColumns)
    }

    def transpose(implicit n: Numeric[T]): Matrix[T] = ConstMatrix(constItem, numRows, numColumns)

    def reduceByColumns(implicit m: RepMonoid[T], n: Numeric[T]): Vector[T] = {
      // TODO: match monoids for optimal operations -OR- we can use optimization rules in lower levels of Scalan
      val res = Collection.replicate(numRows, constItem).reduce(m)
      val coll = Collection.replicate(numColumns, res)
      DenseVector(coll)
    }
    def sumByRows(implicit n: Numeric[T]): Vector[T] = ???
    def sumByColumns(implicit n: Numeric[T]): Vector[T] = ???

    override def countNonZeroesByColumns(implicit n: Numeric[T]): Vector[Int] = {
      ConstVector(IF (constItem !== zeroValue) THEN numRows ELSE toRep(0), numColumns)
    }

    override def *(vector: Vector[T])(implicit n: Numeric[T]): Vector[T] = {
      val dot = vector.reduce * constItem
      ConstVector(dot, numRows)
    }

    @OverloadId("matrix")
    def *(matrix: Matrix[T])(implicit n: Numeric[T], o: Overloaded1): Matrix[T] = {
      def row = matrix.reduceByColumns *^ constItem
      matrix match {
        case DenseFlatMatrix(rmValuesB, width) =>
          DenseFlatMatrix(Collection.replicate(numRows, row).flatMap(v => v.items), width)
        case CompoundMatrix(_, width) =>
          CompoundMatrix(Collection.replicate(numRows, row), width)
        case ConstMatrix(value, width, _) =>
          ConstMatrix(value * constItem * numColumns.to[T], numRows, width)
        case DiagonalMatrix(diagonalValues) =>
          val rowDiag = DenseVector(diagonalValues) *^ constItem
          // TODO: it can be optimized with new matrix class
          DenseFlatMatrix(Collection.replicate(numRows, rowDiag).flatMap(v => v.items), diagonalValues.length)
        case ConstDiagonalMatrix(diagonalValue, _) =>
          ConstMatrix(constItem * diagonalValue, numRows, numColumns)
        case _ => !!!("matcher for @matrix argument in ConstMatrix.*(matrix: Matrix[T]) is not specified.")
      }
    }

    @OverloadId("matrix")
    def +^^(matrix: Matrix[T])(implicit n: Numeric[T]): Matrix[T] = {
      matrix match {
        case ConstMatrix(other_item, _, _) =>
          ConstMatrix(constItem + other_item, numColumns, numRows)
        case DiagonalMatrix(_) => !!!("ConstMatrix +^^ DiagonalMatrix creates DenseFlatMatrix!")
        case ConstDiagonalMatrix(_, _) => !!!("ConstMatrix +^^ ConstDiagonalMatrix creates DenseFlatMatrix!")
        case _ => matrix +^^ self
      }
    }

    @OverloadId("matrix")
    def *^^(matrix: Matrix[T])(implicit n: Numeric[T]): Matrix[T] = {
      matrix match {
        case ConstMatrix(other_item, _, _) =>
          ConstMatrix(constItem * other_item, numColumns, numRows)
        case DiagonalMatrix(diagonal) =>
          DiagonalMatrix((DenseVector(diagonal) *^ constItem).items)
        case ConstDiagonalMatrix(value, width) =>
          ConstDiagonalMatrix(constItem * value, width)
        case _ => matrix *^^ self
      }
    }

    def average(implicit f: Fractional[T], m: RepMonoid[T]): Rep[T] = constItem
  }

  abstract class DiagonalMatrix[T](val diagonalValues: Rep[Collection[T]])
                                  (implicit val eT: Elem[T]) extends AbstractMatrix[T] {

    def numColumns: Rep[Int] = diagonalValues.length
    def numRows: Rep[Int] = numColumns
    def rmValues = SparseVectorBoxed(
      Collection.indexRange(numColumns).map(i => (numColumns * i + i, diagonalValues(i))),
      numColumns * numColumns).items
    def items = rmValues
    def constItem = zeroValue
    def replicatedRow: Vector[T] = ConstVector(zeroValue, numColumns) // TODO: create ZeroVector if it's introduced

    def columns: Rep[Collection[AbstractVector[T]]] = Collection.indexRange(numColumns).map { i =>
      SparseVector(Collection.replicate(1, i), diagonalValues.slice(i, 1), numColumns)
    }
    def rows: Coll[AbstractVector[T]] = Collection.indexRange(numColumns).map { i =>
      SparseVector(Collection.singleton(i), diagonalValues.slice(i, 1), numRows)
    }

    @OverloadId("rows")
    def apply(iRows: Coll[Int])(implicit o: Overloaded1): Matrix[T] = {
      DiagonalMatrix(iRows.map(i => diagonalValues(i)))
    }
    @OverloadId("row")
    def apply(row: Rep[Int]): Vector[T] = SparseVector(Collection.replicate(1, row), diagonalValues.slice(row, 1), numColumns)
    def apply(row: Rep[Int], column: Rep[Int]): Rep[T] = IF (row === column) THEN diagonalValues(row) ELSE eT.defaultRepValue

    def mapRowsBy[R: Elem](f: Rep[AbstractVector[T] => AbstractVector[R] @uncheckedVariance]): Matrix[R] = {
      DenseFlatMatrix.fromRows(rows.mapBy(f), numColumns)
    }

    def transpose(implicit n: Numeric[T]): Matrix[T] = self

    // TODO: inconsistent, no respect towards monoid operation over zero values, fix
    def reduceByColumns(implicit m: RepMonoid[T], n: Numeric[T]): Vector[T] = DenseVector(diagonalValues)
    def sumByRows(implicit n: Numeric[T]): Vector[T] = ???
    def sumByColumns(implicit n: Numeric[T]): Vector[T] = ???

    @OverloadId("matrix")
    def *(matrix: Matrix[T])(implicit n: Numeric[T], o: Overloaded1): Matrix[T] = {
      matrix match {
        case DenseFlatMatrix(rmValuesB, width) =>
          // TODO: check if there is excessive materialization in @diagonalReplicated
          val diagonalReplicated = diagonalValues.flatMap(v => Collection.replicate(width, v))
          DenseFlatMatrix((DenseVector(rmValuesB) *^ DenseVector(diagonalReplicated)).items, width)
        case CompoundMatrix(rowsB, width) =>
          CompoundMatrix((diagonalValues zip rowsB).map { case Pair(d, v) => v *^ d }, width)
        case ConstMatrix(value, width, _) =>
          val rowsConstant = diagonalValues.map(v => ConstVector(v * value, width))
          CompoundMatrix(rowsConstant, width)
        case DiagonalMatrix(diagonalValues1) =>
          DiagonalMatrix((DenseVector(diagonalValues) *^ DenseVector(diagonalValues1)).items)
        case ConstDiagonalMatrix(diagonalValue, _) =>
          DiagonalMatrix((DenseVector(diagonalValues) *^ diagonalValue).items)
        case _ => !!!("matcher for @matrix argument in DiagonalMatrix.*(matrix: Matrix[T]) is not specified.")
      }
    }

    @OverloadId("matrix")
    def +^^(matrix: Matrix[T])(implicit n: Numeric[T]): Matrix[T] = {
      matrix match {
        case DiagonalMatrix(diagonalValues1) =>
          DiagonalMatrix((DenseVector(diagonalValues) +^ DenseVector(diagonalValues1)).items)
        case ConstDiagonalMatrix(diagonalValue, _) =>
          DiagonalMatrix((DenseVector(diagonalValues) +^ diagonalValue).items)
        case _ => matrix +^^ self
      }
    }

    @OverloadId("matrix")
    def *^^(matrix: Matrix[T])(implicit n: Numeric[T]): Matrix[T] = {
      matrix match {
        case DiagonalMatrix(diagonalValues1) =>
          DiagonalMatrix((DenseVector(diagonalValues) *^ DenseVector(diagonalValues1)).items)
        case ConstDiagonalMatrix(diagonalValue, _) =>
          DiagonalMatrix((DenseVector(diagonalValues) *^ diagonalValue).items)
        case _ => matrix *^^ self
      }
    }

    def average(implicit f: Fractional[T], m: RepMonoid[T]): Rep[T] = {
      diagonalValues.reduce / diagonalValues.length.to[T]
    }
  }

  abstract class ConstDiagonalMatrix[T](val constItem: Rep[T], val numColumns: Rep[Int])
                                       (implicit val eT: Elem[T]) extends AbstractMatrix[T] {

    def numRows: Rep[Int] = numColumns
    def rmValues = SparseVectorBoxed(
      Collection.indexRange(numColumns).map(i => (numColumns * i + i, constItem)),
      numColumns * numColumns).items
    def items = rmValues
    def diagonalValues = Collection.replicate(numColumns, constItem)
    def replicatedRow: Vector[T] = ConstVector(zeroValue, numColumns) // TODO: create ZeroVector if it's introduced

    def rows: Coll[AbstractVector[T]] = Collection.indexRange(numColumns).map { i =>
      SparseVector(Collection.singleton(i), Collection.singleton(constItem), numColumns)
    }
    def columns = rows

    @OverloadId("rows")
    def apply(iRows: Coll[Int])(implicit o: Overloaded1): Matrix[T] = {
      CompoundMatrix(iRows.map(i => SparseVectorBoxed(Collection.singleton(Pair(i, constItem)), numColumns)), numColumns)
    }
    @OverloadId("row")
    def apply(row: Rep[Int]): Vector[T] = SparseVector(Collection.singleton(row), Collection.singleton(constItem), numColumns)
    def apply(row: Rep[Int], column: Rep[Int]): Rep[T] = IF (row === column) THEN constItem ELSE zeroValue

    def mapRowsBy[R: Elem](f: Rep[AbstractVector[T] => AbstractVector[R] @uncheckedVariance]): Matrix[R] = {
      CompoundMatrix(rows.mapBy(f), numColumns)
    }

    def transpose(implicit n: Numeric[T]): Matrix[T] = self

    def reduceByColumns(implicit m: RepMonoid[T], n: Numeric[T]): Vector[T] = ConstVector(constItem, numColumns)
    def sumByRows(implicit n: Numeric[T]): Vector[T] = ???
    def sumByColumns(implicit n: Numeric[T]): Vector[T] = ???

    @OverloadId("matrix")
    def *(matrix: Matrix[T])(implicit n: Numeric[T], o: Overloaded1): Matrix[T] = {
      matrix match {
        case DenseFlatMatrix(rmValuesB, width) =>
          DenseFlatMatrix((DenseVector(rmValuesB) *^ constItem).items, width)
        case CompoundMatrix(rowsB, width) =>
          CompoundMatrix(rowsB.map(v => v *^ constItem), width)
        case ConstMatrix(value, width, height) =>
          ConstMatrix(value * constItem, height, width)
        case DiagonalMatrix(diagonalValues1) =>
          DiagonalMatrix((DenseVector(diagonalValues1) *^ constItem).items)
        case ConstDiagonalMatrix(diagonalValue, width) =>
          ConstDiagonalMatrix(constItem * diagonalValue, width)
        case _ => !!!("matcher for @matrix argument in DiagonalMatrix.*(matrix: Matrix[T]) is not specified.")
      }
    }

    @OverloadId("matrix")
    def +^^(matrix: Matrix[T])(implicit n: Numeric[T]): Matrix[T] = {
      matrix match {
        case ConstDiagonalMatrix(diagonalValue, _) =>
          ConstDiagonalMatrix(constItem + diagonalValue, numColumns)
        case _ =>
          matrix +^^ self
      }
    }

    @OverloadId("matrix")
    def *^^(matrix: Matrix[T])(implicit n: Numeric[T]): Matrix[T] = {
      matrix match {
        case ConstDiagonalMatrix(diagonalValue, _) =>
          ConstDiagonalMatrix(constItem * diagonalValue, numColumns)
        case _ =>
          matrix *^^ self
      }
    }

    def average(implicit f: Fractional[T], m: RepMonoid[T]): Rep[T] = {
      diagonalValues.reduce / diagonalValues.length.to[T]
    }
  }

  trait AbstractMatrixCompanion extends TypeFamily1[AbstractMatrix]

  trait DenseFlatMatrixCompanion extends ConcreteClass1[DenseFlatMatrix] {
    def fromColumns[T: Elem](cols: Coll[AbstractVector[T]]): Matrix[T] = {
      val numColumns = cols.length
      val numRows = cols(0).length
      val columnsArr: Coll[Collection[T]] = cols.map(col => col.items)
      val rmValues = Collection.indexRange(numRows * numColumns).map { i =>
        columnsArr(i % numColumns)(i /! numColumns)
      }
      DenseFlatMatrix(rmValues, numColumns)
    }
    def fromNColl[T](items: NColl[(Int, T)], numColumns: Rep[Int])
                             (implicit elem: Elem[T], o: Overloaded1): Matrix[T] = ???
    @OverloadId("dense")
    def fromNColl[T](items: NColl[T], numColumns: Rep[Int])
                             (implicit elem: Elem[T], o: Overloaded2): Matrix[T] = {
      DenseFlatMatrix(items.flatMap { coll => coll }, numColumns)
    }
    def fromRows[T: Elem](rows: Coll[AbstractVector[T]], length: IntRep): Matrix[T] = {
      DenseFlatMatrix(rows.flatMap(v => v.convertTo[DenseVector[T]].items), length)
    }
  }

  trait CompoundMatrixCompanion extends ConcreteClass1[CompoundMatrix] {
    def fromColumns[T: Elem](cols: Coll[AbstractVector[T]]): Matrix[T] = ???
    def fromNColl[T](items: Coll[Collection[(Int, T)]], numColumns: Rep[Int])
                    (implicit elem: Elem[T], o: Overloaded1): Matrix[T] = {
      CompoundMatrix(items.map { coll => SparseVector(coll.as, coll.bs, numColumns) }, numColumns)
    }
    @OverloadId("dense")
    def fromNColl[T](items: Coll[Collection[T]], numColumns: Rep[Int])
                    (implicit elem: Elem[T], o: Overloaded2): Matrix[T] = {
      CompoundMatrix(items.map { coll => DenseVector(coll) }, numColumns)
    }
    def fromRows[T: Elem](rows: Coll[AbstractVector[T]], length: IntRep): Matrix[T] = {
      CompoundMatrix(rows, length)
    }
  }

  trait ConstMatrixCompanion extends ConcreteClass1[ConstMatrix] {
    def fromColumns[T: Elem](cols: Coll[AbstractVector[T]]): Matrix[T] = {
      val numColumns = cols.length
      val numRows = cols(0).length
      val item = cols(0)(0)
      ConstMatrix(item, numColumns, numRows)
    }
    def fromNColl[T](items: NColl[(Int, T)], numColumns: Rep[Int])
                             (implicit elem: Elem[T], o: Overloaded1): Matrix[T] = ???
    @OverloadId("dense")
    def fromNColl[T](items: NColl[T], numColumns: Rep[Int])
                             (implicit elem: Elem[T], o: Overloaded2): Matrix[T] = {
      val rmValues = items.flatMap { coll => coll }
      val numRows = rmValues.length /! numColumns
      val item = rmValues(0)
      ConstMatrix(item, numColumns, numRows)
    }
    def fromRows[T: Elem](rows: Coll[AbstractVector[T]], length: IntRep): Matrix[T] = {
      val numRows = rows.length
      val numColumns = rows(0).length
      val item = rows(0)(0)
      ConstMatrix(item, numColumns, numRows)
    }
  }

  trait DiagonalMatrixCompanion extends ConcreteClass1[DiagonalMatrix] {
    def fromColumns[T: Elem](cols: Coll[AbstractVector[T]]): Matrix[T] = ???
    def fromNColl[T](items: NColl[(Int, T)], numColumns: Rep[Int])
                             (implicit elem: Elem[T], o: Overloaded1): Matrix[T] = ???
    @OverloadId("dense")
    def fromNColl[T](items: NColl[T], numColumns: Rep[Int])
                             (implicit elem: Elem[T], o: Overloaded2): Matrix[T] = ???
    def fromRows[T: Elem](rows: Coll[AbstractVector[T]], length: IntRep): Matrix[T] = ???
  }
}

trait MatricesDsl extends impl.MatricesAbs { self: LADsl =>

  type MatrixCompanion = Rep[AbstractMatrixCompanion]

  implicit class MatrixExtensions[T](matrix: Matrix[T]) {
    implicit def eItem: Elem[T] = matrix.selfType1.asInstanceOf[AbstractMatrixElem[T, _]].eT

    //def map[R: Elem](f: Vector[T] => Vector[R]): Matrix[R] = matrix.mapBy(fun(f))

    //def filter(f: Rep[T] => Rep[Boolean]): Matrix[T] = matrix.filterBy(fun(f))

    //def flatMap[R: Elem](f: Rep[T] => Coll[R]): Matrix[R] = matrix.flatMapBy(fun(f))
  }

  def transposeDirect[T](m: Matrix[T])(implicit elem: Elem[T], n: Numeric[T]): Matrix[T] = {
    // TODO: inefficient
    val rows = m.rows
    val zero = elem.defaultRepValue
    val newNestedItems = for (i <- Collection.indexRange(m.numColumns)) yield {
      val items = Collection.indexRange(rows.length).map(j => Pair(j, rows(j)(i))).filter {
        p => p._2 !== zero //.nonZeroIndices.filter(l => l === i).length !== toRep(0)
      }
      /*val newRow: PairColl[Int, T] =
        indices zip indices.map { j =>
          val indices = rows(j).nonZeroIndices
          val values = rows(j).nonZeroValues
          val p = (indices zip Collection.indexRange(indices.length)).filter(l => l._1 === i)(toRep(0))
          values(p._2)
        }*/
      SparseVector(items.as, items.bs, m.numRows)
    }
    CompoundMatrix(newNestedItems, m.numRows)
  }
}

trait MatricesDslSeq extends impl.MatricesSeq { self: LADslSeq => }

trait MatricesDslExp extends impl.MatricesExp { self: LADslExp => }
