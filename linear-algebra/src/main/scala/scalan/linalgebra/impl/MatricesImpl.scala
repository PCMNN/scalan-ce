package scalan.linalgebra

import scalan._
import scalan.common.OverloadHack.{Overloaded1, Overloaded2, Overloaded3}
import scala.annotation.unchecked.uncheckedVariance
import scala.reflect.runtime.universe.{WeakTypeTag, weakTypeTag}
import scalan.meta.ScalanAst._

package impl {
// Abs -----------------------------------
trait MatricesAbs extends scalan.ScalanDsl with Matrices {
  self: LADsl =>

  // single proxy for each type family
  implicit def proxyMatrix[T](p: Rep[Matrix[T]]): Matrix[T] = {
    proxyOps[Matrix[T]](p)(scala.reflect.classTag[Matrix[T]])
  }

  // familyElem
  class MatrixElem[T, To <: Matrix[T]](implicit _eT: Elem[T])
    extends EntityElem[To] {
    def eT = _eT
    lazy val parent: Option[Elem[_]] = None
    lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map("T" -> Left(eT))
    }
    override def isEntityType = true
    override lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[Matrix[T]].asInstanceOf[WeakTypeTag[To]]
    }
    override def convert(x: Rep[Def[_]]) = {
      implicit val eTo: Elem[To] = this
      val conv = fun {x: Rep[Matrix[T]] => convertMatrix(x) }
      tryConvert(element[Matrix[T]], this, x, conv)
    }

    def convertMatrix(x: Rep[Matrix[T]]): Rep[To] = {
      x.selfType1 match {
        case _: MatrixElem[_, _] => x.asRep[To]
        case e => !!!(s"Expected $x to have MatrixElem[_, _], but got $e", x)
      }
    }

    override def getDefaultRep: Rep[To] = ???
  }

  implicit def matrixElement[T](implicit eT: Elem[T]): Elem[Matrix[T]] =
    cachedElem[MatrixElem[T, Matrix[T]]](eT)

  implicit case object MatrixCompanionElem extends CompanionElem[MatrixCompanionAbs] {
    lazy val tag = weakTypeTag[MatrixCompanionAbs]
    protected def getDefaultRep = Matrix
  }

  abstract class MatrixCompanionAbs extends CompanionDef[MatrixCompanionAbs] with MatrixCompanion {
    def selfType = MatrixCompanionElem
    override def toString = "Matrix"
  }
  def Matrix: Rep[MatrixCompanionAbs]
  implicit def proxyMatrixCompanionAbs(p: Rep[MatrixCompanionAbs]): MatrixCompanionAbs =
    proxyOps[MatrixCompanionAbs](p)

  abstract class AbsDenseFlatMatrix[T]
      (rmFlatValues: Rep[Collection[T]], numColumns: Rep[Int])(implicit eT: Elem[T])
    extends DenseFlatMatrix[T](rmFlatValues, numColumns) with Def[DenseFlatMatrix[T]] {
    lazy val selfType = element[DenseFlatMatrix[T]]
  }
  // elem for concrete class
  class DenseFlatMatrixElem[T](val iso: Iso[DenseFlatMatrixData[T], DenseFlatMatrix[T]])(implicit override val eT: Elem[T])
    extends MatrixElem[T, DenseFlatMatrix[T]]
    with ConcreteElem[DenseFlatMatrixData[T], DenseFlatMatrix[T]] {
    override lazy val parent: Option[Elem[_]] = Some(matrixElement(element[T]))
    override lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map("T" -> Left(eT))
    }

    override def convertMatrix(x: Rep[Matrix[T]]) = DenseFlatMatrix(x.rmFlatValues, x.numColumns)
    override def getDefaultRep = DenseFlatMatrix(element[Collection[T]].defaultRepValue, 0)
    override lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[DenseFlatMatrix[T]]
    }
  }

  // state representation type
  type DenseFlatMatrixData[T] = (Collection[T], Int)

  // 3) Iso for concrete class
  class DenseFlatMatrixIso[T](implicit eT: Elem[T])
    extends EntityIso[DenseFlatMatrixData[T], DenseFlatMatrix[T]] with Def[DenseFlatMatrixIso[T]] {
    override def from(p: Rep[DenseFlatMatrix[T]]) =
      (p.rmFlatValues, p.numColumns)
    override def to(p: Rep[(Collection[T], Int)]) = {
      val Pair(rmFlatValues, numColumns) = p
      DenseFlatMatrix(rmFlatValues, numColumns)
    }
    lazy val eFrom = pairElement(element[Collection[T]], element[Int])
    lazy val eTo = new DenseFlatMatrixElem[T](self)
    lazy val selfType = new DenseFlatMatrixIsoElem[T](eT)
    def productArity = 1
    def productElement(n: Int) = eT
  }
  case class DenseFlatMatrixIsoElem[T](eT: Elem[T]) extends Elem[DenseFlatMatrixIso[T]] {
    def isEntityType = true
    def getDefaultRep = reifyObject(new DenseFlatMatrixIso[T]()(eT))
    lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[DenseFlatMatrixIso[T]]
    }
  }
  // 4) constructor and deconstructor
  class DenseFlatMatrixCompanionAbs extends CompanionDef[DenseFlatMatrixCompanionAbs] with DenseFlatMatrixCompanion {
    def selfType = DenseFlatMatrixCompanionElem
    override def toString = "DenseFlatMatrix"
    @scalan.OverloadId("fromData")
    def apply[T](p: Rep[DenseFlatMatrixData[T]])(implicit eT: Elem[T]): Rep[DenseFlatMatrix[T]] =
      isoDenseFlatMatrix(eT).to(p)
    @scalan.OverloadId("fromFields")
    def apply[T](rmFlatValues: Rep[Collection[T]], numColumns: Rep[Int])(implicit eT: Elem[T]): Rep[DenseFlatMatrix[T]] =
      mkDenseFlatMatrix(rmFlatValues, numColumns)

    def unapply[T](p: Rep[Matrix[T]]) = unmkDenseFlatMatrix(p)
  }
  lazy val DenseFlatMatrixRep: Rep[DenseFlatMatrixCompanionAbs] = new DenseFlatMatrixCompanionAbs
  lazy val DenseFlatMatrix: DenseFlatMatrixCompanionAbs = proxyDenseFlatMatrixCompanion(DenseFlatMatrixRep)
  implicit def proxyDenseFlatMatrixCompanion(p: Rep[DenseFlatMatrixCompanionAbs]): DenseFlatMatrixCompanionAbs = {
    proxyOps[DenseFlatMatrixCompanionAbs](p)
  }

  implicit case object DenseFlatMatrixCompanionElem extends CompanionElem[DenseFlatMatrixCompanionAbs] {
    lazy val tag = weakTypeTag[DenseFlatMatrixCompanionAbs]
    protected def getDefaultRep = DenseFlatMatrix
  }

  implicit def proxyDenseFlatMatrix[T](p: Rep[DenseFlatMatrix[T]]): DenseFlatMatrix[T] =
    proxyOps[DenseFlatMatrix[T]](p)

  implicit class ExtendedDenseFlatMatrix[T](p: Rep[DenseFlatMatrix[T]])(implicit eT: Elem[T]) {
    def toData: Rep[DenseFlatMatrixData[T]] = isoDenseFlatMatrix(eT).from(p)
  }

  // 5) implicit resolution of Iso
  implicit def isoDenseFlatMatrix[T](implicit eT: Elem[T]): Iso[DenseFlatMatrixData[T], DenseFlatMatrix[T]] =
    reifyObject(new DenseFlatMatrixIso[T]()(eT))

  // 6) smart constructor and deconstructor
  def mkDenseFlatMatrix[T](rmFlatValues: Rep[Collection[T]], numColumns: Rep[Int])(implicit eT: Elem[T]): Rep[DenseFlatMatrix[T]]
  def unmkDenseFlatMatrix[T](p: Rep[Matrix[T]]): Option[(Rep[Collection[T]], Rep[Int])]

  abstract class AbsCompoundMatrix[T]
      (rows: Rep[Collection[Vector[T]]], numColumns: Rep[Int])(implicit eT: Elem[T])
    extends CompoundMatrix[T](rows, numColumns) with Def[CompoundMatrix[T]] {
    lazy val selfType = element[CompoundMatrix[T]]
  }
  // elem for concrete class
  class CompoundMatrixElem[T](val iso: Iso[CompoundMatrixData[T], CompoundMatrix[T]])(implicit override val eT: Elem[T])
    extends MatrixElem[T, CompoundMatrix[T]]
    with ConcreteElem[CompoundMatrixData[T], CompoundMatrix[T]] {
    override lazy val parent: Option[Elem[_]] = Some(matrixElement(element[T]))
    override lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map("T" -> Left(eT))
    }

    override def convertMatrix(x: Rep[Matrix[T]]) = CompoundMatrix(x.rows, x.numColumns)
    override def getDefaultRep = CompoundMatrix(element[Collection[Vector[T]]].defaultRepValue, 0)
    override lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[CompoundMatrix[T]]
    }
  }

  // state representation type
  type CompoundMatrixData[T] = (Collection[Vector[T]], Int)

  // 3) Iso for concrete class
  class CompoundMatrixIso[T](implicit eT: Elem[T])
    extends EntityIso[CompoundMatrixData[T], CompoundMatrix[T]] with Def[CompoundMatrixIso[T]] {
    override def from(p: Rep[CompoundMatrix[T]]) =
      (p.rows, p.numColumns)
    override def to(p: Rep[(Collection[Vector[T]], Int)]) = {
      val Pair(rows, numColumns) = p
      CompoundMatrix(rows, numColumns)
    }
    lazy val eFrom = pairElement(element[Collection[Vector[T]]], element[Int])
    lazy val eTo = new CompoundMatrixElem[T](self)
    lazy val selfType = new CompoundMatrixIsoElem[T](eT)
    def productArity = 1
    def productElement(n: Int) = eT
  }
  case class CompoundMatrixIsoElem[T](eT: Elem[T]) extends Elem[CompoundMatrixIso[T]] {
    def isEntityType = true
    def getDefaultRep = reifyObject(new CompoundMatrixIso[T]()(eT))
    lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[CompoundMatrixIso[T]]
    }
  }
  // 4) constructor and deconstructor
  class CompoundMatrixCompanionAbs extends CompanionDef[CompoundMatrixCompanionAbs] with CompoundMatrixCompanion {
    def selfType = CompoundMatrixCompanionElem
    override def toString = "CompoundMatrix"
    @scalan.OverloadId("fromData")
    def apply[T](p: Rep[CompoundMatrixData[T]])(implicit eT: Elem[T]): Rep[CompoundMatrix[T]] =
      isoCompoundMatrix(eT).to(p)
    @scalan.OverloadId("fromFields")
    def apply[T](rows: Rep[Collection[Vector[T]]], numColumns: Rep[Int])(implicit eT: Elem[T]): Rep[CompoundMatrix[T]] =
      mkCompoundMatrix(rows, numColumns)

    def unapply[T](p: Rep[Matrix[T]]) = unmkCompoundMatrix(p)
  }
  lazy val CompoundMatrixRep: Rep[CompoundMatrixCompanionAbs] = new CompoundMatrixCompanionAbs
  lazy val CompoundMatrix: CompoundMatrixCompanionAbs = proxyCompoundMatrixCompanion(CompoundMatrixRep)
  implicit def proxyCompoundMatrixCompanion(p: Rep[CompoundMatrixCompanionAbs]): CompoundMatrixCompanionAbs = {
    proxyOps[CompoundMatrixCompanionAbs](p)
  }

  implicit case object CompoundMatrixCompanionElem extends CompanionElem[CompoundMatrixCompanionAbs] {
    lazy val tag = weakTypeTag[CompoundMatrixCompanionAbs]
    protected def getDefaultRep = CompoundMatrix
  }

  implicit def proxyCompoundMatrix[T](p: Rep[CompoundMatrix[T]]): CompoundMatrix[T] =
    proxyOps[CompoundMatrix[T]](p)

  implicit class ExtendedCompoundMatrix[T](p: Rep[CompoundMatrix[T]])(implicit eT: Elem[T]) {
    def toData: Rep[CompoundMatrixData[T]] = isoCompoundMatrix(eT).from(p)
  }

  // 5) implicit resolution of Iso
  implicit def isoCompoundMatrix[T](implicit eT: Elem[T]): Iso[CompoundMatrixData[T], CompoundMatrix[T]] =
    reifyObject(new CompoundMatrixIso[T]()(eT))

  // 6) smart constructor and deconstructor
  def mkCompoundMatrix[T](rows: Rep[Collection[Vector[T]]], numColumns: Rep[Int])(implicit eT: Elem[T]): Rep[CompoundMatrix[T]]
  def unmkCompoundMatrix[T](p: Rep[Matrix[T]]): Option[(Rep[Collection[Vector[T]]], Rep[Int])]

  abstract class AbsConstMatrix[T]
      (constItem: Rep[T], numColumns: Rep[Int], numRows: Rep[Int])(implicit eT: Elem[T])
    extends ConstMatrix[T](constItem, numColumns, numRows) with Def[ConstMatrix[T]] {
    lazy val selfType = element[ConstMatrix[T]]
  }
  // elem for concrete class
  class ConstMatrixElem[T](val iso: Iso[ConstMatrixData[T], ConstMatrix[T]])(implicit override val eT: Elem[T])
    extends MatrixElem[T, ConstMatrix[T]]
    with ConcreteElem[ConstMatrixData[T], ConstMatrix[T]] {
    override lazy val parent: Option[Elem[_]] = Some(matrixElement(element[T]))
    override lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map("T" -> Left(eT))
    }

    override def convertMatrix(x: Rep[Matrix[T]]) = // Converter is not generated by meta
!!!("Cannot convert from Matrix to ConstMatrix: missing fields List(constItem)")
    override def getDefaultRep = ConstMatrix(element[T].defaultRepValue, 0, 0)
    override lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[ConstMatrix[T]]
    }
  }

  // state representation type
  type ConstMatrixData[T] = (T, (Int, Int))

  // 3) Iso for concrete class
  class ConstMatrixIso[T](implicit eT: Elem[T])
    extends EntityIso[ConstMatrixData[T], ConstMatrix[T]] with Def[ConstMatrixIso[T]] {
    override def from(p: Rep[ConstMatrix[T]]) =
      (p.constItem, p.numColumns, p.numRows)
    override def to(p: Rep[(T, (Int, Int))]) = {
      val Pair(constItem, Pair(numColumns, numRows)) = p
      ConstMatrix(constItem, numColumns, numRows)
    }
    lazy val eFrom = pairElement(element[T], pairElement(element[Int], element[Int]))
    lazy val eTo = new ConstMatrixElem[T](self)
    lazy val selfType = new ConstMatrixIsoElem[T](eT)
    def productArity = 1
    def productElement(n: Int) = eT
  }
  case class ConstMatrixIsoElem[T](eT: Elem[T]) extends Elem[ConstMatrixIso[T]] {
    def isEntityType = true
    def getDefaultRep = reifyObject(new ConstMatrixIso[T]()(eT))
    lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[ConstMatrixIso[T]]
    }
  }
  // 4) constructor and deconstructor
  class ConstMatrixCompanionAbs extends CompanionDef[ConstMatrixCompanionAbs] with ConstMatrixCompanion {
    def selfType = ConstMatrixCompanionElem
    override def toString = "ConstMatrix"
    @scalan.OverloadId("fromData")
    def apply[T](p: Rep[ConstMatrixData[T]])(implicit eT: Elem[T]): Rep[ConstMatrix[T]] =
      isoConstMatrix(eT).to(p)
    @scalan.OverloadId("fromFields")
    def apply[T](constItem: Rep[T], numColumns: Rep[Int], numRows: Rep[Int])(implicit eT: Elem[T]): Rep[ConstMatrix[T]] =
      mkConstMatrix(constItem, numColumns, numRows)

    def unapply[T](p: Rep[Matrix[T]]) = unmkConstMatrix(p)
  }
  lazy val ConstMatrixRep: Rep[ConstMatrixCompanionAbs] = new ConstMatrixCompanionAbs
  lazy val ConstMatrix: ConstMatrixCompanionAbs = proxyConstMatrixCompanion(ConstMatrixRep)
  implicit def proxyConstMatrixCompanion(p: Rep[ConstMatrixCompanionAbs]): ConstMatrixCompanionAbs = {
    proxyOps[ConstMatrixCompanionAbs](p)
  }

  implicit case object ConstMatrixCompanionElem extends CompanionElem[ConstMatrixCompanionAbs] {
    lazy val tag = weakTypeTag[ConstMatrixCompanionAbs]
    protected def getDefaultRep = ConstMatrix
  }

  implicit def proxyConstMatrix[T](p: Rep[ConstMatrix[T]]): ConstMatrix[T] =
    proxyOps[ConstMatrix[T]](p)

  implicit class ExtendedConstMatrix[T](p: Rep[ConstMatrix[T]])(implicit eT: Elem[T]) {
    def toData: Rep[ConstMatrixData[T]] = isoConstMatrix(eT).from(p)
  }

  // 5) implicit resolution of Iso
  implicit def isoConstMatrix[T](implicit eT: Elem[T]): Iso[ConstMatrixData[T], ConstMatrix[T]] =
    reifyObject(new ConstMatrixIso[T]()(eT))

  // 6) smart constructor and deconstructor
  def mkConstMatrix[T](constItem: Rep[T], numColumns: Rep[Int], numRows: Rep[Int])(implicit eT: Elem[T]): Rep[ConstMatrix[T]]
  def unmkConstMatrix[T](p: Rep[Matrix[T]]): Option[(Rep[T], Rep[Int], Rep[Int])]

  abstract class AbsDiagonalMatrix[T]
      (mainDiagonal: Rep[Collection[T]])(implicit eT: Elem[T])
    extends DiagonalMatrix[T](mainDiagonal) with Def[DiagonalMatrix[T]] {
    lazy val selfType = element[DiagonalMatrix[T]]
  }
  // elem for concrete class
  class DiagonalMatrixElem[T](val iso: Iso[DiagonalMatrixData[T], DiagonalMatrix[T]])(implicit override val eT: Elem[T])
    extends MatrixElem[T, DiagonalMatrix[T]]
    with ConcreteElem[DiagonalMatrixData[T], DiagonalMatrix[T]] {
    override lazy val parent: Option[Elem[_]] = Some(matrixElement(element[T]))
    override lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map("T" -> Left(eT))
    }

    override def convertMatrix(x: Rep[Matrix[T]]) = DiagonalMatrix(x.mainDiagonal)
    override def getDefaultRep = DiagonalMatrix(element[Collection[T]].defaultRepValue)
    override lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[DiagonalMatrix[T]]
    }
  }

  // state representation type
  type DiagonalMatrixData[T] = Collection[T]

  // 3) Iso for concrete class
  class DiagonalMatrixIso[T](implicit eT: Elem[T])
    extends EntityIso[DiagonalMatrixData[T], DiagonalMatrix[T]] with Def[DiagonalMatrixIso[T]] {
    override def from(p: Rep[DiagonalMatrix[T]]) =
      p.mainDiagonal
    override def to(p: Rep[Collection[T]]) = {
      val mainDiagonal = p
      DiagonalMatrix(mainDiagonal)
    }
    lazy val eFrom = element[Collection[T]]
    lazy val eTo = new DiagonalMatrixElem[T](self)
    lazy val selfType = new DiagonalMatrixIsoElem[T](eT)
    def productArity = 1
    def productElement(n: Int) = eT
  }
  case class DiagonalMatrixIsoElem[T](eT: Elem[T]) extends Elem[DiagonalMatrixIso[T]] {
    def isEntityType = true
    def getDefaultRep = reifyObject(new DiagonalMatrixIso[T]()(eT))
    lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[DiagonalMatrixIso[T]]
    }
  }
  // 4) constructor and deconstructor
  class DiagonalMatrixCompanionAbs extends CompanionDef[DiagonalMatrixCompanionAbs] with DiagonalMatrixCompanion {
    def selfType = DiagonalMatrixCompanionElem
    override def toString = "DiagonalMatrix"

    @scalan.OverloadId("fromFields")
    def apply[T](mainDiagonal: Rep[Collection[T]])(implicit eT: Elem[T]): Rep[DiagonalMatrix[T]] =
      mkDiagonalMatrix(mainDiagonal)

    def unapply[T](p: Rep[Matrix[T]]) = unmkDiagonalMatrix(p)
  }
  lazy val DiagonalMatrixRep: Rep[DiagonalMatrixCompanionAbs] = new DiagonalMatrixCompanionAbs
  lazy val DiagonalMatrix: DiagonalMatrixCompanionAbs = proxyDiagonalMatrixCompanion(DiagonalMatrixRep)
  implicit def proxyDiagonalMatrixCompanion(p: Rep[DiagonalMatrixCompanionAbs]): DiagonalMatrixCompanionAbs = {
    proxyOps[DiagonalMatrixCompanionAbs](p)
  }

  implicit case object DiagonalMatrixCompanionElem extends CompanionElem[DiagonalMatrixCompanionAbs] {
    lazy val tag = weakTypeTag[DiagonalMatrixCompanionAbs]
    protected def getDefaultRep = DiagonalMatrix
  }

  implicit def proxyDiagonalMatrix[T](p: Rep[DiagonalMatrix[T]]): DiagonalMatrix[T] =
    proxyOps[DiagonalMatrix[T]](p)

  implicit class ExtendedDiagonalMatrix[T](p: Rep[DiagonalMatrix[T]])(implicit eT: Elem[T]) {
    def toData: Rep[DiagonalMatrixData[T]] = isoDiagonalMatrix(eT).from(p)
  }

  // 5) implicit resolution of Iso
  implicit def isoDiagonalMatrix[T](implicit eT: Elem[T]): Iso[DiagonalMatrixData[T], DiagonalMatrix[T]] =
    reifyObject(new DiagonalMatrixIso[T]()(eT))

  // 6) smart constructor and deconstructor
  def mkDiagonalMatrix[T](mainDiagonal: Rep[Collection[T]])(implicit eT: Elem[T]): Rep[DiagonalMatrix[T]]
  def unmkDiagonalMatrix[T](p: Rep[Matrix[T]]): Option[(Rep[Collection[T]])]

  abstract class AbsConstDiagonalMatrix[T]
      (constItem: Rep[T], numColumns: Rep[Int])(implicit eT: Elem[T])
    extends ConstDiagonalMatrix[T](constItem, numColumns) with Def[ConstDiagonalMatrix[T]] {
    lazy val selfType = element[ConstDiagonalMatrix[T]]
  }
  // elem for concrete class
  class ConstDiagonalMatrixElem[T](val iso: Iso[ConstDiagonalMatrixData[T], ConstDiagonalMatrix[T]])(implicit override val eT: Elem[T])
    extends MatrixElem[T, ConstDiagonalMatrix[T]]
    with ConcreteElem[ConstDiagonalMatrixData[T], ConstDiagonalMatrix[T]] {
    override lazy val parent: Option[Elem[_]] = Some(matrixElement(element[T]))
    override lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map("T" -> Left(eT))
    }

    override def convertMatrix(x: Rep[Matrix[T]]) = // Converter is not generated by meta
!!!("Cannot convert from Matrix to ConstDiagonalMatrix: missing fields List(constItem)")
    override def getDefaultRep = ConstDiagonalMatrix(element[T].defaultRepValue, 0)
    override lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[ConstDiagonalMatrix[T]]
    }
  }

  // state representation type
  type ConstDiagonalMatrixData[T] = (T, Int)

  // 3) Iso for concrete class
  class ConstDiagonalMatrixIso[T](implicit eT: Elem[T])
    extends EntityIso[ConstDiagonalMatrixData[T], ConstDiagonalMatrix[T]] with Def[ConstDiagonalMatrixIso[T]] {
    override def from(p: Rep[ConstDiagonalMatrix[T]]) =
      (p.constItem, p.numColumns)
    override def to(p: Rep[(T, Int)]) = {
      val Pair(constItem, numColumns) = p
      ConstDiagonalMatrix(constItem, numColumns)
    }
    lazy val eFrom = pairElement(element[T], element[Int])
    lazy val eTo = new ConstDiagonalMatrixElem[T](self)
    lazy val selfType = new ConstDiagonalMatrixIsoElem[T](eT)
    def productArity = 1
    def productElement(n: Int) = eT
  }
  case class ConstDiagonalMatrixIsoElem[T](eT: Elem[T]) extends Elem[ConstDiagonalMatrixIso[T]] {
    def isEntityType = true
    def getDefaultRep = reifyObject(new ConstDiagonalMatrixIso[T]()(eT))
    lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[ConstDiagonalMatrixIso[T]]
    }
  }
  // 4) constructor and deconstructor
  class ConstDiagonalMatrixCompanionAbs extends CompanionDef[ConstDiagonalMatrixCompanionAbs] {
    def selfType = ConstDiagonalMatrixCompanionElem
    override def toString = "ConstDiagonalMatrix"
    @scalan.OverloadId("fromData")
    def apply[T](p: Rep[ConstDiagonalMatrixData[T]])(implicit eT: Elem[T]): Rep[ConstDiagonalMatrix[T]] =
      isoConstDiagonalMatrix(eT).to(p)
    @scalan.OverloadId("fromFields")
    def apply[T](constItem: Rep[T], numColumns: Rep[Int])(implicit eT: Elem[T]): Rep[ConstDiagonalMatrix[T]] =
      mkConstDiagonalMatrix(constItem, numColumns)

    def unapply[T](p: Rep[Matrix[T]]) = unmkConstDiagonalMatrix(p)
  }
  lazy val ConstDiagonalMatrixRep: Rep[ConstDiagonalMatrixCompanionAbs] = new ConstDiagonalMatrixCompanionAbs
  lazy val ConstDiagonalMatrix: ConstDiagonalMatrixCompanionAbs = proxyConstDiagonalMatrixCompanion(ConstDiagonalMatrixRep)
  implicit def proxyConstDiagonalMatrixCompanion(p: Rep[ConstDiagonalMatrixCompanionAbs]): ConstDiagonalMatrixCompanionAbs = {
    proxyOps[ConstDiagonalMatrixCompanionAbs](p)
  }

  implicit case object ConstDiagonalMatrixCompanionElem extends CompanionElem[ConstDiagonalMatrixCompanionAbs] {
    lazy val tag = weakTypeTag[ConstDiagonalMatrixCompanionAbs]
    protected def getDefaultRep = ConstDiagonalMatrix
  }

  implicit def proxyConstDiagonalMatrix[T](p: Rep[ConstDiagonalMatrix[T]]): ConstDiagonalMatrix[T] =
    proxyOps[ConstDiagonalMatrix[T]](p)

  implicit class ExtendedConstDiagonalMatrix[T](p: Rep[ConstDiagonalMatrix[T]])(implicit eT: Elem[T]) {
    def toData: Rep[ConstDiagonalMatrixData[T]] = isoConstDiagonalMatrix(eT).from(p)
  }

  // 5) implicit resolution of Iso
  implicit def isoConstDiagonalMatrix[T](implicit eT: Elem[T]): Iso[ConstDiagonalMatrixData[T], ConstDiagonalMatrix[T]] =
    reifyObject(new ConstDiagonalMatrixIso[T]()(eT))

  // 6) smart constructor and deconstructor
  def mkConstDiagonalMatrix[T](constItem: Rep[T], numColumns: Rep[Int])(implicit eT: Elem[T]): Rep[ConstDiagonalMatrix[T]]
  def unmkConstDiagonalMatrix[T](p: Rep[Matrix[T]]): Option[(Rep[T], Rep[Int])]

  registerModule(Matrices_Module)
}

// Std -----------------------------------
trait MatricesStd extends scalan.ScalanDslStd with MatricesDsl {
  self: LADslStd =>
  lazy val Matrix: Rep[MatrixCompanionAbs] = new MatrixCompanionAbs {
  }

  case class StdDenseFlatMatrix[T]
      (override val rmFlatValues: Rep[Collection[T]], override val numColumns: Rep[Int])(implicit eT: Elem[T])
    extends AbsDenseFlatMatrix[T](rmFlatValues, numColumns) {
  }

  def mkDenseFlatMatrix[T]
    (rmFlatValues: Rep[Collection[T]], numColumns: Rep[Int])(implicit eT: Elem[T]): Rep[DenseFlatMatrix[T]] =
    new StdDenseFlatMatrix[T](rmFlatValues, numColumns)
  def unmkDenseFlatMatrix[T](p: Rep[Matrix[T]]) = p match {
    case p: DenseFlatMatrix[T] @unchecked =>
      Some((p.rmFlatValues, p.numColumns))
    case _ => None
  }

  case class StdCompoundMatrix[T]
      (override val rows: Rep[Collection[Vector[T]]], override val numColumns: Rep[Int])(implicit eT: Elem[T])
    extends AbsCompoundMatrix[T](rows, numColumns) {
  }

  def mkCompoundMatrix[T]
    (rows: Rep[Collection[Vector[T]]], numColumns: Rep[Int])(implicit eT: Elem[T]): Rep[CompoundMatrix[T]] =
    new StdCompoundMatrix[T](rows, numColumns)
  def unmkCompoundMatrix[T](p: Rep[Matrix[T]]) = p match {
    case p: CompoundMatrix[T] @unchecked =>
      Some((p.rows, p.numColumns))
    case _ => None
  }

  case class StdConstMatrix[T]
      (override val constItem: Rep[T], override val numColumns: Rep[Int], override val numRows: Rep[Int])(implicit eT: Elem[T])
    extends AbsConstMatrix[T](constItem, numColumns, numRows) {
  }

  def mkConstMatrix[T]
    (constItem: Rep[T], numColumns: Rep[Int], numRows: Rep[Int])(implicit eT: Elem[T]): Rep[ConstMatrix[T]] =
    new StdConstMatrix[T](constItem, numColumns, numRows)
  def unmkConstMatrix[T](p: Rep[Matrix[T]]) = p match {
    case p: ConstMatrix[T] @unchecked =>
      Some((p.constItem, p.numColumns, p.numRows))
    case _ => None
  }

  case class StdDiagonalMatrix[T]
      (override val mainDiagonal: Rep[Collection[T]])(implicit eT: Elem[T])
    extends AbsDiagonalMatrix[T](mainDiagonal) {
  }

  def mkDiagonalMatrix[T]
    (mainDiagonal: Rep[Collection[T]])(implicit eT: Elem[T]): Rep[DiagonalMatrix[T]] =
    new StdDiagonalMatrix[T](mainDiagonal)
  def unmkDiagonalMatrix[T](p: Rep[Matrix[T]]) = p match {
    case p: DiagonalMatrix[T] @unchecked =>
      Some((p.mainDiagonal))
    case _ => None
  }

  case class StdConstDiagonalMatrix[T]
      (override val constItem: Rep[T], override val numColumns: Rep[Int])(implicit eT: Elem[T])
    extends AbsConstDiagonalMatrix[T](constItem, numColumns) {
  }

  def mkConstDiagonalMatrix[T]
    (constItem: Rep[T], numColumns: Rep[Int])(implicit eT: Elem[T]): Rep[ConstDiagonalMatrix[T]] =
    new StdConstDiagonalMatrix[T](constItem, numColumns)
  def unmkConstDiagonalMatrix[T](p: Rep[Matrix[T]]) = p match {
    case p: ConstDiagonalMatrix[T] @unchecked =>
      Some((p.constItem, p.numColumns))
    case _ => None
  }
}

// Exp -----------------------------------
trait MatricesExp extends scalan.ScalanDslExp with MatricesDsl {
  self: LADslExp =>
  lazy val Matrix: Rep[MatrixCompanionAbs] = new MatrixCompanionAbs {
  }

  case class ExpDenseFlatMatrix[T]
      (override val rmFlatValues: Rep[Collection[T]], override val numColumns: Rep[Int])(implicit eT: Elem[T])
    extends AbsDenseFlatMatrix[T](rmFlatValues, numColumns)

  object DenseFlatMatrixMethods {
    object numRows {
      def unapply(d: Def[_]): Option[Rep[DenseFlatMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "numRows" =>
          Some(receiver).asInstanceOf[Option[Rep[DenseFlatMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[DenseFlatMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object columns {
      def unapply(d: Def[_]): Option[Rep[DenseFlatMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "columns" =>
          Some(receiver).asInstanceOf[Option[Rep[DenseFlatMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[DenseFlatMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object rows {
      def unapply(d: Def[_]): Option[Rep[DenseFlatMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "rows" =>
          Some(receiver).asInstanceOf[Option[Rep[DenseFlatMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[DenseFlatMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object mainDiagonal {
      def unapply(d: Def[_]): Option[Rep[DenseFlatMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "mainDiagonal" =>
          Some(receiver).asInstanceOf[Option[Rep[DenseFlatMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[DenseFlatMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object replicatedRow {
      def unapply(d: Def[_]): Option[Rep[DenseFlatMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "replicatedRow" =>
          Some(receiver).asInstanceOf[Option[Rep[DenseFlatMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[DenseFlatMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_rows {
      def unapply(d: Def[_]): Option[(Rep[DenseFlatMatrix[T]], Coll[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(iRows, _*), _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "rows" } =>
          Some((receiver, iRows)).asInstanceOf[Option[(Rep[DenseFlatMatrix[T]], Coll[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseFlatMatrix[T]], Coll[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_row {
      def unapply(d: Def[_]): Option[(Rep[DenseFlatMatrix[T]], Rep[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(row, _*), _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "row" } =>
          Some((receiver, row)).asInstanceOf[Option[(Rep[DenseFlatMatrix[T]], Rep[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseFlatMatrix[T]], Rep[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply {
      def unapply(d: Def[_]): Option[(Rep[DenseFlatMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(row, column, _*), _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "apply" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, row, column)).asInstanceOf[Option[(Rep[DenseFlatMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseFlatMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object mapRowsBy {
      def unapply(d: Def[_]): Option[(Rep[DenseFlatMatrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}] = d match {
        case MethodCall(receiver, method, Seq(f, _*), _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "mapRowsBy" =>
          Some((receiver, f)).asInstanceOf[Option[(Rep[DenseFlatMatrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseFlatMatrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object fromCellIndex {
      def unapply(d: Def[_]): Option[(Rep[DenseFlatMatrix[T]], Rep[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(iCell, _*), _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "fromCellIndex" =>
          Some((receiver, iCell)).asInstanceOf[Option[(Rep[DenseFlatMatrix[T]], Rep[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseFlatMatrix[T]], Rep[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object toCellIndex {
      def unapply(d: Def[_]): Option[(Rep[DenseFlatMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(iRow, iCol, _*), _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "toCellIndex" =>
          Some((receiver, iRow, iCol)).asInstanceOf[Option[(Rep[DenseFlatMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseFlatMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object transpose_block_size {
      def unapply(d: Def[_]): Option[(Rep[DenseFlatMatrix[T]], Rep[Int], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(blockSize, n, _*), _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "transpose" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "block_size" } =>
          Some((receiver, blockSize, n)).asInstanceOf[Option[(Rep[DenseFlatMatrix[T]], Rep[Int], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseFlatMatrix[T]], Rep[Int], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object transpose {
      def unapply(d: Def[_]): Option[(Rep[DenseFlatMatrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "transpose" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[DenseFlatMatrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseFlatMatrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object reduceByColumns {
      def unapply(d: Def[_]): Option[(Rep[DenseFlatMatrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(m, n, _*), _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "reduceByColumns" =>
          Some((receiver, m, n)).asInstanceOf[Option[(Rep[DenseFlatMatrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseFlatMatrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sumByRows {
      def unapply(d: Def[_]): Option[(Rep[DenseFlatMatrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "sumByRows" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[DenseFlatMatrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseFlatMatrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sumByColumns {
      def unapply(d: Def[_]): Option[(Rep[DenseFlatMatrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "sumByColumns" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[DenseFlatMatrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseFlatMatrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_* {
      def unapply(d: Def[_]): Option[(Rep[DenseFlatMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "$times" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[DenseFlatMatrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseFlatMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_+^^ {
      def unapply(d: Def[_]): Option[(Rep[DenseFlatMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "$plus$up$up" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[DenseFlatMatrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseFlatMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_*^^ {
      def unapply(d: Def[_]): Option[(Rep[DenseFlatMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "$times$up$up" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[DenseFlatMatrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseFlatMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object average {
      def unapply(d: Def[_]): Option[(Rep[DenseFlatMatrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(f, m, _*), _) if receiver.elem.isInstanceOf[DenseFlatMatrixElem[_]] && method.getName == "average" =>
          Some((receiver, f, m)).asInstanceOf[Option[(Rep[DenseFlatMatrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseFlatMatrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  object DenseFlatMatrixCompanionMethods {
    object fromRows {
      def unapply(d: Def[_]): Option[(Coll[Vector[T]], IntRep) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(rows, length, _*), _) if receiver.elem == DenseFlatMatrixCompanionElem && method.getName == "fromRows" =>
          Some((rows, length)).asInstanceOf[Option[(Coll[Vector[T]], IntRep) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Coll[Vector[T]], IntRep) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object fromColumns {
      def unapply(d: Def[_]): Option[Coll[Vector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(cols, _*), _) if receiver.elem == DenseFlatMatrixCompanionElem && method.getName == "fromColumns" =>
          Some(cols).asInstanceOf[Option[Coll[Vector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Coll[Vector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object fromNColl_dense {
      def unapply(d: Def[_]): Option[(NColl[T], Rep[Int], Elem[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(items, numColumns, elem, _*), _) if receiver.elem == DenseFlatMatrixCompanionElem && method.getName == "fromNColl" =>
          Some((items, numColumns, elem)).asInstanceOf[Option[(NColl[T], Rep[Int], Elem[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(NColl[T], Rep[Int], Elem[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  def mkDenseFlatMatrix[T]
    (rmFlatValues: Rep[Collection[T]], numColumns: Rep[Int])(implicit eT: Elem[T]): Rep[DenseFlatMatrix[T]] =
    new ExpDenseFlatMatrix[T](rmFlatValues, numColumns)
  def unmkDenseFlatMatrix[T](p: Rep[Matrix[T]]) = p.elem.asInstanceOf[Elem[_]] match {
    case _: DenseFlatMatrixElem[T] @unchecked =>
      Some((p.asRep[DenseFlatMatrix[T]].rmFlatValues, p.asRep[DenseFlatMatrix[T]].numColumns))
    case _ =>
      None
  }

  case class ExpCompoundMatrix[T]
      (override val rows: Rep[Collection[Vector[T]]], override val numColumns: Rep[Int])(implicit eT: Elem[T])
    extends AbsCompoundMatrix[T](rows, numColumns)

  object CompoundMatrixMethods {
    object columns {
      def unapply(d: Def[_]): Option[Rep[CompoundMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[CompoundMatrixElem[_]] && method.getName == "columns" =>
          Some(receiver).asInstanceOf[Option[Rep[CompoundMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[CompoundMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object numRows {
      def unapply(d: Def[_]): Option[Rep[CompoundMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[CompoundMatrixElem[_]] && method.getName == "numRows" =>
          Some(receiver).asInstanceOf[Option[Rep[CompoundMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[CompoundMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object rmFlatValues {
      def unapply(d: Def[_]): Option[Rep[CompoundMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[CompoundMatrixElem[_]] && method.getName == "rmFlatValues" =>
          Some(receiver).asInstanceOf[Option[Rep[CompoundMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[CompoundMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object mainDiagonal {
      def unapply(d: Def[_]): Option[Rep[CompoundMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[CompoundMatrixElem[_]] && method.getName == "mainDiagonal" =>
          Some(receiver).asInstanceOf[Option[Rep[CompoundMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[CompoundMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object replicatedRow {
      def unapply(d: Def[_]): Option[Rep[CompoundMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[CompoundMatrixElem[_]] && method.getName == "replicatedRow" =>
          Some(receiver).asInstanceOf[Option[Rep[CompoundMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[CompoundMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_rows {
      def unapply(d: Def[_]): Option[(Rep[CompoundMatrix[T]], Coll[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(iRows, _*), _) if receiver.elem.isInstanceOf[CompoundMatrixElem[_]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "rows" } =>
          Some((receiver, iRows)).asInstanceOf[Option[(Rep[CompoundMatrix[T]], Coll[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[CompoundMatrix[T]], Coll[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_row {
      def unapply(d: Def[_]): Option[(Rep[CompoundMatrix[T]], Rep[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(row, _*), _) if receiver.elem.isInstanceOf[CompoundMatrixElem[_]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "row" } =>
          Some((receiver, row)).asInstanceOf[Option[(Rep[CompoundMatrix[T]], Rep[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[CompoundMatrix[T]], Rep[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply {
      def unapply(d: Def[_]): Option[(Rep[CompoundMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(row, column, _*), _) if receiver.elem.isInstanceOf[CompoundMatrixElem[_]] && method.getName == "apply" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, row, column)).asInstanceOf[Option[(Rep[CompoundMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[CompoundMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object mapRowsBy {
      def unapply(d: Def[_]): Option[(Rep[CompoundMatrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}] = d match {
        case MethodCall(receiver, method, Seq(f, _*), _) if receiver.elem.isInstanceOf[CompoundMatrixElem[_]] && method.getName == "mapRowsBy" =>
          Some((receiver, f)).asInstanceOf[Option[(Rep[CompoundMatrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[CompoundMatrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object transpose {
      def unapply(d: Def[_]): Option[(Rep[CompoundMatrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[CompoundMatrixElem[_]] && method.getName == "transpose" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[CompoundMatrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[CompoundMatrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object reduceByColumns {
      def unapply(d: Def[_]): Option[(Rep[CompoundMatrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(m, n, _*), _) if receiver.elem.isInstanceOf[CompoundMatrixElem[_]] && method.getName == "reduceByColumns" =>
          Some((receiver, m, n)).asInstanceOf[Option[(Rep[CompoundMatrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[CompoundMatrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sumByRows {
      def unapply(d: Def[_]): Option[(Rep[CompoundMatrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[CompoundMatrixElem[_]] && method.getName == "sumByRows" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[CompoundMatrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[CompoundMatrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sumByColumns {
      def unapply(d: Def[_]): Option[(Rep[CompoundMatrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[CompoundMatrixElem[_]] && method.getName == "sumByColumns" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[CompoundMatrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[CompoundMatrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_* {
      def unapply(d: Def[_]): Option[(Rep[CompoundMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[CompoundMatrixElem[_]] && method.getName == "$times" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[CompoundMatrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[CompoundMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_+^^ {
      def unapply(d: Def[_]): Option[(Rep[CompoundMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[CompoundMatrixElem[_]] && method.getName == "$plus$up$up" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[CompoundMatrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[CompoundMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_*^^ {
      def unapply(d: Def[_]): Option[(Rep[CompoundMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[CompoundMatrixElem[_]] && method.getName == "$times$up$up" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[CompoundMatrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[CompoundMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object average {
      def unapply(d: Def[_]): Option[(Rep[CompoundMatrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(f, m, _*), _) if receiver.elem.isInstanceOf[CompoundMatrixElem[_]] && method.getName == "average" =>
          Some((receiver, f, m)).asInstanceOf[Option[(Rep[CompoundMatrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[CompoundMatrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  object CompoundMatrixCompanionMethods {
    object fromNColl {
      def unapply(d: Def[_]): Option[(NColl[(Int, T)], Rep[Int], Elem[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(items, numColumns, elem, _*), _) if receiver.elem == CompoundMatrixCompanionElem && method.getName == "fromNColl" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((items, numColumns, elem)).asInstanceOf[Option[(NColl[(Int, T)], Rep[Int], Elem[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(NColl[(Int, T)], Rep[Int], Elem[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object fromNColl_dense1 {
      def unapply(d: Def[_]): Option[(NColl[T], Rep[Int], Elem[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(items, numColumns, elem, _*), _) if receiver.elem == CompoundMatrixCompanionElem && method.getName == "fromNColl" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "dense1" } =>
          Some((items, numColumns, elem)).asInstanceOf[Option[(NColl[T], Rep[Int], Elem[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(NColl[T], Rep[Int], Elem[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object fromNColl_dense2 {
      def unapply(d: Def[_]): Option[(NColl[T], Elem[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(items, elem, _*), _) if receiver.elem == CompoundMatrixCompanionElem && method.getName == "fromNColl" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "dense2" } =>
          Some((items, elem)).asInstanceOf[Option[(NColl[T], Elem[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(NColl[T], Elem[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object fromRows {
      def unapply(d: Def[_]): Option[(Coll[Vector[T]], IntRep) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(rows, numCols, _*), _) if receiver.elem == CompoundMatrixCompanionElem && method.getName == "fromRows" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((rows, numCols)).asInstanceOf[Option[(Coll[Vector[T]], IntRep) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Coll[Vector[T]], IntRep) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object fromRows_fromRowsNoLength {
      def unapply(d: Def[_]): Option[Coll[Vector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(rows, _*), _) if receiver.elem == CompoundMatrixCompanionElem && method.getName == "fromRows" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "fromRowsNoLength" } =>
          Some(rows).asInstanceOf[Option[Coll[Vector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Coll[Vector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  def mkCompoundMatrix[T]
    (rows: Rep[Collection[Vector[T]]], numColumns: Rep[Int])(implicit eT: Elem[T]): Rep[CompoundMatrix[T]] =
    new ExpCompoundMatrix[T](rows, numColumns)
  def unmkCompoundMatrix[T](p: Rep[Matrix[T]]) = p.elem.asInstanceOf[Elem[_]] match {
    case _: CompoundMatrixElem[T] @unchecked =>
      Some((p.asRep[CompoundMatrix[T]].rows, p.asRep[CompoundMatrix[T]].numColumns))
    case _ =>
      None
  }

  case class ExpConstMatrix[T]
      (override val constItem: Rep[T], override val numColumns: Rep[Int], override val numRows: Rep[Int])(implicit eT: Elem[T])
    extends AbsConstMatrix[T](constItem, numColumns, numRows)

  object ConstMatrixMethods {
    object rmFlatValues {
      def unapply(d: Def[_]): Option[Rep[ConstMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "rmFlatValues" =>
          Some(receiver).asInstanceOf[Option[Rep[ConstMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ConstMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object items {
      def unapply(d: Def[_]): Option[Rep[ConstMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "items" =>
          Some(receiver).asInstanceOf[Option[Rep[ConstMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ConstMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object columns {
      def unapply(d: Def[_]): Option[Rep[ConstMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "columns" =>
          Some(receiver).asInstanceOf[Option[Rep[ConstMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ConstMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object rows {
      def unapply(d: Def[_]): Option[Rep[ConstMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "rows" =>
          Some(receiver).asInstanceOf[Option[Rep[ConstMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ConstMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object mainDiagonal {
      def unapply(d: Def[_]): Option[Rep[ConstMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "mainDiagonal" =>
          Some(receiver).asInstanceOf[Option[Rep[ConstMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ConstMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object replicatedRow {
      def unapply(d: Def[_]): Option[Rep[ConstMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "replicatedRow" =>
          Some(receiver).asInstanceOf[Option[Rep[ConstMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ConstMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_rows {
      def unapply(d: Def[_]): Option[(Rep[ConstMatrix[T]], Coll[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(iRows, _*), _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "rows" } =>
          Some((receiver, iRows)).asInstanceOf[Option[(Rep[ConstMatrix[T]], Coll[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstMatrix[T]], Coll[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_row {
      def unapply(d: Def[_]): Option[(Rep[ConstMatrix[T]], Rep[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(row, _*), _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "row" } =>
          Some((receiver, row)).asInstanceOf[Option[(Rep[ConstMatrix[T]], Rep[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstMatrix[T]], Rep[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply {
      def unapply(d: Def[_]): Option[(Rep[ConstMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(row, column, _*), _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "apply" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, row, column)).asInstanceOf[Option[(Rep[ConstMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object mapRowsBy {
      def unapply(d: Def[_]): Option[(Rep[ConstMatrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}] = d match {
        case MethodCall(receiver, method, Seq(f, _*), _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "mapRowsBy" =>
          Some((receiver, f)).asInstanceOf[Option[(Rep[ConstMatrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstMatrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object transpose {
      def unapply(d: Def[_]): Option[(Rep[ConstMatrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "transpose" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[ConstMatrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstMatrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object reduceByColumns {
      def unapply(d: Def[_]): Option[(Rep[ConstMatrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(m, n, _*), _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "reduceByColumns" =>
          Some((receiver, m, n)).asInstanceOf[Option[(Rep[ConstMatrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstMatrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sumByRows {
      def unapply(d: Def[_]): Option[(Rep[ConstMatrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "sumByRows" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[ConstMatrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstMatrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sumByColumns {
      def unapply(d: Def[_]): Option[(Rep[ConstMatrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "sumByColumns" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[ConstMatrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstMatrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object countNonZeroesByColumns {
      def unapply(d: Def[_]): Option[(Rep[ConstMatrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "countNonZeroesByColumns" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[ConstMatrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstMatrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object * {
      def unapply(d: Def[_]): Option[(Rep[ConstMatrix[T]], Vec[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "$times" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[ConstMatrix[T]], Vec[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstMatrix[T]], Vec[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_* {
      def unapply(d: Def[_]): Option[(Rep[ConstMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "$times" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "matrix" } =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[ConstMatrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_+^^ {
      def unapply(d: Def[_]): Option[(Rep[ConstMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "$plus$up$up" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[ConstMatrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_*^^ {
      def unapply(d: Def[_]): Option[(Rep[ConstMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "$times$up$up" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[ConstMatrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object average {
      def unapply(d: Def[_]): Option[(Rep[ConstMatrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(f, m, _*), _) if receiver.elem.isInstanceOf[ConstMatrixElem[_]] && method.getName == "average" =>
          Some((receiver, f, m)).asInstanceOf[Option[(Rep[ConstMatrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstMatrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  object ConstMatrixCompanionMethods {
  }

  def mkConstMatrix[T]
    (constItem: Rep[T], numColumns: Rep[Int], numRows: Rep[Int])(implicit eT: Elem[T]): Rep[ConstMatrix[T]] =
    new ExpConstMatrix[T](constItem, numColumns, numRows)
  def unmkConstMatrix[T](p: Rep[Matrix[T]]) = p.elem.asInstanceOf[Elem[_]] match {
    case _: ConstMatrixElem[T] @unchecked =>
      Some((p.asRep[ConstMatrix[T]].constItem, p.asRep[ConstMatrix[T]].numColumns, p.asRep[ConstMatrix[T]].numRows))
    case _ =>
      None
  }

  case class ExpDiagonalMatrix[T]
      (override val mainDiagonal: Rep[Collection[T]])(implicit eT: Elem[T])
    extends AbsDiagonalMatrix[T](mainDiagonal)

  object DiagonalMatrixMethods {
    object numColumns {
      def unapply(d: Def[_]): Option[Rep[DiagonalMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "numColumns" =>
          Some(receiver).asInstanceOf[Option[Rep[DiagonalMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[DiagonalMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object numRows {
      def unapply(d: Def[_]): Option[Rep[DiagonalMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "numRows" =>
          Some(receiver).asInstanceOf[Option[Rep[DiagonalMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[DiagonalMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object rmFlatValues {
      def unapply(d: Def[_]): Option[Rep[DiagonalMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "rmFlatValues" =>
          Some(receiver).asInstanceOf[Option[Rep[DiagonalMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[DiagonalMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object items {
      def unapply(d: Def[_]): Option[Rep[DiagonalMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "items" =>
          Some(receiver).asInstanceOf[Option[Rep[DiagonalMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[DiagonalMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object replicatedRow {
      def unapply(d: Def[_]): Option[Rep[DiagonalMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "replicatedRow" =>
          Some(receiver).asInstanceOf[Option[Rep[DiagonalMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[DiagonalMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object columns {
      def unapply(d: Def[_]): Option[Rep[DiagonalMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "columns" =>
          Some(receiver).asInstanceOf[Option[Rep[DiagonalMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[DiagonalMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object rows {
      def unapply(d: Def[_]): Option[Rep[DiagonalMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "rows" =>
          Some(receiver).asInstanceOf[Option[Rep[DiagonalMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[DiagonalMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_rows {
      def unapply(d: Def[_]): Option[(Rep[DiagonalMatrix[T]], Coll[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(iRows, _*), _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "rows" } =>
          Some((receiver, iRows)).asInstanceOf[Option[(Rep[DiagonalMatrix[T]], Coll[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DiagonalMatrix[T]], Coll[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_row {
      def unapply(d: Def[_]): Option[(Rep[DiagonalMatrix[T]], Rep[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(row, _*), _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "row" } =>
          Some((receiver, row)).asInstanceOf[Option[(Rep[DiagonalMatrix[T]], Rep[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DiagonalMatrix[T]], Rep[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply {
      def unapply(d: Def[_]): Option[(Rep[DiagonalMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(row, column, _*), _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "apply" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, row, column)).asInstanceOf[Option[(Rep[DiagonalMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DiagonalMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object mapRowsBy {
      def unapply(d: Def[_]): Option[(Rep[DiagonalMatrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}] = d match {
        case MethodCall(receiver, method, Seq(f, _*), _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "mapRowsBy" =>
          Some((receiver, f)).asInstanceOf[Option[(Rep[DiagonalMatrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DiagonalMatrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object transpose {
      def unapply(d: Def[_]): Option[(Rep[DiagonalMatrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "transpose" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[DiagonalMatrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DiagonalMatrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object reduceByColumns {
      def unapply(d: Def[_]): Option[(Rep[DiagonalMatrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(m, n, _*), _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "reduceByColumns" =>
          Some((receiver, m, n)).asInstanceOf[Option[(Rep[DiagonalMatrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DiagonalMatrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sumByRows {
      def unapply(d: Def[_]): Option[(Rep[DiagonalMatrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "sumByRows" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[DiagonalMatrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DiagonalMatrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sumByColumns {
      def unapply(d: Def[_]): Option[(Rep[DiagonalMatrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "sumByColumns" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[DiagonalMatrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DiagonalMatrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_* {
      def unapply(d: Def[_]): Option[(Rep[DiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "$times" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[DiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_+^^ {
      def unapply(d: Def[_]): Option[(Rep[DiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "$plus$up$up" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[DiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_*^^ {
      def unapply(d: Def[_]): Option[(Rep[DiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "$times$up$up" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[DiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object average {
      def unapply(d: Def[_]): Option[(Rep[DiagonalMatrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(f, m, _*), _) if receiver.elem.isInstanceOf[DiagonalMatrixElem[_]] && method.getName == "average" =>
          Some((receiver, f, m)).asInstanceOf[Option[(Rep[DiagonalMatrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DiagonalMatrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  object DiagonalMatrixCompanionMethods {
  }

  def mkDiagonalMatrix[T]
    (mainDiagonal: Rep[Collection[T]])(implicit eT: Elem[T]): Rep[DiagonalMatrix[T]] =
    new ExpDiagonalMatrix[T](mainDiagonal)
  def unmkDiagonalMatrix[T](p: Rep[Matrix[T]]) = p.elem.asInstanceOf[Elem[_]] match {
    case _: DiagonalMatrixElem[T] @unchecked =>
      Some((p.asRep[DiagonalMatrix[T]].mainDiagonal))
    case _ =>
      None
  }

  case class ExpConstDiagonalMatrix[T]
      (override val constItem: Rep[T], override val numColumns: Rep[Int])(implicit eT: Elem[T])
    extends AbsConstDiagonalMatrix[T](constItem, numColumns)

  object ConstDiagonalMatrixMethods {
    object numRows {
      def unapply(d: Def[_]): Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "numRows" =>
          Some(receiver).asInstanceOf[Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object rmFlatValues {
      def unapply(d: Def[_]): Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "rmFlatValues" =>
          Some(receiver).asInstanceOf[Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object items {
      def unapply(d: Def[_]): Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "items" =>
          Some(receiver).asInstanceOf[Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object mainDiagonal {
      def unapply(d: Def[_]): Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "mainDiagonal" =>
          Some(receiver).asInstanceOf[Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object replicatedRow {
      def unapply(d: Def[_]): Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "replicatedRow" =>
          Some(receiver).asInstanceOf[Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object rows {
      def unapply(d: Def[_]): Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "rows" =>
          Some(receiver).asInstanceOf[Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object columns {
      def unapply(d: Def[_]): Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "columns" =>
          Some(receiver).asInstanceOf[Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ConstDiagonalMatrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_rows {
      def unapply(d: Def[_]): Option[(Rep[ConstDiagonalMatrix[T]], Coll[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(iRows, _*), _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "rows" } =>
          Some((receiver, iRows)).asInstanceOf[Option[(Rep[ConstDiagonalMatrix[T]], Coll[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstDiagonalMatrix[T]], Coll[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_row {
      def unapply(d: Def[_]): Option[(Rep[ConstDiagonalMatrix[T]], Rep[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(row, _*), _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "row" } =>
          Some((receiver, row)).asInstanceOf[Option[(Rep[ConstDiagonalMatrix[T]], Rep[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstDiagonalMatrix[T]], Rep[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply {
      def unapply(d: Def[_]): Option[(Rep[ConstDiagonalMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(row, column, _*), _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "apply" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, row, column)).asInstanceOf[Option[(Rep[ConstDiagonalMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstDiagonalMatrix[T]], Rep[Int], Rep[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object mapRowsBy {
      def unapply(d: Def[_]): Option[(Rep[ConstDiagonalMatrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}] = d match {
        case MethodCall(receiver, method, Seq(f, _*), _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "mapRowsBy" =>
          Some((receiver, f)).asInstanceOf[Option[(Rep[ConstDiagonalMatrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstDiagonalMatrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object transpose {
      def unapply(d: Def[_]): Option[(Rep[ConstDiagonalMatrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "transpose" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[ConstDiagonalMatrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstDiagonalMatrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object reduceByColumns {
      def unapply(d: Def[_]): Option[(Rep[ConstDiagonalMatrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(m, n, _*), _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "reduceByColumns" =>
          Some((receiver, m, n)).asInstanceOf[Option[(Rep[ConstDiagonalMatrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstDiagonalMatrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sumByRows {
      def unapply(d: Def[_]): Option[(Rep[ConstDiagonalMatrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "sumByRows" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[ConstDiagonalMatrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstDiagonalMatrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sumByColumns {
      def unapply(d: Def[_]): Option[(Rep[ConstDiagonalMatrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "sumByColumns" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[ConstDiagonalMatrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstDiagonalMatrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_* {
      def unapply(d: Def[_]): Option[(Rep[ConstDiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "$times" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[ConstDiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstDiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_+^^ {
      def unapply(d: Def[_]): Option[(Rep[ConstDiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "$plus$up$up" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[ConstDiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstDiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_*^^ {
      def unapply(d: Def[_]): Option[(Rep[ConstDiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "$times$up$up" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[ConstDiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstDiagonalMatrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object average {
      def unapply(d: Def[_]): Option[(Rep[ConstDiagonalMatrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(f, m, _*), _) if receiver.elem.isInstanceOf[ConstDiagonalMatrixElem[_]] && method.getName == "average" =>
          Some((receiver, f, m)).asInstanceOf[Option[(Rep[ConstDiagonalMatrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstDiagonalMatrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  def mkConstDiagonalMatrix[T]
    (constItem: Rep[T], numColumns: Rep[Int])(implicit eT: Elem[T]): Rep[ConstDiagonalMatrix[T]] =
    new ExpConstDiagonalMatrix[T](constItem, numColumns)
  def unmkConstDiagonalMatrix[T](p: Rep[Matrix[T]]) = p.elem.asInstanceOf[Elem[_]] match {
    case _: ConstDiagonalMatrixElem[T] @unchecked =>
      Some((p.asRep[ConstDiagonalMatrix[T]].constItem, p.asRep[ConstDiagonalMatrix[T]].numColumns))
    case _ =>
      None
  }

  object MatrixMethods {
    object numColumns {
      def unapply(d: Def[_]): Option[Rep[Matrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "numColumns" =>
          Some(receiver).asInstanceOf[Option[Rep[Matrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[Matrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object numRows {
      def unapply(d: Def[_]): Option[Rep[Matrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "numRows" =>
          Some(receiver).asInstanceOf[Option[Rep[Matrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[Matrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object rows {
      def unapply(d: Def[_]): Option[Rep[Matrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "rows" =>
          Some(receiver).asInstanceOf[Option[Rep[Matrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[Matrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object columns {
      def unapply(d: Def[_]): Option[Rep[Matrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "columns" =>
          Some(receiver).asInstanceOf[Option[Rep[Matrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[Matrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object rmFlatValues {
      def unapply(d: Def[_]): Option[Rep[Matrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "rmFlatValues" =>
          Some(receiver).asInstanceOf[Option[Rep[Matrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[Matrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object zeroValue {
      def unapply(d: Def[_]): Option[Rep[Matrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "zeroValue" =>
          Some(receiver).asInstanceOf[Option[Rep[Matrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[Matrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object mainDiagonal {
      def unapply(d: Def[_]): Option[Rep[Matrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "mainDiagonal" =>
          Some(receiver).asInstanceOf[Option[Rep[Matrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[Matrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object replicatedRow {
      def unapply(d: Def[_]): Option[Rep[Matrix[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "replicatedRow" =>
          Some(receiver).asInstanceOf[Option[Rep[Matrix[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[Matrix[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_rowsByVector {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], Vec[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "rowsByVector" } =>
          Some((receiver, vector)).asInstanceOf[Option[(Rep[Matrix[T]], Vec[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], Vec[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_rows {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], Coll[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(iRows, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "rows" } =>
          Some((receiver, iRows)).asInstanceOf[Option[(Rep[Matrix[T]], Coll[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], Coll[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_row {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], Rep[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(row, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "row" } =>
          Some((receiver, row)).asInstanceOf[Option[(Rep[Matrix[T]], Rep[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], Rep[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], Rep[Int], Rep[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(row, column, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "apply" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, row, column)).asInstanceOf[Option[(Rep[Matrix[T]], Rep[Int], Rep[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], Rep[Int], Rep[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object mapRowsBy {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}] = d match {
        case MethodCall(receiver, method, Seq(f, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "mapRowsBy" =>
          Some((receiver, f)).asInstanceOf[Option[(Rep[Matrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], Rep[Vector[T] => Vector[R] @uncheckedVariance]) forSome {type T; type R}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object transpose {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "transpose" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[Matrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object reduceByRows {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], RepMonoid[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(m, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "reduceByRows" =>
          Some((receiver, m)).asInstanceOf[Option[(Rep[Matrix[T]], RepMonoid[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], RepMonoid[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object reduceByColumns {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(m, n, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "reduceByColumns" =>
          Some((receiver, m, n)).asInstanceOf[Option[(Rep[Matrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], RepMonoid[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sumByRows {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "sumByRows" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[Matrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sumByColumns {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "sumByColumns" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[Matrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object countNonZeroesByColumns {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "countNonZeroesByColumns" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[Matrix[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object + {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "$plus" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[Matrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_* {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "$times" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "matrix" } =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[Matrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object * {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], Vec[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "$times" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[Matrix[T]], Vec[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], Vec[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_+^^ {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "$plus$up$up" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "matrix" } =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[Matrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object +^^ {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], Rep[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(value, n, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "$plus$up$up" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, value, n)).asInstanceOf[Option[(Rep[Matrix[T]], Rep[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], Rep[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object matrix_*^^ {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], Matr[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "$times$up$up" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "matrix" } =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[Matrix[T]], Matr[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], Matr[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object *^^ {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], Rep[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(value, n, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "$times$up$up" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, value, n)).asInstanceOf[Option[(Rep[Matrix[T]], Rep[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], Rep[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object average {
      def unapply(d: Def[_]): Option[(Rep[Matrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(f, m, _*), _) if receiver.elem.isInstanceOf[MatrixElem[_, _]] && method.getName == "average" =>
          Some((receiver, f, m)).asInstanceOf[Option[(Rep[Matrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Matrix[T]], Fractional[T], RepMonoid[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  object MatrixCompanionMethods {
  }
}

object Matrices_Module extends scalan.ModuleInfo {
  val dump = "H4sIAAAAAAAAAM1YTWwbRRSeteM4tqOkvxAkIkIwIBCNUxAqUg5VsBMIcpMoGypkKtB4PXG3zM4uO+Ngc+ixB7ghrhwqIXHpBfXAAdQLQkIcOCGExIkDp9Kq6qE9IBBvZn+86+wmxIQoPox2Z+a9973vfW889o07KMdd9Aw3MMVsziICz+nqeZGLsr7EhCl6F+xWh5Ia2frti1duzma/+iaDJhto9DLmNU4bqOA9LHWd8FkXrToqYGYQLmyXC/RkXUWoGDalxBCmzSqmZXUEblJSqZtcLNTRSNNu9d5HV5FWR8cMmxkuEUSvUsw54f78GJGIzPC9oN57a04/BqvILCqRLDZdbAqADzGOefs3iKP3mM16lkATPrQ1R8KCPXnTcmxXBCHy4O6y3QpeRxiGCXSifgVv4wqEaFd04ZqsDZYlBxvv4TZZhS1y+wgA5oRubfYc9Z6toyIXLSBoxXKomuk6CCGowIsKxFyfn7mQnznJT1knromp+SGWi+uu3e0h76NlEeo64OKFPVwEHsgSa5U/umS8/VAvWRlp3JVQ8irDUXD0RIoaVCmAx+83PuH3X7t+LoOKDVQ0+WKTCxcbIlpyn60SZswWCnNIIHbbUK3ZtGqpKIuwZ0ASBcO2HMzAk0/lONSJmoYp5GY5N+5XJ4X6vHBIsFXrOlqY70xKvko3VUzp+u3Hzjz9x9JbGZSJhyiASx2E7wZOBRq9gEEOXd+5HCcF0jYVw3IodPtjfpfgIQ3P3r7b+m4eXcqE5Pmx/l29wEWO//Jz6afnzmfQWEOpe5nidgP440uUWGtu1WaigcbsbeJ6K/ltTOVTYv3yLbKFO1T4rEbpyAIdAs2k9qFDJFcLSvNaQEDJk+2qzUh5eb38QP/h0xtSlS4a91a8xvzbPPfXrxNbQglWoHHXAoTiIqYdwgOas9DXceKL1bAb9qyIWpoKoclhGjywjgVOOhZLCuOip9LE45B117TgsNomL3/79Zv3bq3mlH5O+Pwp6N7R4dPXp1JmqM1DpBUmkkRT9JjRbYscn71vvnP9Y6HkoXXjJ9Na8wokv6DsHt9FKcEJ+eW1a6fvff7uSdXZY01TWNgpz++jr4M2/B/7FsULOVH1vymU2s/GFydrhHEiheJ1ZUoXyvF0uOZVHiowNWBdjSYyHTGNBJ3SBvSTIZsBmhHZbnvKMBn1dCi46XTBAUuPbNRP0Tvnb2VQ7g2U24Im5nWUa9od1groh69WQbri1WBOi9MPdGMXWyHd6jOD+jkPoFYbS1o8r/2dgjtIHGzCEdf+YJguH70Is75q94Ix1AEghzPJCc2r8aX9yHVCKkyWZRi1Pho3PiyxJmCejpi9fiT0A2cQ42JF+BklimgnqKGlkGydB+uNRB0frIpKVZnsMBI6FbE8LP0Moj164hm3sMlqJm7bDNODuWocxFkRIBrqrIgbH9pZsRPz0Sv3IZ8VEWx9Pg6a+JOqyf4r+5F0RxMFm4Ur5PC1SdHsLg1SkrfEZWyZtHc2Me7+umIytRucmMdhWJPjn/09/sYx5VRerdFx/1pHTahQmzRd7CfuotmUG5/u35OB9asPP1t9/sebv6tfGEV544afUyz8DyP6yyJOVK6+WOM0AhdEJe/fCuo//wU6dB4SAAA="
}
}

