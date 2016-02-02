package scalan.linalgebra

import scalan._
import scalan.collections.{CollectionsDsl, CollectionsDslSeq, CollectionsDslExp}
import scalan.common.OverloadHack.{Overloaded2, Overloaded1}
import scala.annotation.unchecked.uncheckedVariance
import scala.reflect.runtime.universe.{WeakTypeTag, weakTypeTag}
import scalan.meta.ScalanAst._

package impl {
// Abs -----------------------------------
trait VectorsAbs extends scalan.ScalanDsl with Vectors {
  self: LADsl =>

  // single proxy for each type family
  implicit def proxyAbstractVector[T](p: Rep[AbstractVector[T]]): AbstractVector[T] = {
    proxyOps[AbstractVector[T]](p)(scala.reflect.classTag[AbstractVector[T]])
  }

  // familyElem
  class AbstractVectorElem[T, To <: AbstractVector[T]](implicit _eT: Elem[T])
    extends EntityElem[To] {
    def eT = _eT
    lazy val parent: Option[Elem[_]] = None
    lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map("T" -> Left(eT))
    }
    override def isEntityType = true
    override lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[AbstractVector[T]].asInstanceOf[WeakTypeTag[To]]
    }
    override def convert(x: Rep[Def[_]]) = {
      implicit val eTo: Elem[To] = this
      val conv = fun {x: Rep[AbstractVector[T]] => convertAbstractVector(x) }
      tryConvert(element[AbstractVector[T]], this, x, conv)
    }

    def convertAbstractVector(x: Rep[AbstractVector[T]]): Rep[To] = {
      x.selfType1 match {
        case _: AbstractVectorElem[_, _] => x.asRep[To]
        case e => !!!(s"Expected $x to have AbstractVectorElem[_, _], but got $e", x)
      }
    }

    override def getDefaultRep: Rep[To] = ???
  }

  implicit def abstractVectorElement[T](implicit eT: Elem[T]): Elem[AbstractVector[T]] =
    cachedElem[AbstractVectorElem[T, AbstractVector[T]]](eT)

  implicit case object AbstractVectorCompanionElem extends CompanionElem[AbstractVectorCompanionAbs] {
    lazy val tag = weakTypeTag[AbstractVectorCompanionAbs]
    protected def getDefaultRep = AbstractVector
  }

  abstract class AbstractVectorCompanionAbs extends CompanionDef[AbstractVectorCompanionAbs] with AbstractVectorCompanion {
    def selfType = AbstractVectorCompanionElem
    override def toString = "AbstractVector"
  }
  def AbstractVector: Rep[AbstractVectorCompanionAbs]
  implicit def proxyAbstractVectorCompanionAbs(p: Rep[AbstractVectorCompanionAbs]): AbstractVectorCompanionAbs =
    proxyOps[AbstractVectorCompanionAbs](p)

  abstract class AbsDenseVector[T]
      (items: Coll[T])(implicit eT: Elem[T])
    extends DenseVector[T](items) with Def[DenseVector[T]] {
    lazy val selfType = element[DenseVector[T]]
  }
  // elem for concrete class
  class DenseVectorElem[T](val iso: Iso[DenseVectorData[T], DenseVector[T]])(implicit override val eT: Elem[T])
    extends AbstractVectorElem[T, DenseVector[T]]
    with ConcreteElem[DenseVectorData[T], DenseVector[T]] {
    override lazy val parent: Option[Elem[_]] = Some(abstractVectorElement(element[T]))
    override lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map("T" -> Left(eT))
    }

    override def convertAbstractVector(x: Rep[AbstractVector[T]]) = DenseVector(x.items)
    override def getDefaultRep = DenseVector(element[Collection[T]].defaultRepValue)
    override lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[DenseVector[T]]
    }
  }

  // state representation type
  type DenseVectorData[T] = Collection[T]

  // 3) Iso for concrete class
  class DenseVectorIso[T](implicit eT: Elem[T])
    extends EntityIso[DenseVectorData[T], DenseVector[T]] with Def[DenseVectorIso[T]] {
    override def from(p: Rep[DenseVector[T]]) =
      p.items
    override def to(p: Rep[Collection[T]]) = {
      val items = p
      DenseVector(items)
    }
    lazy val eFrom = element[Collection[T]]
    lazy val eTo = new DenseVectorElem[T](self)
    lazy val selfType = new DenseVectorIsoElem[T](eT)
    def productArity = 1
    def productElement(n: Int) = eT
  }
  case class DenseVectorIsoElem[T](eT: Elem[T]) extends Elem[DenseVectorIso[T]] {
    def isEntityType = true
    def getDefaultRep = reifyObject(new DenseVectorIso[T]()(eT))
    lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[DenseVectorIso[T]]
    }
  }
  // 4) constructor and deconstructor
  class DenseVectorCompanionAbs extends CompanionDef[DenseVectorCompanionAbs] with DenseVectorCompanion {
    def selfType = DenseVectorCompanionElem
    override def toString = "DenseVector"

    def apply[T](items: Coll[T])(implicit eT: Elem[T]): Rep[DenseVector[T]] =
      mkDenseVector(items)
  }
  object DenseVectorMatcher {
    def unapply[T](p: Rep[AbstractVector[T]]) = unmkDenseVector(p)
  }
  lazy val DenseVector: Rep[DenseVectorCompanionAbs] = new DenseVectorCompanionAbs
  implicit def proxyDenseVectorCompanion(p: Rep[DenseVectorCompanionAbs]): DenseVectorCompanionAbs = {
    proxyOps[DenseVectorCompanionAbs](p)
  }

  implicit case object DenseVectorCompanionElem extends CompanionElem[DenseVectorCompanionAbs] {
    lazy val tag = weakTypeTag[DenseVectorCompanionAbs]
    protected def getDefaultRep = DenseVector
  }

  implicit def proxyDenseVector[T](p: Rep[DenseVector[T]]): DenseVector[T] =
    proxyOps[DenseVector[T]](p)

  implicit class ExtendedDenseVector[T](p: Rep[DenseVector[T]])(implicit eT: Elem[T]) {
    def toData: Rep[DenseVectorData[T]] = isoDenseVector(eT).from(p)
  }

  // 5) implicit resolution of Iso
  implicit def isoDenseVector[T](implicit eT: Elem[T]): Iso[DenseVectorData[T], DenseVector[T]] =
    reifyObject(new DenseVectorIso[T]()(eT))

  // 6) smart constructor and deconstructor
  def mkDenseVector[T](items: Coll[T])(implicit eT: Elem[T]): Rep[DenseVector[T]]
  def unmkDenseVector[T](p: Rep[AbstractVector[T]]): Option[(Rep[Collection[T]])]

  abstract class AbsConstVector[T]
      (constItem: Rep[T], length: IntRep)(implicit eT: Elem[T])
    extends ConstVector[T](constItem, length) with Def[ConstVector[T]] {
    lazy val selfType = element[ConstVector[T]]
  }
  // elem for concrete class
  class ConstVectorElem[T](val iso: Iso[ConstVectorData[T], ConstVector[T]])(implicit override val eT: Elem[T])
    extends AbstractVectorElem[T, ConstVector[T]]
    with ConcreteElem[ConstVectorData[T], ConstVector[T]] {
    override lazy val parent: Option[Elem[_]] = Some(abstractVectorElement(element[T]))
    override lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map("T" -> Left(eT))
    }

    override def convertAbstractVector(x: Rep[AbstractVector[T]]) = ConstVector(x.constItem, x.length)
    override def getDefaultRep = ConstVector(element[T].defaultRepValue, element[Int].defaultRepValue)
    override lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[ConstVector[T]]
    }
  }

  // state representation type
  type ConstVectorData[T] = (T, Int)

  // 3) Iso for concrete class
  class ConstVectorIso[T](implicit eT: Elem[T])
    extends EntityIso[ConstVectorData[T], ConstVector[T]] with Def[ConstVectorIso[T]] {
    override def from(p: Rep[ConstVector[T]]) =
      (p.constItem, p.length)
    override def to(p: Rep[(T, Int)]) = {
      val Pair(constItem, length) = p
      ConstVector(constItem, length)
    }
    lazy val eFrom = pairElement(element[T], element[Int])
    lazy val eTo = new ConstVectorElem[T](self)
    lazy val selfType = new ConstVectorIsoElem[T](eT)
    def productArity = 1
    def productElement(n: Int) = eT
  }
  case class ConstVectorIsoElem[T](eT: Elem[T]) extends Elem[ConstVectorIso[T]] {
    def isEntityType = true
    def getDefaultRep = reifyObject(new ConstVectorIso[T]()(eT))
    lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[ConstVectorIso[T]]
    }
  }
  // 4) constructor and deconstructor
  class ConstVectorCompanionAbs extends CompanionDef[ConstVectorCompanionAbs] with ConstVectorCompanion {
    def selfType = ConstVectorCompanionElem
    override def toString = "ConstVector"
    def apply[T](p: Rep[ConstVectorData[T]])(implicit eT: Elem[T]): Rep[ConstVector[T]] =
      isoConstVector(eT).to(p)
    def apply[T](constItem: Rep[T], length: IntRep)(implicit eT: Elem[T]): Rep[ConstVector[T]] =
      mkConstVector(constItem, length)
  }
  object ConstVectorMatcher {
    def unapply[T](p: Rep[AbstractVector[T]]) = unmkConstVector(p)
  }
  lazy val ConstVector: Rep[ConstVectorCompanionAbs] = new ConstVectorCompanionAbs
  implicit def proxyConstVectorCompanion(p: Rep[ConstVectorCompanionAbs]): ConstVectorCompanionAbs = {
    proxyOps[ConstVectorCompanionAbs](p)
  }

  implicit case object ConstVectorCompanionElem extends CompanionElem[ConstVectorCompanionAbs] {
    lazy val tag = weakTypeTag[ConstVectorCompanionAbs]
    protected def getDefaultRep = ConstVector
  }

  implicit def proxyConstVector[T](p: Rep[ConstVector[T]]): ConstVector[T] =
    proxyOps[ConstVector[T]](p)

  implicit class ExtendedConstVector[T](p: Rep[ConstVector[T]])(implicit eT: Elem[T]) {
    def toData: Rep[ConstVectorData[T]] = isoConstVector(eT).from(p)
  }

  // 5) implicit resolution of Iso
  implicit def isoConstVector[T](implicit eT: Elem[T]): Iso[ConstVectorData[T], ConstVector[T]] =
    reifyObject(new ConstVectorIso[T]()(eT))

  // 6) smart constructor and deconstructor
  def mkConstVector[T](constItem: Rep[T], length: IntRep)(implicit eT: Elem[T]): Rep[ConstVector[T]]
  def unmkConstVector[T](p: Rep[AbstractVector[T]]): Option[(Rep[T], Rep[Int])]

  abstract class AbsSparseVector[T]
      (nonZeroIndices: Coll[Int], nonZeroValues: Coll[T], length: IntRep)(implicit eT: Elem[T])
    extends SparseVector[T](nonZeroIndices, nonZeroValues, length) with Def[SparseVector[T]] {
    lazy val selfType = element[SparseVector[T]]
  }
  // elem for concrete class
  class SparseVectorElem[T](val iso: Iso[SparseVectorData[T], SparseVector[T]])(implicit override val eT: Elem[T])
    extends AbstractVectorElem[T, SparseVector[T]]
    with ConcreteElem[SparseVectorData[T], SparseVector[T]] {
    override lazy val parent: Option[Elem[_]] = Some(abstractVectorElement(element[T]))
    override lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map("T" -> Left(eT))
    }

    override def convertAbstractVector(x: Rep[AbstractVector[T]]) = SparseVector(x.nonZeroIndices, x.nonZeroValues, x.length)
    override def getDefaultRep = SparseVector(element[Collection[Int]].defaultRepValue, element[Collection[T]].defaultRepValue, element[Int].defaultRepValue)
    override lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[SparseVector[T]]
    }
  }

  // state representation type
  type SparseVectorData[T] = (Collection[Int], (Collection[T], Int))

  // 3) Iso for concrete class
  class SparseVectorIso[T](implicit eT: Elem[T])
    extends EntityIso[SparseVectorData[T], SparseVector[T]] with Def[SparseVectorIso[T]] {
    override def from(p: Rep[SparseVector[T]]) =
      (p.nonZeroIndices, p.nonZeroValues, p.length)
    override def to(p: Rep[(Collection[Int], (Collection[T], Int))]) = {
      val Pair(nonZeroIndices, Pair(nonZeroValues, length)) = p
      SparseVector(nonZeroIndices, nonZeroValues, length)
    }
    lazy val eFrom = pairElement(element[Collection[Int]], pairElement(element[Collection[T]], element[Int]))
    lazy val eTo = new SparseVectorElem[T](self)
    lazy val selfType = new SparseVectorIsoElem[T](eT)
    def productArity = 1
    def productElement(n: Int) = eT
  }
  case class SparseVectorIsoElem[T](eT: Elem[T]) extends Elem[SparseVectorIso[T]] {
    def isEntityType = true
    def getDefaultRep = reifyObject(new SparseVectorIso[T]()(eT))
    lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[SparseVectorIso[T]]
    }
  }
  // 4) constructor and deconstructor
  class SparseVectorCompanionAbs extends CompanionDef[SparseVectorCompanionAbs] with SparseVectorCompanion {
    def selfType = SparseVectorCompanionElem
    override def toString = "SparseVector"
    def apply[T](p: Rep[SparseVectorData[T]])(implicit eT: Elem[T]): Rep[SparseVector[T]] =
      isoSparseVector(eT).to(p)
    def apply[T](nonZeroIndices: Coll[Int], nonZeroValues: Coll[T], length: IntRep)(implicit eT: Elem[T]): Rep[SparseVector[T]] =
      mkSparseVector(nonZeroIndices, nonZeroValues, length)
  }
  object SparseVectorMatcher {
    def unapply[T](p: Rep[AbstractVector[T]]) = unmkSparseVector(p)
  }
  lazy val SparseVector: Rep[SparseVectorCompanionAbs] = new SparseVectorCompanionAbs
  implicit def proxySparseVectorCompanion(p: Rep[SparseVectorCompanionAbs]): SparseVectorCompanionAbs = {
    proxyOps[SparseVectorCompanionAbs](p)
  }

  implicit case object SparseVectorCompanionElem extends CompanionElem[SparseVectorCompanionAbs] {
    lazy val tag = weakTypeTag[SparseVectorCompanionAbs]
    protected def getDefaultRep = SparseVector
  }

  implicit def proxySparseVector[T](p: Rep[SparseVector[T]]): SparseVector[T] =
    proxyOps[SparseVector[T]](p)

  implicit class ExtendedSparseVector[T](p: Rep[SparseVector[T]])(implicit eT: Elem[T]) {
    def toData: Rep[SparseVectorData[T]] = isoSparseVector(eT).from(p)
  }

  // 5) implicit resolution of Iso
  implicit def isoSparseVector[T](implicit eT: Elem[T]): Iso[SparseVectorData[T], SparseVector[T]] =
    reifyObject(new SparseVectorIso[T]()(eT))

  // 6) smart constructor and deconstructor
  def mkSparseVector[T](nonZeroIndices: Coll[Int], nonZeroValues: Coll[T], length: IntRep)(implicit eT: Elem[T]): Rep[SparseVector[T]]
  def unmkSparseVector[T](p: Rep[AbstractVector[T]]): Option[(Rep[Collection[Int]], Rep[Collection[T]], Rep[Int])]

  abstract class AbsSparseVectorBoxed[T]
      (nonZeroItems: Coll[(Int, T)], length: IntRep)(implicit eT: Elem[T])
    extends SparseVectorBoxed[T](nonZeroItems, length) with Def[SparseVectorBoxed[T]] {
    lazy val selfType = element[SparseVectorBoxed[T]]
  }
  // elem for concrete class
  class SparseVectorBoxedElem[T](val iso: Iso[SparseVectorBoxedData[T], SparseVectorBoxed[T]])(implicit eT: Elem[T])
    extends AbstractVectorElem[T, SparseVectorBoxed[T]]
    with ConcreteElem[SparseVectorBoxedData[T], SparseVectorBoxed[T]] {
    override lazy val parent: Option[Elem[_]] = Some(abstractVectorElement(element[T]))
    override lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map("T" -> Left(eT))
    }

    override def convertAbstractVector(x: Rep[AbstractVector[T]]) = SparseVectorBoxed(x.nonZeroItems, x.length)
    override def getDefaultRep = SparseVectorBoxed(element[Collection[(Int, T)]].defaultRepValue, element[Int].defaultRepValue)
    override lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[SparseVectorBoxed[T]]
    }
  }

  // state representation type
  type SparseVectorBoxedData[T] = (Collection[(Int, T)], Int)

  // 3) Iso for concrete class
  class SparseVectorBoxedIso[T](implicit eT: Elem[T])
    extends EntityIso[SparseVectorBoxedData[T], SparseVectorBoxed[T]] with Def[SparseVectorBoxedIso[T]] {
    override def from(p: Rep[SparseVectorBoxed[T]]) =
      (p.nonZeroItems, p.length)
    override def to(p: Rep[(Collection[(Int, T)], Int)]) = {
      val Pair(nonZeroItems, length) = p
      SparseVectorBoxed(nonZeroItems, length)
    }
    lazy val eFrom = pairElement(element[Collection[(Int, T)]], element[Int])
    lazy val eTo = new SparseVectorBoxedElem[T](self)
    lazy val selfType = new SparseVectorBoxedIsoElem[T](eT)
    def productArity = 1
    def productElement(n: Int) = eT
  }
  case class SparseVectorBoxedIsoElem[T](eT: Elem[T]) extends Elem[SparseVectorBoxedIso[T]] {
    def isEntityType = true
    def getDefaultRep = reifyObject(new SparseVectorBoxedIso[T]()(eT))
    lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[SparseVectorBoxedIso[T]]
    }
  }
  // 4) constructor and deconstructor
  class SparseVectorBoxedCompanionAbs extends CompanionDef[SparseVectorBoxedCompanionAbs] with SparseVectorBoxedCompanion {
    def selfType = SparseVectorBoxedCompanionElem
    override def toString = "SparseVectorBoxed"
    def apply[T](p: Rep[SparseVectorBoxedData[T]])(implicit eT: Elem[T]): Rep[SparseVectorBoxed[T]] =
      isoSparseVectorBoxed(eT).to(p)
    def apply[T](nonZeroItems: Coll[(Int, T)], length: IntRep)(implicit eT: Elem[T]): Rep[SparseVectorBoxed[T]] =
      mkSparseVectorBoxed(nonZeroItems, length)
  }
  object SparseVectorBoxedMatcher {
    def unapply[T](p: Rep[AbstractVector[T]]) = unmkSparseVectorBoxed(p)
  }
  lazy val SparseVectorBoxed: Rep[SparseVectorBoxedCompanionAbs] = new SparseVectorBoxedCompanionAbs
  implicit def proxySparseVectorBoxedCompanion(p: Rep[SparseVectorBoxedCompanionAbs]): SparseVectorBoxedCompanionAbs = {
    proxyOps[SparseVectorBoxedCompanionAbs](p)
  }

  implicit case object SparseVectorBoxedCompanionElem extends CompanionElem[SparseVectorBoxedCompanionAbs] {
    lazy val tag = weakTypeTag[SparseVectorBoxedCompanionAbs]
    protected def getDefaultRep = SparseVectorBoxed
  }

  implicit def proxySparseVectorBoxed[T](p: Rep[SparseVectorBoxed[T]]): SparseVectorBoxed[T] =
    proxyOps[SparseVectorBoxed[T]](p)

  implicit class ExtendedSparseVectorBoxed[T](p: Rep[SparseVectorBoxed[T]])(implicit eT: Elem[T]) {
    def toData: Rep[SparseVectorBoxedData[T]] = isoSparseVectorBoxed(eT).from(p)
  }

  // 5) implicit resolution of Iso
  implicit def isoSparseVectorBoxed[T](implicit eT: Elem[T]): Iso[SparseVectorBoxedData[T], SparseVectorBoxed[T]] =
    reifyObject(new SparseVectorBoxedIso[T]()(eT))

  // 6) smart constructor and deconstructor
  def mkSparseVectorBoxed[T](nonZeroItems: Coll[(Int, T)], length: IntRep)(implicit eT: Elem[T]): Rep[SparseVectorBoxed[T]]
  def unmkSparseVectorBoxed[T](p: Rep[AbstractVector[T]]): Option[(Rep[Collection[(Int, T)]], Rep[Int])]

  abstract class AbsShiftVector[T]
      (nonZeroIndices: Coll[Int], nonZeroValues: Coll[T], constItem: Rep[T], length: IntRep)(implicit eT: Elem[T])
    extends ShiftVector[T](nonZeroIndices, nonZeroValues, constItem, length) with Def[ShiftVector[T]] {
    lazy val selfType = element[ShiftVector[T]]
  }
  // elem for concrete class
  class ShiftVectorElem[T](val iso: Iso[ShiftVectorData[T], ShiftVector[T]])(implicit eT: Elem[T])
    extends AbstractVectorElem[T, ShiftVector[T]]
    with ConcreteElem[ShiftVectorData[T], ShiftVector[T]] {
    override lazy val parent: Option[Elem[_]] = Some(abstractVectorElement(element[T]))
    override lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map("T" -> Left(eT))
    }

    override def convertAbstractVector(x: Rep[AbstractVector[T]]) = ShiftVector(x.nonZeroIndices, x.nonZeroValues, x.constItem, x.length)
    override def getDefaultRep = ShiftVector(element[Collection[Int]].defaultRepValue, element[Collection[T]].defaultRepValue, element[T].defaultRepValue, element[Int].defaultRepValue)
    override lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[ShiftVector[T]]
    }
  }

  // state representation type
  type ShiftVectorData[T] = (Collection[Int], (Collection[T], (T, Int)))

  // 3) Iso for concrete class
  class ShiftVectorIso[T](implicit eT: Elem[T])
    extends EntityIso[ShiftVectorData[T], ShiftVector[T]] with Def[ShiftVectorIso[T]] {
    override def from(p: Rep[ShiftVector[T]]) =
      (p.nonZeroIndices, p.nonZeroValues, p.constItem, p.length)
    override def to(p: Rep[(Collection[Int], (Collection[T], (T, Int)))]) = {
      val Pair(nonZeroIndices, Pair(nonZeroValues, Pair(constItem, length))) = p
      ShiftVector(nonZeroIndices, nonZeroValues, constItem, length)
    }
    lazy val eFrom = pairElement(element[Collection[Int]], pairElement(element[Collection[T]], pairElement(element[T], element[Int])))
    lazy val eTo = new ShiftVectorElem[T](self)
    lazy val selfType = new ShiftVectorIsoElem[T](eT)
    def productArity = 1
    def productElement(n: Int) = eT
  }
  case class ShiftVectorIsoElem[T](eT: Elem[T]) extends Elem[ShiftVectorIso[T]] {
    def isEntityType = true
    def getDefaultRep = reifyObject(new ShiftVectorIso[T]()(eT))
    lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[ShiftVectorIso[T]]
    }
  }
  // 4) constructor and deconstructor
  class ShiftVectorCompanionAbs extends CompanionDef[ShiftVectorCompanionAbs] {
    def selfType = ShiftVectorCompanionElem
    override def toString = "ShiftVector"
    def apply[T](p: Rep[ShiftVectorData[T]])(implicit eT: Elem[T]): Rep[ShiftVector[T]] =
      isoShiftVector(eT).to(p)
    def apply[T](nonZeroIndices: Coll[Int], nonZeroValues: Coll[T], constItem: Rep[T], length: IntRep)(implicit eT: Elem[T]): Rep[ShiftVector[T]] =
      mkShiftVector(nonZeroIndices, nonZeroValues, constItem, length)
  }
  object ShiftVectorMatcher {
    def unapply[T](p: Rep[AbstractVector[T]]) = unmkShiftVector(p)
  }
  lazy val ShiftVector: Rep[ShiftVectorCompanionAbs] = new ShiftVectorCompanionAbs
  implicit def proxyShiftVectorCompanion(p: Rep[ShiftVectorCompanionAbs]): ShiftVectorCompanionAbs = {
    proxyOps[ShiftVectorCompanionAbs](p)
  }

  implicit case object ShiftVectorCompanionElem extends CompanionElem[ShiftVectorCompanionAbs] {
    lazy val tag = weakTypeTag[ShiftVectorCompanionAbs]
    protected def getDefaultRep = ShiftVector
  }

  implicit def proxyShiftVector[T](p: Rep[ShiftVector[T]]): ShiftVector[T] =
    proxyOps[ShiftVector[T]](p)

  implicit class ExtendedShiftVector[T](p: Rep[ShiftVector[T]])(implicit eT: Elem[T]) {
    def toData: Rep[ShiftVectorData[T]] = isoShiftVector(eT).from(p)
  }

  // 5) implicit resolution of Iso
  implicit def isoShiftVector[T](implicit eT: Elem[T]): Iso[ShiftVectorData[T], ShiftVector[T]] =
    reifyObject(new ShiftVectorIso[T]()(eT))

  // 6) smart constructor and deconstructor
  def mkShiftVector[T](nonZeroIndices: Coll[Int], nonZeroValues: Coll[T], constItem: Rep[T], length: IntRep)(implicit eT: Elem[T]): Rep[ShiftVector[T]]
  def unmkShiftVector[T](p: Rep[AbstractVector[T]]): Option[(Rep[Collection[Int]], Rep[Collection[T]], Rep[T], Rep[Int])]

  abstract class AbsShiftVectorBoxed[T]
      (nonZeroItems: Coll[(Int, T)], constItem: Rep[T], length: IntRep)(implicit eT: Elem[T])
    extends ShiftVectorBoxed[T](nonZeroItems, constItem, length) with Def[ShiftVectorBoxed[T]] {
    lazy val selfType = element[ShiftVectorBoxed[T]]
  }
  // elem for concrete class
  class ShiftVectorBoxedElem[T](val iso: Iso[ShiftVectorBoxedData[T], ShiftVectorBoxed[T]])(implicit eT: Elem[T])
    extends AbstractVectorElem[T, ShiftVectorBoxed[T]]
    with ConcreteElem[ShiftVectorBoxedData[T], ShiftVectorBoxed[T]] {
    override lazy val parent: Option[Elem[_]] = Some(abstractVectorElement(element[T]))
    override lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map("T" -> Left(eT))
    }

    override def convertAbstractVector(x: Rep[AbstractVector[T]]) = ShiftVectorBoxed(x.nonZeroItems, x.constItem, x.length)
    override def getDefaultRep = ShiftVectorBoxed(element[Collection[(Int, T)]].defaultRepValue, element[T].defaultRepValue, element[Int].defaultRepValue)
    override lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[ShiftVectorBoxed[T]]
    }
  }

  // state representation type
  type ShiftVectorBoxedData[T] = (Collection[(Int, T)], (T, Int))

  // 3) Iso for concrete class
  class ShiftVectorBoxedIso[T](implicit eT: Elem[T])
    extends EntityIso[ShiftVectorBoxedData[T], ShiftVectorBoxed[T]] with Def[ShiftVectorBoxedIso[T]] {
    override def from(p: Rep[ShiftVectorBoxed[T]]) =
      (p.nonZeroItems, p.constItem, p.length)
    override def to(p: Rep[(Collection[(Int, T)], (T, Int))]) = {
      val Pair(nonZeroItems, Pair(constItem, length)) = p
      ShiftVectorBoxed(nonZeroItems, constItem, length)
    }
    lazy val eFrom = pairElement(element[Collection[(Int, T)]], pairElement(element[T], element[Int]))
    lazy val eTo = new ShiftVectorBoxedElem[T](self)
    lazy val selfType = new ShiftVectorBoxedIsoElem[T](eT)
    def productArity = 1
    def productElement(n: Int) = eT
  }
  case class ShiftVectorBoxedIsoElem[T](eT: Elem[T]) extends Elem[ShiftVectorBoxedIso[T]] {
    def isEntityType = true
    def getDefaultRep = reifyObject(new ShiftVectorBoxedIso[T]()(eT))
    lazy val tag = {
      implicit val tagT = eT.tag
      weakTypeTag[ShiftVectorBoxedIso[T]]
    }
  }
  // 4) constructor and deconstructor
  class ShiftVectorBoxedCompanionAbs extends CompanionDef[ShiftVectorBoxedCompanionAbs] {
    def selfType = ShiftVectorBoxedCompanionElem
    override def toString = "ShiftVectorBoxed"
    def apply[T](p: Rep[ShiftVectorBoxedData[T]])(implicit eT: Elem[T]): Rep[ShiftVectorBoxed[T]] =
      isoShiftVectorBoxed(eT).to(p)
    def apply[T](nonZeroItems: Coll[(Int, T)], constItem: Rep[T], length: IntRep)(implicit eT: Elem[T]): Rep[ShiftVectorBoxed[T]] =
      mkShiftVectorBoxed(nonZeroItems, constItem, length)
  }
  object ShiftVectorBoxedMatcher {
    def unapply[T](p: Rep[AbstractVector[T]]) = unmkShiftVectorBoxed(p)
  }
  lazy val ShiftVectorBoxed: Rep[ShiftVectorBoxedCompanionAbs] = new ShiftVectorBoxedCompanionAbs
  implicit def proxyShiftVectorBoxedCompanion(p: Rep[ShiftVectorBoxedCompanionAbs]): ShiftVectorBoxedCompanionAbs = {
    proxyOps[ShiftVectorBoxedCompanionAbs](p)
  }

  implicit case object ShiftVectorBoxedCompanionElem extends CompanionElem[ShiftVectorBoxedCompanionAbs] {
    lazy val tag = weakTypeTag[ShiftVectorBoxedCompanionAbs]
    protected def getDefaultRep = ShiftVectorBoxed
  }

  implicit def proxyShiftVectorBoxed[T](p: Rep[ShiftVectorBoxed[T]]): ShiftVectorBoxed[T] =
    proxyOps[ShiftVectorBoxed[T]](p)

  implicit class ExtendedShiftVectorBoxed[T](p: Rep[ShiftVectorBoxed[T]])(implicit eT: Elem[T]) {
    def toData: Rep[ShiftVectorBoxedData[T]] = isoShiftVectorBoxed(eT).from(p)
  }

  // 5) implicit resolution of Iso
  implicit def isoShiftVectorBoxed[T](implicit eT: Elem[T]): Iso[ShiftVectorBoxedData[T], ShiftVectorBoxed[T]] =
    reifyObject(new ShiftVectorBoxedIso[T]()(eT))

  // 6) smart constructor and deconstructor
  def mkShiftVectorBoxed[T](nonZeroItems: Coll[(Int, T)], constItem: Rep[T], length: IntRep)(implicit eT: Elem[T]): Rep[ShiftVectorBoxed[T]]
  def unmkShiftVectorBoxed[T](p: Rep[AbstractVector[T]]): Option[(Rep[Collection[(Int, T)]], Rep[T], Rep[Int])]

  registerModule(Vectors_Module)
}

// Seq -----------------------------------
trait VectorsSeq extends scalan.ScalanDslStd with VectorsDsl {
  self: LADslSeq =>
  lazy val AbstractVector: Rep[AbstractVectorCompanionAbs] = new AbstractVectorCompanionAbs {
  }

  case class SeqDenseVector[T]
      (override val items: Coll[T])(implicit eT: Elem[T])
    extends AbsDenseVector[T](items) {
  }

  def mkDenseVector[T]
    (items: Coll[T])(implicit eT: Elem[T]): Rep[DenseVector[T]] =
    new SeqDenseVector[T](items)
  def unmkDenseVector[T](p: Rep[AbstractVector[T]]) = p match {
    case p: DenseVector[T] @unchecked =>
      Some((p.items))
    case _ => None
  }

  case class SeqConstVector[T]
      (override val constItem: Rep[T], override val length: IntRep)(implicit eT: Elem[T])
    extends AbsConstVector[T](constItem, length) {
  }

  def mkConstVector[T]
    (constItem: Rep[T], length: IntRep)(implicit eT: Elem[T]): Rep[ConstVector[T]] =
    new SeqConstVector[T](constItem, length)
  def unmkConstVector[T](p: Rep[AbstractVector[T]]) = p match {
    case p: ConstVector[T] @unchecked =>
      Some((p.constItem, p.length))
    case _ => None
  }

  case class SeqSparseVector[T]
      (override val nonZeroIndices: Coll[Int], override val nonZeroValues: Coll[T], override val length: IntRep)(implicit eT: Elem[T])
    extends AbsSparseVector[T](nonZeroIndices, nonZeroValues, length) {
  }

  def mkSparseVector[T]
    (nonZeroIndices: Coll[Int], nonZeroValues: Coll[T], length: IntRep)(implicit eT: Elem[T]): Rep[SparseVector[T]] =
    new SeqSparseVector[T](nonZeroIndices, nonZeroValues, length)
  def unmkSparseVector[T](p: Rep[AbstractVector[T]]) = p match {
    case p: SparseVector[T] @unchecked =>
      Some((p.nonZeroIndices, p.nonZeroValues, p.length))
    case _ => None
  }

  case class SeqSparseVectorBoxed[T]
      (override val nonZeroItems: Coll[(Int, T)], override val length: IntRep)(implicit eT: Elem[T])
    extends AbsSparseVectorBoxed[T](nonZeroItems, length) {
  }

  def mkSparseVectorBoxed[T]
    (nonZeroItems: Coll[(Int, T)], length: IntRep)(implicit eT: Elem[T]): Rep[SparseVectorBoxed[T]] =
    new SeqSparseVectorBoxed[T](nonZeroItems, length)
  def unmkSparseVectorBoxed[T](p: Rep[AbstractVector[T]]) = p match {
    case p: SparseVectorBoxed[T] @unchecked =>
      Some((p.nonZeroItems, p.length))
    case _ => None
  }

  case class SeqShiftVector[T]
      (override val nonZeroIndices: Coll[Int], override val nonZeroValues: Coll[T], override val constItem: Rep[T], override val length: IntRep)(implicit eT: Elem[T])
    extends AbsShiftVector[T](nonZeroIndices, nonZeroValues, constItem, length) {
  }

  def mkShiftVector[T]
    (nonZeroIndices: Coll[Int], nonZeroValues: Coll[T], constItem: Rep[T], length: IntRep)(implicit eT: Elem[T]): Rep[ShiftVector[T]] =
    new SeqShiftVector[T](nonZeroIndices, nonZeroValues, constItem, length)
  def unmkShiftVector[T](p: Rep[AbstractVector[T]]) = p match {
    case p: ShiftVector[T] @unchecked =>
      Some((p.nonZeroIndices, p.nonZeroValues, p.constItem, p.length))
    case _ => None
  }

  case class SeqShiftVectorBoxed[T]
      (override val nonZeroItems: Coll[(Int, T)], override val constItem: Rep[T], override val length: IntRep)(implicit eT: Elem[T])
    extends AbsShiftVectorBoxed[T](nonZeroItems, constItem, length) {
  }

  def mkShiftVectorBoxed[T]
    (nonZeroItems: Coll[(Int, T)], constItem: Rep[T], length: IntRep)(implicit eT: Elem[T]): Rep[ShiftVectorBoxed[T]] =
    new SeqShiftVectorBoxed[T](nonZeroItems, constItem, length)
  def unmkShiftVectorBoxed[T](p: Rep[AbstractVector[T]]) = p match {
    case p: ShiftVectorBoxed[T] @unchecked =>
      Some((p.nonZeroItems, p.constItem, p.length))
    case _ => None
  }
}

// Exp -----------------------------------
trait VectorsExp extends scalan.ScalanDslExp with VectorsDsl {
  self: LADslExp =>
  lazy val AbstractVector: Rep[AbstractVectorCompanionAbs] = new AbstractVectorCompanionAbs {
  }

  case class ExpDenseVector[T]
      (override val items: Coll[T])(implicit eT: Elem[T])
    extends AbsDenseVector[T](items)

  object DenseVectorMethods {
    object length {
      def unapply(d: Def[_]): Option[Rep[DenseVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "length" =>
          Some(receiver).asInstanceOf[Option[Rep[DenseVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[DenseVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object nonZeroIndices {
      def unapply(d: Def[_]): Option[Rep[DenseVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "nonZeroIndices" =>
          Some(receiver).asInstanceOf[Option[Rep[DenseVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[DenseVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object nonZeroValues {
      def unapply(d: Def[_]): Option[Rep[DenseVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "nonZeroValues" =>
          Some(receiver).asInstanceOf[Option[Rep[DenseVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[DenseVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object nonZeroItems {
      def unapply(d: Def[_]): Option[Rep[DenseVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "nonZeroItems" =>
          Some(receiver).asInstanceOf[Option[Rep[DenseVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[DenseVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object constItem {
      def unapply(d: Def[_]): Option[Rep[DenseVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "constItem" =>
          Some(receiver).asInstanceOf[Option[Rep[DenseVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[DenseVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply {
      def unapply(d: Def[_]): Option[(Rep[DenseVector[T]], IntRep) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(i, _*), _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "apply" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, i)).asInstanceOf[Option[(Rep[DenseVector[T]], IntRep) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseVector[T]], IntRep) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_apply_by_collection {
      def unapply(d: Def[_]): Option[(Rep[DenseVector[T]], Coll[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(is, _*), _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "apply_by_collection" } =>
          Some((receiver, is)).asInstanceOf[Option[(Rep[DenseVector[T]], Coll[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseVector[T]], Coll[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object filterBy {
      def unapply(d: Def[_]): Option[(Rep[DenseVector[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(f, _*), _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "filterBy" =>
          Some((receiver, f)).asInstanceOf[Option[(Rep[DenseVector[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseVector[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object +^ {
      def unapply(d: Def[_]): Option[(Rep[DenseVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "$plus$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[DenseVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object -^ {
      def unapply(d: Def[_]): Option[(Rep[DenseVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "$minus$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[DenseVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object *^ {
      def unapply(d: Def[_]): Option[(Rep[DenseVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "$times$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[DenseVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object /^ {
      def unapply(d: Def[_]): Option[(Rep[DenseVector[T]], Vector[T], Fractional[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, f, _*), _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "$div$up" =>
          Some((receiver, vector, f)).asInstanceOf[Option[(Rep[DenseVector[T]], Vector[T], Fractional[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseVector[T]], Vector[T], Fractional[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object dot {
      def unapply(d: Def[_]): Option[(Rep[DenseVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "dot" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[DenseVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object * {
      def unapply(d: Def[_]): Option[(Rep[DenseVector[T]], Matrix[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "$times" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[DenseVector[T]], Matrix[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseVector[T]], Matrix[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object pow_^ {
      def unapply(d: Def[_]): Option[(Rep[DenseVector[T]], DoubleRep, Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(order, n, _*), _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "pow_$up" =>
          Some((receiver, order, n)).asInstanceOf[Option[(Rep[DenseVector[T]], DoubleRep, Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseVector[T]], DoubleRep, Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sum {
      def unapply(d: Def[_]): Option[(Rep[DenseVector[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "sum" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[DenseVector[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseVector[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object reduce {
      def unapply(d: Def[_]): Option[(Rep[DenseVector[T]], RepMonoid[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(m, _*), _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "reduce" =>
          Some((receiver, m)).asInstanceOf[Option[(Rep[DenseVector[T]], RepMonoid[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseVector[T]], RepMonoid[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object euclideanNorm {
      def unapply(d: Def[_]): Option[(Rep[DenseVector[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(num, _*), _) if receiver.elem.isInstanceOf[DenseVectorElem[_]] && method.getName == "euclideanNorm" =>
          Some((receiver, num)).asInstanceOf[Option[(Rep[DenseVector[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[DenseVector[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  object DenseVectorCompanionMethods {
    object zero {
      def unapply(d: Def[_]): Option[IntRep forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(len, _*), _) if receiver.elem == DenseVectorCompanionElem && method.getName == "zero" =>
          Some(len).asInstanceOf[Option[IntRep forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[IntRep forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object fromSparseData {
      def unapply(d: Def[_]): Option[(Coll[Int], Coll[T], IntRep) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(nonZeroIndices, nonZeroValues, length, _*), _) if receiver.elem == DenseVectorCompanionElem && method.getName == "fromSparseData" =>
          Some((nonZeroIndices, nonZeroValues, length)).asInstanceOf[Option[(Coll[Int], Coll[T], IntRep) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Coll[Int], Coll[T], IntRep) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  def mkDenseVector[T]
    (items: Coll[T])(implicit eT: Elem[T]): Rep[DenseVector[T]] =
    new ExpDenseVector[T](items)
  def unmkDenseVector[T](p: Rep[AbstractVector[T]]) = p.elem.asInstanceOf[Elem[_]] match {
    case _: DenseVectorElem[T] @unchecked =>
      Some((p.asRep[DenseVector[T]].items))
    case _ =>
      None
  }

  case class ExpConstVector[T]
      (override val constItem: Rep[T], override val length: IntRep)(implicit eT: Elem[T])
    extends AbsConstVector[T](constItem, length)

  object ConstVectorMethods {
    object items {
      def unapply(d: Def[_]): Option[Rep[ConstVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ConstVectorElem[_]] && method.getName == "items" =>
          Some(receiver).asInstanceOf[Option[Rep[ConstVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ConstVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object nonZeroIndices {
      def unapply(d: Def[_]): Option[Rep[ConstVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ConstVectorElem[_]] && method.getName == "nonZeroIndices" =>
          Some(receiver).asInstanceOf[Option[Rep[ConstVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ConstVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object nonZeroValues {
      def unapply(d: Def[_]): Option[Rep[ConstVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ConstVectorElem[_]] && method.getName == "nonZeroValues" =>
          Some(receiver).asInstanceOf[Option[Rep[ConstVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ConstVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object nonZeroItems {
      def unapply(d: Def[_]): Option[Rep[ConstVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ConstVectorElem[_]] && method.getName == "nonZeroItems" =>
          Some(receiver).asInstanceOf[Option[Rep[ConstVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ConstVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply {
      def unapply(d: Def[_]): Option[(Rep[ConstVector[T]], IntRep) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(i, _*), _) if receiver.elem.isInstanceOf[ConstVectorElem[_]] && method.getName == "apply" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, i)).asInstanceOf[Option[(Rep[ConstVector[T]], IntRep) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstVector[T]], IntRep) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_apply_by_collection {
      def unapply(d: Def[_]): Option[(Rep[ConstVector[T]], Coll[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(is, _*), _) if receiver.elem.isInstanceOf[ConstVectorElem[_]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "apply_by_collection" } =>
          Some((receiver, is)).asInstanceOf[Option[(Rep[ConstVector[T]], Coll[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstVector[T]], Coll[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object filterBy {
      def unapply(d: Def[_]): Option[(Rep[ConstVector[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(f, _*), _) if receiver.elem.isInstanceOf[ConstVectorElem[_]] && method.getName == "filterBy" =>
          Some((receiver, f)).asInstanceOf[Option[(Rep[ConstVector[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstVector[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object +^ {
      def unapply(d: Def[_]): Option[(Rep[ConstVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[ConstVectorElem[_]] && method.getName == "$plus$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[ConstVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object -^ {
      def unapply(d: Def[_]): Option[(Rep[ConstVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[ConstVectorElem[_]] && method.getName == "$minus$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[ConstVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object *^ {
      def unapply(d: Def[_]): Option[(Rep[ConstVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[ConstVectorElem[_]] && method.getName == "$times$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[ConstVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object /^ {
      def unapply(d: Def[_]): Option[(Rep[ConstVector[T]], Vector[T], Fractional[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, f, _*), _) if receiver.elem.isInstanceOf[ConstVectorElem[_]] && method.getName == "$div$up" =>
          Some((receiver, vector, f)).asInstanceOf[Option[(Rep[ConstVector[T]], Vector[T], Fractional[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstVector[T]], Vector[T], Fractional[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object dot {
      def unapply(d: Def[_]): Option[(Rep[ConstVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[ConstVectorElem[_]] && method.getName == "dot" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[ConstVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object * {
      def unapply(d: Def[_]): Option[(Rep[ConstVector[T]], Matrix[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[ConstVectorElem[_]] && method.getName == "$times" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[ConstVector[T]], Matrix[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstVector[T]], Matrix[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object pow_^ {
      def unapply(d: Def[_]): Option[(Rep[ConstVector[T]], DoubleRep, Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(order, n, _*), _) if receiver.elem.isInstanceOf[ConstVectorElem[_]] && method.getName == "pow_$up" =>
          Some((receiver, order, n)).asInstanceOf[Option[(Rep[ConstVector[T]], DoubleRep, Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstVector[T]], DoubleRep, Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sum {
      def unapply(d: Def[_]): Option[(Rep[ConstVector[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[ConstVectorElem[_]] && method.getName == "sum" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[ConstVector[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstVector[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object reduce {
      def unapply(d: Def[_]): Option[(Rep[ConstVector[T]], RepMonoid[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(m, _*), _) if receiver.elem.isInstanceOf[ConstVectorElem[_]] && method.getName == "reduce" =>
          Some((receiver, m)).asInstanceOf[Option[(Rep[ConstVector[T]], RepMonoid[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstVector[T]], RepMonoid[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object euclideanNorm {
      def unapply(d: Def[_]): Option[(Rep[ConstVector[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(num, _*), _) if receiver.elem.isInstanceOf[ConstVectorElem[_]] && method.getName == "euclideanNorm" =>
          Some((receiver, num)).asInstanceOf[Option[(Rep[ConstVector[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ConstVector[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  object ConstVectorCompanionMethods {
    object zero {
      def unapply(d: Def[_]): Option[IntRep forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(len, _*), _) if receiver.elem == ConstVectorCompanionElem && method.getName == "zero" =>
          Some(len).asInstanceOf[Option[IntRep forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[IntRep forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object fromSparseData {
      def unapply(d: Def[_]): Option[(Coll[Int], Coll[T], IntRep) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(nonZeroIndices, nonZeroValues, length, _*), _) if receiver.elem == ConstVectorCompanionElem && method.getName == "fromSparseData" =>
          Some((nonZeroIndices, nonZeroValues, length)).asInstanceOf[Option[(Coll[Int], Coll[T], IntRep) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Coll[Int], Coll[T], IntRep) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  def mkConstVector[T]
    (constItem: Rep[T], length: IntRep)(implicit eT: Elem[T]): Rep[ConstVector[T]] =
    new ExpConstVector[T](constItem, length)
  def unmkConstVector[T](p: Rep[AbstractVector[T]]) = p.elem.asInstanceOf[Elem[_]] match {
    case _: ConstVectorElem[T] @unchecked =>
      Some((p.asRep[ConstVector[T]].constItem, p.asRep[ConstVector[T]].length))
    case _ =>
      None
  }

  case class ExpSparseVector[T]
      (override val nonZeroIndices: Coll[Int], override val nonZeroValues: Coll[T], override val length: IntRep)(implicit eT: Elem[T])
    extends AbsSparseVector[T](nonZeroIndices, nonZeroValues, length)

  object SparseVectorMethods {
    object items {
      def unapply(d: Def[_]): Option[Rep[SparseVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[SparseVectorElem[_]] && method.getName == "items" =>
          Some(receiver).asInstanceOf[Option[Rep[SparseVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[SparseVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object constItem {
      def unapply(d: Def[_]): Option[Rep[SparseVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[SparseVectorElem[_]] && method.getName == "constItem" =>
          Some(receiver).asInstanceOf[Option[Rep[SparseVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[SparseVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object nonZeroItems {
      def unapply(d: Def[_]): Option[Rep[SparseVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[SparseVectorElem[_]] && method.getName == "nonZeroItems" =>
          Some(receiver).asInstanceOf[Option[Rep[SparseVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[SparseVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply {
      def unapply(d: Def[_]): Option[(Rep[SparseVector[T]], IntRep) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(i, _*), _) if receiver.elem.isInstanceOf[SparseVectorElem[_]] && method.getName == "apply" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, i)).asInstanceOf[Option[(Rep[SparseVector[T]], IntRep) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVector[T]], IntRep) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_apply_by_collection {
      def unapply(d: Def[_]): Option[(Rep[SparseVector[T]], Coll[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(is, _*), _) if receiver.elem.isInstanceOf[SparseVectorElem[_]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "apply_by_collection" } =>
          Some((receiver, is)).asInstanceOf[Option[(Rep[SparseVector[T]], Coll[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVector[T]], Coll[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object filterBy {
      def unapply(d: Def[_]): Option[(Rep[SparseVector[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(f, _*), _) if receiver.elem.isInstanceOf[SparseVectorElem[_]] && method.getName == "filterBy" =>
          Some((receiver, f)).asInstanceOf[Option[(Rep[SparseVector[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVector[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object +^ {
      def unapply(d: Def[_]): Option[(Rep[SparseVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[SparseVectorElem[_]] && method.getName == "$plus$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[SparseVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object -^ {
      def unapply(d: Def[_]): Option[(Rep[SparseVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[SparseVectorElem[_]] && method.getName == "$minus$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[SparseVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object *^ {
      def unapply(d: Def[_]): Option[(Rep[SparseVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[SparseVectorElem[_]] && method.getName == "$times$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[SparseVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object /^ {
      def unapply(d: Def[_]): Option[(Rep[SparseVector[T]], Vector[T], Fractional[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, f, _*), _) if receiver.elem.isInstanceOf[SparseVectorElem[_]] && method.getName == "$div$up" =>
          Some((receiver, vector, f)).asInstanceOf[Option[(Rep[SparseVector[T]], Vector[T], Fractional[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVector[T]], Vector[T], Fractional[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object dot {
      def unapply(d: Def[_]): Option[(Rep[SparseVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[SparseVectorElem[_]] && method.getName == "dot" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[SparseVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object * {
      def unapply(d: Def[_]): Option[(Rep[SparseVector[T]], Matrix[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[SparseVectorElem[_]] && method.getName == "$times" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[SparseVector[T]], Matrix[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVector[T]], Matrix[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object pow_^ {
      def unapply(d: Def[_]): Option[(Rep[SparseVector[T]], DoubleRep, Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(order, n, _*), _) if receiver.elem.isInstanceOf[SparseVectorElem[_]] && method.getName == "pow_$up" =>
          Some((receiver, order, n)).asInstanceOf[Option[(Rep[SparseVector[T]], DoubleRep, Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVector[T]], DoubleRep, Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sum {
      def unapply(d: Def[_]): Option[(Rep[SparseVector[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[SparseVectorElem[_]] && method.getName == "sum" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[SparseVector[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVector[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object reduce {
      def unapply(d: Def[_]): Option[(Rep[SparseVector[T]], RepMonoid[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(m, _*), _) if receiver.elem.isInstanceOf[SparseVectorElem[_]] && method.getName == "reduce" =>
          Some((receiver, m)).asInstanceOf[Option[(Rep[SparseVector[T]], RepMonoid[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVector[T]], RepMonoid[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object euclideanNorm {
      def unapply(d: Def[_]): Option[(Rep[SparseVector[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(num, _*), _) if receiver.elem.isInstanceOf[SparseVectorElem[_]] && method.getName == "euclideanNorm" =>
          Some((receiver, num)).asInstanceOf[Option[(Rep[SparseVector[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVector[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  object SparseVectorCompanionMethods {
    object apply {
      def unapply(d: Def[_]): Option[(Coll[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(items, n, _*), _) if receiver.elem == SparseVectorCompanionElem && method.getName == "apply" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((items, n)).asInstanceOf[Option[(Coll[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Coll[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_SparseVectorCompanion_apply_nonZeroItems {
      def unapply(d: Def[_]): Option[(Coll[(Int, T)], IntRep, Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(nonZeroItems, length, n, _*), _) if receiver.elem == SparseVectorCompanionElem && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "SparseVectorCompanion_apply_nonZeroItems" } =>
          Some((nonZeroItems, length, n)).asInstanceOf[Option[(Coll[(Int, T)], IntRep, Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Coll[(Int, T)], IntRep, Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object zero {
      def unapply(d: Def[_]): Option[IntRep forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(len, _*), _) if receiver.elem == SparseVectorCompanionElem && method.getName == "zero" =>
          Some(len).asInstanceOf[Option[IntRep forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[IntRep forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object fromSparseData {
      def unapply(d: Def[_]): Option[(Coll[Int], Coll[T], IntRep) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(nonZeroIndices, nonZeroValues, length, _*), _) if receiver.elem == SparseVectorCompanionElem && method.getName == "fromSparseData" =>
          Some((nonZeroIndices, nonZeroValues, length)).asInstanceOf[Option[(Coll[Int], Coll[T], IntRep) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Coll[Int], Coll[T], IntRep) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  def mkSparseVector[T]
    (nonZeroIndices: Coll[Int], nonZeroValues: Coll[T], length: IntRep)(implicit eT: Elem[T]): Rep[SparseVector[T]] =
    new ExpSparseVector[T](nonZeroIndices, nonZeroValues, length)
  def unmkSparseVector[T](p: Rep[AbstractVector[T]]) = p.elem.asInstanceOf[Elem[_]] match {
    case _: SparseVectorElem[T] @unchecked =>
      Some((p.asRep[SparseVector[T]].nonZeroIndices, p.asRep[SparseVector[T]].nonZeroValues, p.asRep[SparseVector[T]].length))
    case _ =>
      None
  }

  case class ExpSparseVectorBoxed[T]
      (override val nonZeroItems: Coll[(Int, T)], override val length: IntRep)(implicit eT: Elem[T])
    extends AbsSparseVectorBoxed[T](nonZeroItems, length)

  object SparseVectorBoxedMethods {
    object items {
      def unapply(d: Def[_]): Option[Rep[SparseVectorBoxed[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[SparseVectorBoxedElem[_]] && method.getName == "items" =>
          Some(receiver).asInstanceOf[Option[Rep[SparseVectorBoxed[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[SparseVectorBoxed[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object constItem {
      def unapply(d: Def[_]): Option[Rep[SparseVectorBoxed[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[SparseVectorBoxedElem[_]] && method.getName == "constItem" =>
          Some(receiver).asInstanceOf[Option[Rep[SparseVectorBoxed[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[SparseVectorBoxed[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object nonZeroIndices {
      def unapply(d: Def[_]): Option[Rep[SparseVectorBoxed[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[SparseVectorBoxedElem[_]] && method.getName == "nonZeroIndices" =>
          Some(receiver).asInstanceOf[Option[Rep[SparseVectorBoxed[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[SparseVectorBoxed[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object nonZeroValues {
      def unapply(d: Def[_]): Option[Rep[SparseVectorBoxed[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[SparseVectorBoxedElem[_]] && method.getName == "nonZeroValues" =>
          Some(receiver).asInstanceOf[Option[Rep[SparseVectorBoxed[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[SparseVectorBoxed[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply {
      def unapply(d: Def[_]): Option[(Rep[SparseVectorBoxed[T]], IntRep) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(i, _*), _) if receiver.elem.isInstanceOf[SparseVectorBoxedElem[_]] && method.getName == "apply" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, i)).asInstanceOf[Option[(Rep[SparseVectorBoxed[T]], IntRep) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVectorBoxed[T]], IntRep) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_apply_by_collection {
      def unapply(d: Def[_]): Option[(Rep[SparseVectorBoxed[T]], Coll[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(is, _*), _) if receiver.elem.isInstanceOf[SparseVectorBoxedElem[_]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "apply_by_collection" } =>
          Some((receiver, is)).asInstanceOf[Option[(Rep[SparseVectorBoxed[T]], Coll[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVectorBoxed[T]], Coll[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object filterBy {
      def unapply(d: Def[_]): Option[(Rep[SparseVectorBoxed[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(f, _*), _) if receiver.elem.isInstanceOf[SparseVectorBoxedElem[_]] && method.getName == "filterBy" =>
          Some((receiver, f)).asInstanceOf[Option[(Rep[SparseVectorBoxed[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVectorBoxed[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object +^ {
      def unapply(d: Def[_]): Option[(Rep[SparseVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[SparseVectorBoxedElem[_]] && method.getName == "$plus$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[SparseVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object -^ {
      def unapply(d: Def[_]): Option[(Rep[SparseVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[SparseVectorBoxedElem[_]] && method.getName == "$minus$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[SparseVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object *^ {
      def unapply(d: Def[_]): Option[(Rep[SparseVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[SparseVectorBoxedElem[_]] && method.getName == "$times$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[SparseVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object /^ {
      def unapply(d: Def[_]): Option[(Rep[SparseVectorBoxed[T]], Vector[T], Fractional[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, f, _*), _) if receiver.elem.isInstanceOf[SparseVectorBoxedElem[_]] && method.getName == "$div$up" =>
          Some((receiver, vector, f)).asInstanceOf[Option[(Rep[SparseVectorBoxed[T]], Vector[T], Fractional[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVectorBoxed[T]], Vector[T], Fractional[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object dot {
      def unapply(d: Def[_]): Option[(Rep[SparseVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[SparseVectorBoxedElem[_]] && method.getName == "dot" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[SparseVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object * {
      def unapply(d: Def[_]): Option[(Rep[SparseVectorBoxed[T]], Matrix[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[SparseVectorBoxedElem[_]] && method.getName == "$times" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[SparseVectorBoxed[T]], Matrix[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVectorBoxed[T]], Matrix[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object pow_^ {
      def unapply(d: Def[_]): Option[(Rep[SparseVectorBoxed[T]], DoubleRep, Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(order, n, _*), _) if receiver.elem.isInstanceOf[SparseVectorBoxedElem[_]] && method.getName == "pow_$up" =>
          Some((receiver, order, n)).asInstanceOf[Option[(Rep[SparseVectorBoxed[T]], DoubleRep, Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVectorBoxed[T]], DoubleRep, Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sum {
      def unapply(d: Def[_]): Option[(Rep[SparseVectorBoxed[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[SparseVectorBoxedElem[_]] && method.getName == "sum" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[SparseVectorBoxed[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVectorBoxed[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object reduce {
      def unapply(d: Def[_]): Option[(Rep[SparseVectorBoxed[T]], RepMonoid[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(m, _*), _) if receiver.elem.isInstanceOf[SparseVectorBoxedElem[_]] && method.getName == "reduce" =>
          Some((receiver, m)).asInstanceOf[Option[(Rep[SparseVectorBoxed[T]], RepMonoid[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVectorBoxed[T]], RepMonoid[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object euclideanNorm {
      def unapply(d: Def[_]): Option[(Rep[SparseVectorBoxed[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(num, _*), _) if receiver.elem.isInstanceOf[SparseVectorBoxedElem[_]] && method.getName == "euclideanNorm" =>
          Some((receiver, num)).asInstanceOf[Option[(Rep[SparseVectorBoxed[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[SparseVectorBoxed[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  object SparseVectorBoxedCompanionMethods {
    object apply {
      def unapply(d: Def[_]): Option[(Coll[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(items, n, _*), _) if receiver.elem == SparseVectorBoxedCompanionElem && method.getName == "apply" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((items, n)).asInstanceOf[Option[(Coll[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Coll[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_SparseVector1Companion_apply_nonZeroItems {
      def unapply(d: Def[_]): Option[(Coll[Int], Coll[T], IntRep, Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(nonZeroIndices, nonZeroValues, length, n, _*), _) if receiver.elem == SparseVectorBoxedCompanionElem && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "SparseVector1Companion_apply_nonZeroItems" } =>
          Some((nonZeroIndices, nonZeroValues, length, n)).asInstanceOf[Option[(Coll[Int], Coll[T], IntRep, Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Coll[Int], Coll[T], IntRep, Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object zero {
      def unapply(d: Def[_]): Option[IntRep forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(len, _*), _) if receiver.elem == SparseVectorBoxedCompanionElem && method.getName == "zero" =>
          Some(len).asInstanceOf[Option[IntRep forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[IntRep forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object fromSparseData {
      def unapply(d: Def[_]): Option[(Coll[Int], Coll[T], IntRep) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(nonZeroIndices, nonZeroValues, length, _*), _) if receiver.elem == SparseVectorBoxedCompanionElem && method.getName == "fromSparseData" =>
          Some((nonZeroIndices, nonZeroValues, length)).asInstanceOf[Option[(Coll[Int], Coll[T], IntRep) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Coll[Int], Coll[T], IntRep) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  def mkSparseVectorBoxed[T]
    (nonZeroItems: Coll[(Int, T)], length: IntRep)(implicit eT: Elem[T]): Rep[SparseVectorBoxed[T]] =
    new ExpSparseVectorBoxed[T](nonZeroItems, length)
  def unmkSparseVectorBoxed[T](p: Rep[AbstractVector[T]]) = p.elem.asInstanceOf[Elem[_]] match {
    case _: SparseVectorBoxedElem[T] @unchecked =>
      Some((p.asRep[SparseVectorBoxed[T]].nonZeroItems, p.asRep[SparseVectorBoxed[T]].length))
    case _ =>
      None
  }

  case class ExpShiftVector[T]
      (override val nonZeroIndices: Coll[Int], override val nonZeroValues: Coll[T], override val constItem: Rep[T], override val length: IntRep)(implicit eT: Elem[T])
    extends AbsShiftVector[T](nonZeroIndices, nonZeroValues, constItem, length)

  object ShiftVectorMethods {
    object items {
      def unapply(d: Def[_]): Option[Rep[ShiftVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ShiftVectorElem[_]] && method.getName == "items" =>
          Some(receiver).asInstanceOf[Option[Rep[ShiftVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ShiftVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object nonZeroItems {
      def unapply(d: Def[_]): Option[Rep[ShiftVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ShiftVectorElem[_]] && method.getName == "nonZeroItems" =>
          Some(receiver).asInstanceOf[Option[Rep[ShiftVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ShiftVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply {
      def unapply(d: Def[_]): Option[(Rep[ShiftVector[T]], IntRep) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(i, _*), _) if receiver.elem.isInstanceOf[ShiftVectorElem[_]] && method.getName == "apply" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, i)).asInstanceOf[Option[(Rep[ShiftVector[T]], IntRep) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVector[T]], IntRep) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_apply_by_collection {
      def unapply(d: Def[_]): Option[(Rep[ShiftVector[T]], Coll[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(is, _*), _) if receiver.elem.isInstanceOf[ShiftVectorElem[_]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "apply_by_collection" } =>
          Some((receiver, is)).asInstanceOf[Option[(Rep[ShiftVector[T]], Coll[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVector[T]], Coll[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object filterBy {
      def unapply(d: Def[_]): Option[(Rep[ShiftVector[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(f, _*), _) if receiver.elem.isInstanceOf[ShiftVectorElem[_]] && method.getName == "filterBy" =>
          Some((receiver, f)).asInstanceOf[Option[(Rep[ShiftVector[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVector[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object +^ {
      def unapply(d: Def[_]): Option[(Rep[ShiftVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[ShiftVectorElem[_]] && method.getName == "$plus$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[ShiftVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object -^ {
      def unapply(d: Def[_]): Option[(Rep[ShiftVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[ShiftVectorElem[_]] && method.getName == "$minus$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[ShiftVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object *^ {
      def unapply(d: Def[_]): Option[(Rep[ShiftVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[ShiftVectorElem[_]] && method.getName == "$times$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[ShiftVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object /^ {
      def unapply(d: Def[_]): Option[(Rep[ShiftVector[T]], Vector[T], Fractional[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, f, _*), _) if receiver.elem.isInstanceOf[ShiftVectorElem[_]] && method.getName == "$div$up" =>
          Some((receiver, vector, f)).asInstanceOf[Option[(Rep[ShiftVector[T]], Vector[T], Fractional[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVector[T]], Vector[T], Fractional[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object dot {
      def unapply(d: Def[_]): Option[(Rep[ShiftVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[ShiftVectorElem[_]] && method.getName == "dot" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[ShiftVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object * {
      def unapply(d: Def[_]): Option[(Rep[ShiftVector[T]], Matrix[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[ShiftVectorElem[_]] && method.getName == "$times" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[ShiftVector[T]], Matrix[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVector[T]], Matrix[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object pow_^ {
      def unapply(d: Def[_]): Option[(Rep[ShiftVector[T]], DoubleRep, Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(order, n, _*), _) if receiver.elem.isInstanceOf[ShiftVectorElem[_]] && method.getName == "pow_$up" =>
          Some((receiver, order, n)).asInstanceOf[Option[(Rep[ShiftVector[T]], DoubleRep, Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVector[T]], DoubleRep, Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sum {
      def unapply(d: Def[_]): Option[(Rep[ShiftVector[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[ShiftVectorElem[_]] && method.getName == "sum" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[ShiftVector[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVector[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object reduce {
      def unapply(d: Def[_]): Option[(Rep[ShiftVector[T]], RepMonoid[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(m, _*), _) if receiver.elem.isInstanceOf[ShiftVectorElem[_]] && method.getName == "reduce" =>
          Some((receiver, m)).asInstanceOf[Option[(Rep[ShiftVector[T]], RepMonoid[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVector[T]], RepMonoid[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object euclideanNorm {
      def unapply(d: Def[_]): Option[(Rep[ShiftVector[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(num, _*), _) if receiver.elem.isInstanceOf[ShiftVectorElem[_]] && method.getName == "euclideanNorm" =>
          Some((receiver, num)).asInstanceOf[Option[(Rep[ShiftVector[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVector[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  def mkShiftVector[T]
    (nonZeroIndices: Coll[Int], nonZeroValues: Coll[T], constItem: Rep[T], length: IntRep)(implicit eT: Elem[T]): Rep[ShiftVector[T]] =
    new ExpShiftVector[T](nonZeroIndices, nonZeroValues, constItem, length)
  def unmkShiftVector[T](p: Rep[AbstractVector[T]]) = p.elem.asInstanceOf[Elem[_]] match {
    case _: ShiftVectorElem[T] @unchecked =>
      Some((p.asRep[ShiftVector[T]].nonZeroIndices, p.asRep[ShiftVector[T]].nonZeroValues, p.asRep[ShiftVector[T]].constItem, p.asRep[ShiftVector[T]].length))
    case _ =>
      None
  }

  case class ExpShiftVectorBoxed[T]
      (override val nonZeroItems: Coll[(Int, T)], override val constItem: Rep[T], override val length: IntRep)(implicit eT: Elem[T])
    extends AbsShiftVectorBoxed[T](nonZeroItems, constItem, length)

  object ShiftVectorBoxedMethods {
    object items {
      def unapply(d: Def[_]): Option[Rep[ShiftVectorBoxed[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ShiftVectorBoxedElem[_]] && method.getName == "items" =>
          Some(receiver).asInstanceOf[Option[Rep[ShiftVectorBoxed[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ShiftVectorBoxed[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object nonZeroIndices {
      def unapply(d: Def[_]): Option[Rep[ShiftVectorBoxed[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ShiftVectorBoxedElem[_]] && method.getName == "nonZeroIndices" =>
          Some(receiver).asInstanceOf[Option[Rep[ShiftVectorBoxed[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ShiftVectorBoxed[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object nonZeroValues {
      def unapply(d: Def[_]): Option[Rep[ShiftVectorBoxed[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ShiftVectorBoxedElem[_]] && method.getName == "nonZeroValues" =>
          Some(receiver).asInstanceOf[Option[Rep[ShiftVectorBoxed[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ShiftVectorBoxed[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply {
      def unapply(d: Def[_]): Option[(Rep[ShiftVectorBoxed[T]], IntRep) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(i, _*), _) if receiver.elem.isInstanceOf[ShiftVectorBoxedElem[_]] && method.getName == "apply" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, i)).asInstanceOf[Option[(Rep[ShiftVectorBoxed[T]], IntRep) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVectorBoxed[T]], IntRep) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_apply_by_collection {
      def unapply(d: Def[_]): Option[(Rep[ShiftVectorBoxed[T]], Coll[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(is, _*), _) if receiver.elem.isInstanceOf[ShiftVectorBoxedElem[_]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "apply_by_collection" } =>
          Some((receiver, is)).asInstanceOf[Option[(Rep[ShiftVectorBoxed[T]], Coll[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVectorBoxed[T]], Coll[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object filterBy {
      def unapply(d: Def[_]): Option[(Rep[ShiftVectorBoxed[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(f, _*), _) if receiver.elem.isInstanceOf[ShiftVectorBoxedElem[_]] && method.getName == "filterBy" =>
          Some((receiver, f)).asInstanceOf[Option[(Rep[ShiftVectorBoxed[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVectorBoxed[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object +^ {
      def unapply(d: Def[_]): Option[(Rep[ShiftVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[ShiftVectorBoxedElem[_]] && method.getName == "$plus$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[ShiftVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object -^ {
      def unapply(d: Def[_]): Option[(Rep[ShiftVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[ShiftVectorBoxedElem[_]] && method.getName == "$minus$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[ShiftVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object *^ {
      def unapply(d: Def[_]): Option[(Rep[ShiftVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[ShiftVectorBoxedElem[_]] && method.getName == "$times$up" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[ShiftVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object /^ {
      def unapply(d: Def[_]): Option[(Rep[ShiftVectorBoxed[T]], Vector[T], Fractional[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, f, _*), _) if receiver.elem.isInstanceOf[ShiftVectorBoxedElem[_]] && method.getName == "$div$up" =>
          Some((receiver, vector, f)).asInstanceOf[Option[(Rep[ShiftVectorBoxed[T]], Vector[T], Fractional[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVectorBoxed[T]], Vector[T], Fractional[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object dot {
      def unapply(d: Def[_]): Option[(Rep[ShiftVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[ShiftVectorBoxedElem[_]] && method.getName == "dot" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[ShiftVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVectorBoxed[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object * {
      def unapply(d: Def[_]): Option[(Rep[ShiftVectorBoxed[T]], Matrix[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[ShiftVectorBoxedElem[_]] && method.getName == "$times" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[ShiftVectorBoxed[T]], Matrix[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVectorBoxed[T]], Matrix[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object pow_^ {
      def unapply(d: Def[_]): Option[(Rep[ShiftVectorBoxed[T]], DoubleRep, Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(order, n, _*), _) if receiver.elem.isInstanceOf[ShiftVectorBoxedElem[_]] && method.getName == "pow_$up" =>
          Some((receiver, order, n)).asInstanceOf[Option[(Rep[ShiftVectorBoxed[T]], DoubleRep, Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVectorBoxed[T]], DoubleRep, Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sum {
      def unapply(d: Def[_]): Option[(Rep[ShiftVectorBoxed[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[ShiftVectorBoxedElem[_]] && method.getName == "sum" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[ShiftVectorBoxed[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVectorBoxed[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object reduce {
      def unapply(d: Def[_]): Option[(Rep[ShiftVectorBoxed[T]], RepMonoid[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(m, _*), _) if receiver.elem.isInstanceOf[ShiftVectorBoxedElem[_]] && method.getName == "reduce" =>
          Some((receiver, m)).asInstanceOf[Option[(Rep[ShiftVectorBoxed[T]], RepMonoid[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVectorBoxed[T]], RepMonoid[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object euclideanNorm {
      def unapply(d: Def[_]): Option[(Rep[ShiftVectorBoxed[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(num, _*), _) if receiver.elem.isInstanceOf[ShiftVectorBoxedElem[_]] && method.getName == "euclideanNorm" =>
          Some((receiver, num)).asInstanceOf[Option[(Rep[ShiftVectorBoxed[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[ShiftVectorBoxed[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  def mkShiftVectorBoxed[T]
    (nonZeroItems: Coll[(Int, T)], constItem: Rep[T], length: IntRep)(implicit eT: Elem[T]): Rep[ShiftVectorBoxed[T]] =
    new ExpShiftVectorBoxed[T](nonZeroItems, constItem, length)
  def unmkShiftVectorBoxed[T](p: Rep[AbstractVector[T]]) = p.elem.asInstanceOf[Elem[_]] match {
    case _: ShiftVectorBoxedElem[T] @unchecked =>
      Some((p.asRep[ShiftVectorBoxed[T]].nonZeroItems, p.asRep[ShiftVectorBoxed[T]].constItem, p.asRep[ShiftVectorBoxed[T]].length))
    case _ =>
      None
  }

  object AbstractVectorMethods {
    object length {
      def unapply(d: Def[_]): Option[Rep[AbstractVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "length" =>
          Some(receiver).asInstanceOf[Option[Rep[AbstractVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[AbstractVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object items {
      def unapply(d: Def[_]): Option[Rep[AbstractVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "items" =>
          Some(receiver).asInstanceOf[Option[Rep[AbstractVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[AbstractVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object nonZeroIndices {
      def unapply(d: Def[_]): Option[Rep[AbstractVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "nonZeroIndices" =>
          Some(receiver).asInstanceOf[Option[Rep[AbstractVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[AbstractVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object nonZeroValues {
      def unapply(d: Def[_]): Option[Rep[AbstractVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "nonZeroValues" =>
          Some(receiver).asInstanceOf[Option[Rep[AbstractVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[AbstractVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object nonZeroItems {
      def unapply(d: Def[_]): Option[Rep[AbstractVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "nonZeroItems" =>
          Some(receiver).asInstanceOf[Option[Rep[AbstractVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[AbstractVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object zeroValue {
      def unapply(d: Def[_]): Option[Rep[AbstractVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "zeroValue" =>
          Some(receiver).asInstanceOf[Option[Rep[AbstractVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[AbstractVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object constItem {
      def unapply(d: Def[_]): Option[Rep[AbstractVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "constItem" =>
          Some(receiver).asInstanceOf[Option[Rep[AbstractVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[AbstractVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], IntRep) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(i, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "apply" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, i)).asInstanceOf[Option[(Rep[AbstractVector[T]], IntRep) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], IntRep) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object apply_apply_by_collection {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Coll[Int]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(is, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "apply" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "apply_by_collection" } =>
          Some((receiver, is)).asInstanceOf[Option[(Rep[AbstractVector[T]], Coll[Int]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Coll[Int]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object filterBy {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(f, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "filterBy" =>
          Some((receiver, f)).asInstanceOf[Option[(Rep[AbstractVector[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Rep[T @uncheckedVariance => Boolean]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object +^ {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "$plus$up" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[AbstractVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object elementwise_sum_collection_+^ {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Coll[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(coll, n, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "$plus$up" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "elementwise_sum_collection" } =>
          Some((receiver, coll, n)).asInstanceOf[Option[(Rep[AbstractVector[T]], Coll[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Coll[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object elementwise_sum_value_+^ {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Rep[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(value, n, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "$plus$up" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "elementwise_sum_value" } =>
          Some((receiver, value, n)).asInstanceOf[Option[(Rep[AbstractVector[T]], Rep[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Rep[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object -^ {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "$minus$up" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[AbstractVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object elementwise_diff_collection_-^ {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Coll[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(coll, n, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "$minus$up" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "elementwise_diff_collection" } =>
          Some((receiver, coll, n)).asInstanceOf[Option[(Rep[AbstractVector[T]], Coll[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Coll[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object elementwise_diff_value_-^ {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Rep[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(value, n, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "$minus$up" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "elementwise_diff_value" } =>
          Some((receiver, value, n)).asInstanceOf[Option[(Rep[AbstractVector[T]], Rep[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Rep[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object *^ {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "$times$up" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[AbstractVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object elementwise_mult_collection_*^ {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Coll[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(coll, n, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "$times$up" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "elementwise_mult_collection" } =>
          Some((receiver, coll, n)).asInstanceOf[Option[(Rep[AbstractVector[T]], Coll[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Coll[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object elementwise_mult_value_*^ {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Rep[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(value, n, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "$times$up" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "elementwise_mult_value" } =>
          Some((receiver, value, n)).asInstanceOf[Option[(Rep[AbstractVector[T]], Rep[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Rep[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object /^ {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Vector[T], Fractional[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, f, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "$div$up" && method.getAnnotation(classOf[scalan.OverloadId]) == null =>
          Some((receiver, vector, f)).asInstanceOf[Option[(Rep[AbstractVector[T]], Vector[T], Fractional[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Vector[T], Fractional[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object elementwise_div_collection_/^ {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Coll[T], Fractional[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(coll, f, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "$div$up" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "elementwise_div_collection" } =>
          Some((receiver, coll, f)).asInstanceOf[Option[(Rep[AbstractVector[T]], Coll[T], Fractional[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Coll[T], Fractional[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object elementwise_div_value_/^ {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Rep[T], Fractional[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(value, f, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "$div$up" && { val ann = method.getAnnotation(classOf[scalan.OverloadId]); ann != null && ann.value == "elementwise_div_value" } =>
          Some((receiver, value, f)).asInstanceOf[Option[(Rep[AbstractVector[T]], Rep[T], Fractional[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Rep[T], Fractional[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object * {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Matrix[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(matrix, n, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "$times" =>
          Some((receiver, matrix, n)).asInstanceOf[Option[(Rep[AbstractVector[T]], Matrix[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Matrix[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object pow_^ {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Rep[Double], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(order, n, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "pow_$up" =>
          Some((receiver, order, n)).asInstanceOf[Option[(Rep[AbstractVector[T]], Rep[Double], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Rep[Double], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object euclideanNorm {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(num, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "euclideanNorm" =>
          Some((receiver, num)).asInstanceOf[Option[(Rep[AbstractVector[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object sum {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(n, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "sum" =>
          Some((receiver, n)).asInstanceOf[Option[(Rep[AbstractVector[T]], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object reduce {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], RepMonoid[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(m, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "reduce" =>
          Some((receiver, m)).asInstanceOf[Option[(Rep[AbstractVector[T]], RepMonoid[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], RepMonoid[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object dot {
      def unapply(d: Def[_]): Option[(Rep[AbstractVector[T]], Vector[T], Numeric[T]) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(vector, n, _*), _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "dot" =>
          Some((receiver, vector, n)).asInstanceOf[Option[(Rep[AbstractVector[T]], Vector[T], Numeric[T]) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[AbstractVector[T]], Vector[T], Numeric[T]) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object nonZeroesLength {
      def unapply(d: Def[_]): Option[Rep[AbstractVector[T]] forSome {type T}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[AbstractVectorElem[_, _]] && method.getName == "nonZeroesLength" =>
          Some(receiver).asInstanceOf[Option[Rep[AbstractVector[T]] forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[AbstractVector[T]] forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  object AbstractVectorCompanionMethods {
    object zero {
      def unapply(d: Def[_]): Option[IntRep forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(len, _*), _) if receiver.elem == AbstractVectorCompanionElem && method.getName == "zero" =>
          Some(len).asInstanceOf[Option[IntRep forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[IntRep forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }

    object fromSparseData {
      def unapply(d: Def[_]): Option[(Coll[Int], Coll[T], IntRep) forSome {type T}] = d match {
        case MethodCall(receiver, method, Seq(nonZeroIndices, nonZeroValues, length, _*), _) if receiver.elem == AbstractVectorCompanionElem && method.getName == "fromSparseData" =>
          Some((nonZeroIndices, nonZeroValues, length)).asInstanceOf[Option[(Coll[Int], Coll[T], IntRep) forSome {type T}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Coll[Int], Coll[T], IntRep) forSome {type T}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }
}

object Vectors_Module extends scalan.ModuleInfo {
  val dump = "H4sIAAAAAAAAAN1YTWwbRRSetWM7jkOalgZKRUQIhgoEcYJAPQSpSp0EgkwSZUOFTFU0tsfOltnZzc44sjlUnCoEN8QViUpcEL0gTqhShYSQEAdOCCFx5lSKqh6oOIB4M/vj9c86iUmjgA+j3dl5b9583zfvzfj6bZTgDnqKlzHFbMYkAs/o6nmBi6y+xIQhmq9ZlToli6R6yvr6k7nPTn8VQ8eKKLmF+SKnRZR2H5YadvCsk+0CSmNWJlxYDhfo8YKaIVe2KCVlYVgsZ5hmXeASJbmCwcV8AQ2VrEpzG11BWgGNly1Wdoggep5izgn3+oeJjMgI3tPqvblmt+ZgObmKXGgVmw42BIQPc4y74zeIrTeZxZqmQGNeaGu2DAvGpAzTthzhT5ECd1tWxX8dYhg60InCZbyDczBFLacLx2A1sMzYuPw2rpFVGCKHD0HAnNDqZtNW7/ECGuFkGwBaMW2qeho2QggYeF4FMdPCZybAZ0bik9WJY2BqvIPlx3XHajSR+9PiCDVscPHsLi58D2SJVbLvXyy/eU/PmDFp3JChpNQKk+DosQg1KCoAx+82PuR3X752NoZGimjE4AslLhxcFmHKPbQymDFLqJgDALFTA7amo9hSsyzAmA5JpMuWaWMGnjwoR4EnapQNIQfLvlGPnQjoU8Im/lCtYWvBeqci1qt0k8eUrt965Lknf1t6I4Zi7VOkwaUOwnd8pyAnH40LQIIHRFK1xwTSNhXSskk3Wm2qTxABHGdu/V75dhZdjAUgenPujTdwkeA//5T58elzMTRcVCpfprhWBBz5EiXmmpO3mCiiYWuHOO6X1A6m8qknj6kKqeI6FR66YVjiAItAU5H70SYSs3mlfc0HIOPKd9ViJLu8nv1D//6j61KdDhp1v7gb9G/j7F+/jFWFEq5ACUMQk/v4DuVB/HuGfMT1q1smOT5917h07QOhwNUa7ft7rXQZuJxXdo/2wdnPM19cvTpx59O3HlT7Y7hkCBPb2dl97A5fzPdR/agdpbG8l2+VVubaP2YWCePE1XMEmLKdCL6pZhLYORmyzIcXMBkyC012SvMFoQYJFCObAbdSpLty2x3tZLA/JqN4U8g8tFE4SW+fuxlDiVdRogqy5wWUKFl1VvEhh6IkSEOc9/u0dsgBYuxgM4BY/aZQa70dEauBGa2DiYHyRxeQqANI0A/jYkV4EIKvOBTBPt57u0lSwmpiy7dIrjABbjqCcsPJqvbMvoSWl0EOJLSQ5aEJrSPayZDNS0eK/DE46hSJY62wigEZqFe2dNAT0btj3TFMOHXtkBe/ufH6nZurCVUIT3gF4AKmdeKegbyN0NoUMkVrsyA2EEo/XT3gRah87Tmd9/Ilm/X7pM9RHTb4YJlwImx6WArtivfoSnTUl2hUOe9Tdm2yWbcpeeHGn5fee/cVW9XwrpOZ60Y2zT7RHraijocZOm81SGV/sjrdZX9Y2uod+dEV2O45UGkjWgYHmaQOqB7vRZktVg68/ulbRvU/Uf92TS6y/XzwDPG/oHM8ROeA+zm0tGTPXBiH29G/ZzwiJ/bJwRl5EVrGpkGbc33n76ew1kwKAMi+D7cb90i93X8IDIoqtNpUa4w3MOXBBvnYq47UYJjWSMnBHh4Omo4onLp3QwRSrtz7ePWZH778VR3sRuRdE67hLPgPLHyga8cvUVhY5DQULQhO3jxVpP8AlQwsil4UAAA="
}
}

