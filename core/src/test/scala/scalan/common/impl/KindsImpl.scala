package scalan.common

import scalan._
import scala.reflect.runtime.universe.{WeakTypeTag, weakTypeTag}
import scalan.meta.ScalanAst._

package impl {
// Abs -----------------------------------
trait KindsAbs extends Kinds with scalan.Scalan {
  self: KindsDsl =>

  // single proxy for each type family
  implicit def proxyKind[F[_], A](p: Rep[Kind[F, A]]): Kind[F, A] = {
    proxyOps[Kind[F, A]](p)(scala.reflect.classTag[Kind[F, A]])
  }

  // familyElem
  class KindElem[F[_], A, To <: Kind[F, A]](implicit _cF: Cont[F], _eA: Elem[A])
    extends EntityElem[To] {
    def cF = _cF
    def eA = _eA
    lazy val parent: Option[Elem[_]] = None
    lazy val entityDef: STraitOrClassDef = {
      val module = getModules("Kinds")
      module.entities.find(_.name == "Kind").get
    }
    lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map("F" -> Right(cF.asInstanceOf[SomeCont]), "A" -> Left(eA))
    }
    override def isEntityType = true
    override lazy val tag = {
      implicit val tagA = eA.tag
      weakTypeTag[Kind[F, A]].asInstanceOf[WeakTypeTag[To]]
    }
    override def convert(x: Rep[Reifiable[_]]) = {
      implicit val eTo: Elem[To] = this
      val conv = fun {x: Rep[Kind[F, A]] => convertKind(x) }
      tryConvert(element[Kind[F, A]], this, x, conv)
    }

    def convertKind(x: Rep[Kind[F, A]]): Rep[To] = {
      x.selfType1.asInstanceOf[Element[_]] match {
        case _: KindElem[_, _, _] => x.asRep[To]
        case e => !!!(s"Expected $x to have KindElem[_, _, _], but got $e")
      }
    }
    override def getDefaultRep: Rep[To] = ???
  }

  implicit def kindElement[F[_], A](implicit cF: Cont[F], eA: Elem[A]): Elem[Kind[F, A]] =
    cachedElem[KindElem[F, A, Kind[F, A]]](cF, eA)

  implicit case object KindCompanionElem extends CompanionElem[KindCompanionAbs] {
    lazy val tag = weakTypeTag[KindCompanionAbs]
    protected def getDefaultRep = Kind
  }

  abstract class KindCompanionAbs extends CompanionBase[KindCompanionAbs] with KindCompanion {
    override def toString = "Kind"
  }
  def Kind: Rep[KindCompanionAbs]
  implicit def proxyKindCompanion(p: Rep[KindCompanion]): KindCompanion =
    proxyOps[KindCompanion](p)

  // elem for concrete class
  class ReturnElem[F[_], A](val iso: Iso[ReturnData[F, A], Return[F, A]])(implicit eA: Elem[A], cF: Cont[F])
    extends KindElem[F, A, Return[F, A]]
    with ConcreteElem[ReturnData[F, A], Return[F, A]] {
    override lazy val parent: Option[Elem[_]] = Some(kindElement(container[F], element[A]))
    override lazy val entityDef = {
      val module = getModules("Kinds")
      module.concreteSClasses.find(_.name == "Return").get
    }
    override lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map("F" -> Right(cF.asInstanceOf[SomeCont]), "A" -> Left(eA))
    }

    override def convertKind(x: Rep[Kind[F, A]]) = // Converter is not generated by meta
!!!("Cannot convert from Kind to Return: missing fields List(a)")
    override def getDefaultRep = Return(element[A].defaultRepValue)
    override lazy val tag = {
      implicit val tagA = eA.tag
      weakTypeTag[Return[F, A]]
    }
  }

  // state representation type
  type ReturnData[F[_], A] = A

  // 3) Iso for concrete class
  class ReturnIso[F[_], A](implicit eA: Elem[A], cF: Cont[F])
    extends Iso[ReturnData[F, A], Return[F, A]] {
    override def from(p: Rep[Return[F, A]]) =
      p.a
    override def to(p: Rep[A]) = {
      val a = p
      Return(a)
    }
    lazy val eTo = new ReturnElem[F, A](this)
  }
  // 4) constructor and deconstructor
  abstract class ReturnCompanionAbs extends CompanionBase[ReturnCompanionAbs] with ReturnCompanion {
    override def toString = "Return"

    def apply[F[_], A](a: Rep[A])(implicit eA: Elem[A], cF: Cont[F]): Rep[Return[F, A]] =
      mkReturn(a)
  }
  object ReturnMatcher {
    def unapply[F[_], A](p: Rep[Kind[F, A]]) = unmkReturn(p)
  }
  def Return: Rep[ReturnCompanionAbs]
  implicit def proxyReturnCompanion(p: Rep[ReturnCompanionAbs]): ReturnCompanionAbs = {
    proxyOps[ReturnCompanionAbs](p)
  }

  implicit case object ReturnCompanionElem extends CompanionElem[ReturnCompanionAbs] {
    lazy val tag = weakTypeTag[ReturnCompanionAbs]
    protected def getDefaultRep = Return
  }

  implicit def proxyReturn[F[_], A](p: Rep[Return[F, A]]): Return[F, A] =
    proxyOps[Return[F, A]](p)

  implicit class ExtendedReturn[F[_], A](p: Rep[Return[F, A]])(implicit eA: Elem[A], cF: Cont[F]) {
    def toData: Rep[ReturnData[F, A]] = isoReturn(eA, cF).from(p)
  }

  // 5) implicit resolution of Iso
  implicit def isoReturn[F[_], A](implicit eA: Elem[A], cF: Cont[F]): Iso[ReturnData[F, A], Return[F, A]] =
    cachedIso[ReturnIso[F, A]](eA, cF)

  // 6) smart constructor and deconstructor
  def mkReturn[F[_], A](a: Rep[A])(implicit eA: Elem[A], cF: Cont[F]): Rep[Return[F, A]]
  def unmkReturn[F[_], A](p: Rep[Kind[F, A]]): Option[(Rep[A])]

  // elem for concrete class
  class BindElem[F[_], S, B](val iso: Iso[BindData[F, S, B], Bind[F, S, B]])(implicit eS: Elem[S], eA: Elem[B], cF: Cont[F])
    extends KindElem[F, B, Bind[F, S, B]]
    with ConcreteElem[BindData[F, S, B], Bind[F, S, B]] {
    override lazy val parent: Option[Elem[_]] = Some(kindElement(container[F], element[B]))
    override lazy val entityDef = {
      val module = getModules("Kinds")
      module.concreteSClasses.find(_.name == "Bind").get
    }
    override lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map("F" -> Right(cF.asInstanceOf[SomeCont]), "S" -> Left(eS), "B" -> Left(eA))
    }

    override def convertKind(x: Rep[Kind[F, B]]) = // Converter is not generated by meta
!!!("Cannot convert from Kind to Bind: missing fields List(a, f)")
    override def getDefaultRep = Bind(element[Kind[F, S]].defaultRepValue, constFun[S, Kind[F, B]](element[Kind[F, B]].defaultRepValue))
    override lazy val tag = {
      implicit val tagS = eS.tag
      implicit val tagB = eA.tag
      weakTypeTag[Bind[F, S, B]]
    }
  }

  // state representation type
  type BindData[F[_], S, B] = (Kind[F, S], S => Kind[F, B])

  // 3) Iso for concrete class
  class BindIso[F[_], S, B](implicit eS: Elem[S], eA: Elem[B], cF: Cont[F])
    extends Iso[BindData[F, S, B], Bind[F, S, B]]()(pairElement(implicitly[Elem[Kind[F, S]]], implicitly[Elem[S => Kind[F, B]]])) {
    override def from(p: Rep[Bind[F, S, B]]) =
      (p.a, p.f)
    override def to(p: Rep[(Kind[F, S], S => Kind[F, B])]) = {
      val Pair(a, f) = p
      Bind(a, f)
    }
    lazy val eTo = new BindElem[F, S, B](this)
  }
  // 4) constructor and deconstructor
  abstract class BindCompanionAbs extends CompanionBase[BindCompanionAbs] with BindCompanion {
    override def toString = "Bind"
    def apply[F[_], S, B](p: Rep[BindData[F, S, B]])(implicit eS: Elem[S], eA: Elem[B], cF: Cont[F]): Rep[Bind[F, S, B]] =
      isoBind(eS, eA, cF).to(p)
    def apply[F[_], S, B](a: Rep[Kind[F, S]], f: Rep[S => Kind[F, B]])(implicit eS: Elem[S], eA: Elem[B], cF: Cont[F]): Rep[Bind[F, S, B]] =
      mkBind(a, f)
  }
  object BindMatcher {
    def unapply[F[_], S, B](p: Rep[Kind[F, B]]) = unmkBind(p)
  }
  def Bind: Rep[BindCompanionAbs]
  implicit def proxyBindCompanion(p: Rep[BindCompanionAbs]): BindCompanionAbs = {
    proxyOps[BindCompanionAbs](p)
  }

  implicit case object BindCompanionElem extends CompanionElem[BindCompanionAbs] {
    lazy val tag = weakTypeTag[BindCompanionAbs]
    protected def getDefaultRep = Bind
  }

  implicit def proxyBind[F[_], S, B](p: Rep[Bind[F, S, B]]): Bind[F, S, B] =
    proxyOps[Bind[F, S, B]](p)

  implicit class ExtendedBind[F[_], S, B](p: Rep[Bind[F, S, B]])(implicit eS: Elem[S], eA: Elem[B], cF: Cont[F]) {
    def toData: Rep[BindData[F, S, B]] = isoBind(eS, eA, cF).from(p)
  }

  // 5) implicit resolution of Iso
  implicit def isoBind[F[_], S, B](implicit eS: Elem[S], eA: Elem[B], cF: Cont[F]): Iso[BindData[F, S, B], Bind[F, S, B]] =
    cachedIso[BindIso[F, S, B]](eS, eA, cF)

  // 6) smart constructor and deconstructor
  def mkBind[F[_], S, B](a: Rep[Kind[F, S]], f: Rep[S => Kind[F, B]])(implicit eS: Elem[S], eA: Elem[B], cF: Cont[F]): Rep[Bind[F, S, B]]
  def unmkBind[F[_], S, B](p: Rep[Kind[F, B]]): Option[(Rep[Kind[F, S]], Rep[S => Kind[F, B]])]

  registerModule(scalan.meta.ScalanCodegen.loadModule(Kinds_Module.dump))
}

// Seq -----------------------------------
trait KindsSeq extends KindsDsl with scalan.ScalanSeq {
  self: KindsDslSeq =>
  lazy val Kind: Rep[KindCompanionAbs] = new KindCompanionAbs with UserTypeSeq[KindCompanionAbs] {
    lazy val selfType = element[KindCompanionAbs]
  }

  case class SeqReturn[F[_], A]
      (override val a: Rep[A])
      (implicit eA: Elem[A], cF: Cont[F])
    extends Return[F, A](a)
        with UserTypeSeq[Return[F, A]] {
    lazy val selfType = element[Return[F, A]]
  }
  lazy val Return = new ReturnCompanionAbs with UserTypeSeq[ReturnCompanionAbs] {
    lazy val selfType = element[ReturnCompanionAbs]
  }

  def mkReturn[F[_], A]
      (a: Rep[A])(implicit eA: Elem[A], cF: Cont[F]): Rep[Return[F, A]] =
      new SeqReturn[F, A](a)
  def unmkReturn[F[_], A](p: Rep[Kind[F, A]]) = p match {
    case p: Return[F, A] @unchecked =>
      Some((p.a))
    case _ => None
  }

  case class SeqBind[F[_], S, B]
      (override val a: Rep[Kind[F, S]], override val f: Rep[S => Kind[F, B]])
      (implicit eS: Elem[S], eA: Elem[B], cF: Cont[F])
    extends Bind[F, S, B](a, f)
        with UserTypeSeq[Bind[F, S, B]] {
    lazy val selfType = element[Bind[F, S, B]]
  }
  lazy val Bind = new BindCompanionAbs with UserTypeSeq[BindCompanionAbs] {
    lazy val selfType = element[BindCompanionAbs]
  }

  def mkBind[F[_], S, B]
      (a: Rep[Kind[F, S]], f: Rep[S => Kind[F, B]])(implicit eS: Elem[S], eA: Elem[B], cF: Cont[F]): Rep[Bind[F, S, B]] =
      new SeqBind[F, S, B](a, f)
  def unmkBind[F[_], S, B](p: Rep[Kind[F, B]]) = p match {
    case p: Bind[F, S, B] @unchecked =>
      Some((p.a, p.f))
    case _ => None
  }
}

// Exp -----------------------------------
trait KindsExp extends KindsDsl with scalan.ScalanExp {
  self: KindsDslExp =>
  lazy val Kind: Rep[KindCompanionAbs] = new KindCompanionAbs with UserTypeDef[KindCompanionAbs] {
    lazy val selfType = element[KindCompanionAbs]
    override def mirror(t: Transformer) = this
  }

  case class ExpReturn[F[_], A]
      (override val a: Rep[A])
      (implicit eA: Elem[A], cF: Cont[F])
    extends Return[F, A](a) with UserTypeDef[Return[F, A]] {
    lazy val selfType = element[Return[F, A]]
    override def mirror(t: Transformer) = ExpReturn[F, A](t(a))
  }

  lazy val Return: Rep[ReturnCompanionAbs] = new ReturnCompanionAbs with UserTypeDef[ReturnCompanionAbs] {
    lazy val selfType = element[ReturnCompanionAbs]
    override def mirror(t: Transformer) = this
  }

  object ReturnMethods {
    // WARNING: Cannot generate matcher for method `flatMap`: Method has function arguments f
  }

  object ReturnCompanionMethods {
  }

  def mkReturn[F[_], A]
    (a: Rep[A])(implicit eA: Elem[A], cF: Cont[F]): Rep[Return[F, A]] =
    new ExpReturn[F, A](a)
  def unmkReturn[F[_], A](p: Rep[Kind[F, A]]) = p.elem.asInstanceOf[Elem[_]] match {
    case _: ReturnElem[F, A] @unchecked =>
      Some((p.asRep[Return[F, A]].a))
    case _ =>
      None
  }

  case class ExpBind[F[_], S, B]
      (override val a: Rep[Kind[F, S]], override val f: Rep[S => Kind[F, B]])
      (implicit eS: Elem[S], eA: Elem[B], cF: Cont[F])
    extends Bind[F, S, B](a, f) with UserTypeDef[Bind[F, S, B]] {
    lazy val selfType = element[Bind[F, S, B]]
    override def mirror(t: Transformer) = ExpBind[F, S, B](t(a), t(f))
  }

  lazy val Bind: Rep[BindCompanionAbs] = new BindCompanionAbs with UserTypeDef[BindCompanionAbs] {
    lazy val selfType = element[BindCompanionAbs]
    override def mirror(t: Transformer) = this
  }

  object BindMethods {
    // WARNING: Cannot generate matcher for method `flatMap`: Method has function arguments f1
  }

  object BindCompanionMethods {
  }

  def mkBind[F[_], S, B]
    (a: Rep[Kind[F, S]], f: Rep[S => Kind[F, B]])(implicit eS: Elem[S], eA: Elem[B], cF: Cont[F]): Rep[Bind[F, S, B]] =
    new ExpBind[F, S, B](a, f)
  def unmkBind[F[_], S, B](p: Rep[Kind[F, B]]) = p.elem.asInstanceOf[Elem[_]] match {
    case _: BindElem[F, S, B] @unchecked =>
      Some((p.asRep[Bind[F, S, B]].a, p.asRep[Bind[F, S, B]].f))
    case _ =>
      None
  }

  object KindMethods {
    // WARNING: Cannot generate matcher for method `flatMap`: Method has function arguments f

    object mapBy {
      def unapply(d: Def[_]): Option[(Rep[Kind[F, A]], Rep[A => B]) forSome {type F[_]; type A; type B}] = d match {
        case MethodCall(receiver, method, Seq(f, _*), _) if (receiver.elem.asInstanceOf[Element[_]] match { case _: KindElem[_, _, _] => true; case _ => false }) && method.getName == "mapBy" =>
          Some((receiver, f)).asInstanceOf[Option[(Rep[Kind[F, A]], Rep[A => B]) forSome {type F[_]; type A; type B}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[(Rep[Kind[F, A]], Rep[A => B]) forSome {type F[_]; type A; type B}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  object KindCompanionMethods {
  }
}

object Kinds_Module {
  val packageName = "scalan.common"
  val name = "Kinds"
  val dump = "H4sIAAAAAAAAAL2WPYwbRRTH3+7Z57N95MKHgkIU7jiZQ4fAPtGkOInIdmwU4tydvCkiJyIar8fOhN3Zvd3xyaZIQQldREOBUPp0NFR0SIiCKgIkKgqqEIoISAXizXh3vb7z+pwg2GK0s/v2vTe/9/4ze+8hpH0PNnyTWIQXbSpI0VD3ZV8UjBoXTAwvO52+RS/Q7oenvjQv84qvw0oLFm8S/4JvtSA7uqkN3OjeoPsNyBJuUl84ni/glYaKUDIdy6KmYA4vMdvuC9K2aKnBfLHdgFTb6Qz34TZoDThpOtz0qKBG1SK+T/3g+RKVGbFonlXz4a47jsFLchWl2CqueIQJTB9jnBzZN6lrDLnDh7aAE0Fqu65MC20yzHYdT4QhMujuptMJpylO8AE817hFDkgJQ/RKhvAY7+GXeZeY75Me3UETaZ7ChH1qda8MXTVfaEDOp/sI6KLtWurJwAUArMBbKonimE8x4lOUfAoG9Rix2AdEvtzznMEQRpe2ADBw0cUbx7gIPdAa7xQ+um5ee2zkbV1+PJCpZNQKF9HRakI3qFIgx2+ad/xH79w9p0OuBTnml9u+8Igp4iUPaOUJ545QOUcAidfDaq0nVUtFKaPNoZbImo7tEo6eApTLWCeLmUxIY/lsOahOAvqMcGloqg1cLVrvWsJ6Vd9UiWXtPTj95qu/1q7qoE+GyKJLAxvfC50KSF1ivBO4luOKAK0+5iunZTWVQ3YwHjMzMomYvPbgt87XW3Bdj0gGgecrHrpI+z9+n7+/eV6HpZZq9bpFei2E6dcsau96VYeLFiw5B9QbvckcEEveTS1mpkO7pG+JAHGczQKyEbCWKEqXSnDbSgBaCCA/6uEdh9NCfa/wp/HtJ/dki3qwPHozUunf7NxfP53oCtW9SJSEbBdQ2YfgJ9POjVwajk2fXX/E3rv7sVBctcGkvnfbt1BQ2+q7l2cgDveZP1pb+u+nf/hchyySbDNhE7ewNac6/sOOh4jEeFhFfCtNKvoer8ajrY5b9sUY0Je0sFjKSIBOyyHplGygGfATHJj1yIHsvanSiVdPwOIoX+Ug6vuzSUVRCE41Gy9YD89/pUP6XUh3sZ39BqTbTp93QrZ44gg6EJXwmTbJFlkSj9gRS3WtwZiVTDaW/NtTLW4c5jHd7Ai2vDbJZY5dppLQ90dKCocqMktNc8Q1jsRNCNOdEsZDgSXWsd7n5v2Lnz6/cvbGz2orXuw4NmGqEc5gOT0UqyrXmWA/HKfzr7nF6W2ocTNJTs9UMMZTismYJaY42adSY+V4B0+uxpRcblyLyW19jD7kUJ1PILGqTjc4WsVY7E2YXFe2SVmXyR+lJ+726adL0C3zt8yl6S0T/k/833inr+rOpC80TCtAmH8gWjyw7OAs20Atrydo2QiOKTwrbz/+bOf17774Rek5Jw88PPp59PM93oEHh3aiJRUaf6VjqSIteQKqNP8BKrp859oMAAA="
}
}

trait KindsDsl extends impl.KindsAbs {self: KindsDsl =>}
trait KindsDslSeq extends impl.KindsSeq {self: KindsDslSeq =>}
trait KindsDslExp extends impl.KindsExp {self: KindsDslExp =>}
