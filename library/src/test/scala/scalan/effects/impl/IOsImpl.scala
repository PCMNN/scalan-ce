package scalan.examples

import scala.reflect.runtime.universe._
import scalan._
import scalan.monads._
import scala.reflect.runtime.universe.{WeakTypeTag, weakTypeTag}
import scalan.meta.ScalanAst._

package impl {
// Abs -----------------------------------
trait IOsAbs extends IOs with scalan.Scalan {
  self: IOsDsl =>

  // single proxy for each type family
  implicit def proxyIO[A](p: Rep[IO[A]]): IO[A] = {
    proxyOps[IO[A]](p)(scala.reflect.classTag[IO[A]])
  }

  // familyElem
  class IOElem[A, To <: IO[A]](implicit _eA: Elem[A])
    extends EntityElem[To] {
    def eA = _eA
    lazy val parent: Option[Elem[_]] = None
    lazy val entityDef: STraitOrClassDef = {
      val module = getModules("IOs")
      module.entities.find(_.name == "IO").get
    }
    lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map("A" -> Left(eA))
    }
    override def isEntityType = true
    override lazy val tag = {
      implicit val tagA = eA.tag
      weakTypeTag[IO[A]].asInstanceOf[WeakTypeTag[To]]
    }
    override def convert(x: Rep[Reifiable[_]]) = {
      implicit val eTo: Elem[To] = this
      val conv = fun {x: Rep[IO[A]] => convertIO(x) }
      tryConvert(element[IO[A]], this, x, conv)
    }

    def convertIO(x: Rep[IO[A]]): Rep[To] = {
      x.selfType1 match {
        case _: IOElem[_, _] => x.asRep[To]
        case e => !!!(s"Expected $x to have IOElem[_, _], but got $e")
      }
    }
    override def getDefaultRep: Rep[To] = ???
  }

  implicit def iOElement[A](implicit eA: Elem[A]): Elem[IO[A]] =
    cachedElem[IOElem[A, IO[A]]](eA)

  implicit case object IOCompanionElem extends CompanionElem[IOCompanionAbs] {
    lazy val tag = weakTypeTag[IOCompanionAbs]
    protected def getDefaultRep = IO
  }

  abstract class IOCompanionAbs extends CompanionBase[IOCompanionAbs] with IOCompanion {
    override def toString = "IO"
  }
  def IO: Rep[IOCompanionAbs]
  implicit def proxyIOCompanion(p: Rep[IOCompanion]): IOCompanion =
    proxyOps[IOCompanion](p)

  // elem for concrete class
  class ReadFileElem(val iso: Iso[ReadFileData, ReadFile])
    extends IOElem[List[String], ReadFile]
    with ConcreteElem[ReadFileData, ReadFile] {
    override lazy val parent: Option[Elem[_]] = Some(iOElement(listElement(StringElement)))
    override lazy val entityDef = {
      val module = getModules("IOs")
      module.concreteSClasses.find(_.name == "ReadFile").get
    }
    override lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map()
    }

    override def convertIO(x: Rep[IO[List[String]]]) = // Converter is not generated by meta
!!!("Cannot convert from IO to ReadFile: missing fields List(fileName)")
    override def getDefaultRep = ReadFile("")
    override lazy val tag = {
      weakTypeTag[ReadFile]
    }
  }

  // state representation type
  type ReadFileData = String

  // 3) Iso for concrete class
  class ReadFileIso
    extends Iso[ReadFileData, ReadFile] {
    override def from(p: Rep[ReadFile]) =
      p.fileName
    override def to(p: Rep[String]) = {
      val fileName = p
      ReadFile(fileName)
    }
    lazy val eTo = new ReadFileElem(this)
  }
  // 4) constructor and deconstructor
  abstract class ReadFileCompanionAbs extends CompanionBase[ReadFileCompanionAbs] with ReadFileCompanion {
    override def toString = "ReadFile"

    def apply(fileName: Rep[String]): Rep[ReadFile] =
      mkReadFile(fileName)
  }
  object ReadFileMatcher {
    def unapply(p: Rep[IO[List[String]]]) = unmkReadFile(p)
  }
  def ReadFile: Rep[ReadFileCompanionAbs]
  implicit def proxyReadFileCompanion(p: Rep[ReadFileCompanionAbs]): ReadFileCompanionAbs = {
    proxyOps[ReadFileCompanionAbs](p)
  }

  implicit case object ReadFileCompanionElem extends CompanionElem[ReadFileCompanionAbs] {
    lazy val tag = weakTypeTag[ReadFileCompanionAbs]
    protected def getDefaultRep = ReadFile
  }

  implicit def proxyReadFile(p: Rep[ReadFile]): ReadFile =
    proxyOps[ReadFile](p)

  implicit class ExtendedReadFile(p: Rep[ReadFile]) {
    def toData: Rep[ReadFileData] = isoReadFile.from(p)
  }

  // 5) implicit resolution of Iso
  implicit def isoReadFile: Iso[ReadFileData, ReadFile] =
    cachedIso[ReadFileIso]()

  // 6) smart constructor and deconstructor
  def mkReadFile(fileName: Rep[String]): Rep[ReadFile]
  def unmkReadFile(p: Rep[IO[List[String]]]): Option[(Rep[String])]

  // elem for concrete class
  class WriteFileElem(val iso: Iso[WriteFileData, WriteFile])
    extends IOElem[Unit, WriteFile]
    with ConcreteElem[WriteFileData, WriteFile] {
    override lazy val parent: Option[Elem[_]] = Some(iOElement(UnitElement))
    override lazy val entityDef = {
      val module = getModules("IOs")
      module.concreteSClasses.find(_.name == "WriteFile").get
    }
    override lazy val tyArgSubst: Map[String, TypeDesc] = {
      Map()
    }

    override def convertIO(x: Rep[IO[Unit]]) = // Converter is not generated by meta
!!!("Cannot convert from IO to WriteFile: missing fields List(fileName, lines)")
    override def getDefaultRep = WriteFile("", element[List[String]].defaultRepValue)
    override lazy val tag = {
      weakTypeTag[WriteFile]
    }
  }

  // state representation type
  type WriteFileData = (String, List[String])

  // 3) Iso for concrete class
  class WriteFileIso
    extends Iso[WriteFileData, WriteFile]()(pairElement(implicitly[Elem[String]], implicitly[Elem[List[String]]])) {
    override def from(p: Rep[WriteFile]) =
      (p.fileName, p.lines)
    override def to(p: Rep[(String, List[String])]) = {
      val Pair(fileName, lines) = p
      WriteFile(fileName, lines)
    }
    lazy val eTo = new WriteFileElem(this)
  }
  // 4) constructor and deconstructor
  abstract class WriteFileCompanionAbs extends CompanionBase[WriteFileCompanionAbs] with WriteFileCompanion {
    override def toString = "WriteFile"
    def apply(p: Rep[WriteFileData]): Rep[WriteFile] =
      isoWriteFile.to(p)
    def apply(fileName: Rep[String], lines: Rep[List[String]]): Rep[WriteFile] =
      mkWriteFile(fileName, lines)
  }
  object WriteFileMatcher {
    def unapply(p: Rep[IO[Unit]]) = unmkWriteFile(p)
  }
  def WriteFile: Rep[WriteFileCompanionAbs]
  implicit def proxyWriteFileCompanion(p: Rep[WriteFileCompanionAbs]): WriteFileCompanionAbs = {
    proxyOps[WriteFileCompanionAbs](p)
  }

  implicit case object WriteFileCompanionElem extends CompanionElem[WriteFileCompanionAbs] {
    lazy val tag = weakTypeTag[WriteFileCompanionAbs]
    protected def getDefaultRep = WriteFile
  }

  implicit def proxyWriteFile(p: Rep[WriteFile]): WriteFile =
    proxyOps[WriteFile](p)

  implicit class ExtendedWriteFile(p: Rep[WriteFile]) {
    def toData: Rep[WriteFileData] = isoWriteFile.from(p)
  }

  // 5) implicit resolution of Iso
  implicit def isoWriteFile: Iso[WriteFileData, WriteFile] =
    cachedIso[WriteFileIso]()

  // 6) smart constructor and deconstructor
  def mkWriteFile(fileName: Rep[String], lines: Rep[List[String]]): Rep[WriteFile]
  def unmkWriteFile(p: Rep[IO[Unit]]): Option[(Rep[String], Rep[List[String]])]

  registerModule(scalan.meta.ScalanCodegen.loadModule(IOs_Module.dump))
}

// Seq -----------------------------------
trait IOsSeq extends IOsDsl with scalan.ScalanSeq {
  self: IOsDslSeq =>
  lazy val IO: Rep[IOCompanionAbs] = new IOCompanionAbs with UserTypeSeq[IOCompanionAbs] {
    lazy val selfType = element[IOCompanionAbs]
  }

  case class SeqReadFile
      (override val fileName: Rep[String])

    extends ReadFile(fileName)
        with UserTypeSeq[ReadFile] {
    lazy val selfType = element[ReadFile]
  }
  lazy val ReadFile = new ReadFileCompanionAbs with UserTypeSeq[ReadFileCompanionAbs] {
    lazy val selfType = element[ReadFileCompanionAbs]
  }

  def mkReadFile
      (fileName: Rep[String]): Rep[ReadFile] =
      new SeqReadFile(fileName)
  def unmkReadFile(p: Rep[IO[List[String]]]) = p match {
    case p: ReadFile @unchecked =>
      Some((p.fileName))
    case _ => None
  }

  case class SeqWriteFile
      (override val fileName: Rep[String], override val lines: Rep[List[String]])

    extends WriteFile(fileName, lines)
        with UserTypeSeq[WriteFile] {
    lazy val selfType = element[WriteFile]
  }
  lazy val WriteFile = new WriteFileCompanionAbs with UserTypeSeq[WriteFileCompanionAbs] {
    lazy val selfType = element[WriteFileCompanionAbs]
  }

  def mkWriteFile
      (fileName: Rep[String], lines: Rep[List[String]]): Rep[WriteFile] =
      new SeqWriteFile(fileName, lines)
  def unmkWriteFile(p: Rep[IO[Unit]]) = p match {
    case p: WriteFile @unchecked =>
      Some((p.fileName, p.lines))
    case _ => None
  }
}

// Exp -----------------------------------
trait IOsExp extends IOsDsl with scalan.ScalanExp {
  self: IOsDslExp =>
  lazy val IO: Rep[IOCompanionAbs] = new IOCompanionAbs with UserTypeDef[IOCompanionAbs] {
    lazy val selfType = element[IOCompanionAbs]
    override def mirror(t: Transformer) = this
  }

  case class ExpReadFile
      (override val fileName: Rep[String])

    extends ReadFile(fileName) with UserTypeDef[ReadFile] {
    lazy val selfType = element[ReadFile]
    override def mirror(t: Transformer) = ExpReadFile(t(fileName))
  }

  lazy val ReadFile: Rep[ReadFileCompanionAbs] = new ReadFileCompanionAbs with UserTypeDef[ReadFileCompanionAbs] {
    lazy val selfType = element[ReadFileCompanionAbs]
    override def mirror(t: Transformer) = this
  }

  object ReadFileMethods {
    object toOper {
      def unapply(d: Def[_]): Option[Rep[ReadFile]] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[ReadFileElem] && method.getName == "toOper" =>
          Some(receiver).asInstanceOf[Option[Rep[ReadFile]]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[ReadFile]] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  object ReadFileCompanionMethods {
  }

  def mkReadFile
    (fileName: Rep[String]): Rep[ReadFile] =
    new ExpReadFile(fileName)
  def unmkReadFile(p: Rep[IO[List[String]]]) = p.elem.asInstanceOf[Elem[_]] match {
    case _: ReadFileElem @unchecked =>
      Some((p.asRep[ReadFile].fileName))
    case _ =>
      None
  }

  case class ExpWriteFile
      (override val fileName: Rep[String], override val lines: Rep[List[String]])

    extends WriteFile(fileName, lines) with UserTypeDef[WriteFile] {
    lazy val selfType = element[WriteFile]
    override def mirror(t: Transformer) = ExpWriteFile(t(fileName), t(lines))
  }

  lazy val WriteFile: Rep[WriteFileCompanionAbs] = new WriteFileCompanionAbs with UserTypeDef[WriteFileCompanionAbs] {
    lazy val selfType = element[WriteFileCompanionAbs]
    override def mirror(t: Transformer) = this
  }

  object WriteFileMethods {
    object toOper {
      def unapply(d: Def[_]): Option[Rep[WriteFile]] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[WriteFileElem] && method.getName == "toOper" =>
          Some(receiver).asInstanceOf[Option[Rep[WriteFile]]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[WriteFile]] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  object WriteFileCompanionMethods {
  }

  def mkWriteFile
    (fileName: Rep[String], lines: Rep[List[String]]): Rep[WriteFile] =
    new ExpWriteFile(fileName, lines)
  def unmkWriteFile(p: Rep[IO[Unit]]) = p.elem.asInstanceOf[Elem[_]] match {
    case _: WriteFileElem @unchecked =>
      Some((p.asRep[WriteFile].fileName, p.asRep[WriteFile].lines))
    case _ =>
      None
  }

  object IOMethods {
    object toOper {
      def unapply(d: Def[_]): Option[Rep[IO[A]] forSome {type A}] = d match {
        case MethodCall(receiver, method, _, _) if receiver.elem.isInstanceOf[IOElem[_, _]] && method.getName == "toOper" =>
          Some(receiver).asInstanceOf[Option[Rep[IO[A]] forSome {type A}]]
        case _ => None
      }
      def unapply(exp: Exp[_]): Option[Rep[IO[A]] forSome {type A}] = exp match {
        case Def(d) => unapply(d)
        case _ => None
      }
    }
  }

  object IOCompanionMethods {
  }
}

object IOs_Module {
  val packageName = "scalan.examples"
  val name = "IOs"
  val dump = "H4sIAAAAAAAAALVWTWwbRRSeXcd2bEdNG6GgIlWkxhBagR0hoR5yqNLUQUHbOPK2FJkKabweu1NmZzc742jNoQeOcENcEeq9Ny5ISL0gJMSBEwIkzpxKEaoKPYH6dvbHu4k3+IIPo53ZN+/ne9/3vPcfoaLw0CvCwgzzpk0kbprqeUvIhtnmksrJNWcwZuQqGX60+pV1jV8ROlruodJtLK4K1kOV8KHtu8mzSQ4MVMHcIkI6npDovKEitCyHMWJJ6vAWte2xxH1GWgYVctNAC31nMDlAd5FmoNOWwy2PSGJuMywEEdH5Igkyosm+ovaTjjuNwVtBFa1UFdc9TCWkDzFOh/Zd4poT7vCJLdGpKLWOG6QFNmVqu44n4xBlcHfbGcTbBY7hAK0Yd/AhbkGIUcuUHuUjuFlzsfUBHpE9MAnMFyBhQdjw+sRV+4KBqoIcAEC7tsvUie8ihKADb6gkmlN8mgk+zQCfhkk8ihn9EAcv9z3Hn6DwpxUQ8l1w8dp/uIg9kDYfND6+Zb331KzZenDZD1IpqwpL4OjFHDaoVgCO33U/FY/fundJR9UeqlKx1RfSw5ZMtzxCq4Y5d6TKOQEQeyPoVj2vWyrKFtgcoUTFcmwXc/AUQbkEfWLUojIwDs6Wou7kQF+WLolNNd/VknrXcupVvNnGjO0/PPv6y7+339WRng1RAZcmEN+LnUqk73Yix8G6LMEMsE9ivZQXyyX7HrWB24fkzW++vvHng72iCrcyIEM8ZvIdzMYkZFoUfJqIiluvS1SaGlT8o2v5hFIT0Ncf/jH4dgPd0pNWRZXNxw5wURS//FT78cJlHS32lJZ2GB71oFuizYjd8bYdLnto0TkkXvimfIhZ8DSTLeWo/KiHafALAL5Ea7mqd0nQmU2lMC0GoBaKZM/hpLGz3/jb/P6z+4EGPLQUvgnHwL/00j+/nhpKJQ+JFoeUKVXHTS3ABAkRCZbnZ0FdDf2Zjk3O1B/T9+99IhWomp+dHp3+HZDrprp3/gR84yn2V29Df3L25y90VAEY+1Ta2G1szKm9/1FPSBWeXeqA3ZkuwYMdwG87Ha8+HTkvqEcAOTY88r6mZQWVVdgqHLx6AWR2g1N5vA8qQMr8XEIGFWXe1s6+W2SUE3H84gzpz6RJOsl1tV7MQ3HlpkclmQfGSmI5NUgVUYriZDOtdAkd0uCv4iSs4UDbSjk8Vsnc5dR2OzPqCMen2ifj5lz+wATyrXaN59ijyw90VHwbFYcwRYSBin1nzAcxq+FLQhJfXonPtCyrgcXYw3bCYvVbQ9Okcms2sviCYQHQkmg5ypj4GAQV8WMdSqnnlGJGugJx3336+d7FH778TY3+aqBQGFQ8+RZJj/xsX0oQGr4rUokC/QLBqiSfAW8PMmrnCQAA"
}
}

