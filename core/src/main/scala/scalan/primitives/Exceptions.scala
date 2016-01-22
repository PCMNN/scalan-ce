package scalan.primitives

import scalan.{ScalanExp, ScalanStd, Scalan}

trait Exceptions { self: Scalan =>
  def THROW(msg: Rep[String]): Rep[Unit]
}

trait ExceptionsStd extends Exceptions { self: ScalanStd =>
  def THROW(msg: Rep[String]): Rep[Unit] = throw new Exception(msg)
}

trait ExceptionsExp extends Exceptions { self: ScalanExp =>
  case class ThrowException(msg: Rep[String]) extends BaseDef[Unit]
  def THROW(msg: Rep[String]): Rep[Unit] = ThrowException(msg)    
}
