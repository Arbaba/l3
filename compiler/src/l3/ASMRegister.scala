package l3

/**
  * An L₃VM base register.
  */
case class ASMBaseRegister(initial: Char) {
  override def toString: String = s"${initial}b"
}

/**
  * An L₃VM pseudo-register.
  */
case class ASMRegister(base: ASMBaseRegister, index: Int) {
  override def toString: String = s"${base.initial}${index}"
}

/**
  * The full L₃VM register file.
  */
object ASMRegisterFile {
  val Cb = ASMBaseRegister('C')
  val Ib = ASMBaseRegister('I')
  val Lb = ASMBaseRegister('L')
  val Ob = ASMBaseRegister('O')

  val const = for (i <- 0 until (1 * 32)) yield ASMRegister(Cb, i)
  val in    = for (i <- 0 until (1 * 32)) yield ASMRegister(Ib, i)
  val local = for (i <- 0 until (5 * 32)) yield ASMRegister(Lb, i)
  val out   = for (i <- 0 until (1 * 32)) yield ASMRegister(Ob, i)
}
