package l3

import PCRelativeASMInstructionModule._
import IO._

/**
  * An interpreter for the ASM language.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

object ASMInterpreter extends (Seq[Instruction] => TerminalPhaseResult) {
  def apply(program: Seq[Instruction]): TerminalPhaseResult =
    try {
      Right((interpret(program.toArray), None))
    } catch {
      case e: EvalError => Left(e.msg)
    }

  private class EvalError(val msg: String) extends Exception

  private def interpret(program: Array[Instruction]): Int = {
    import scala.language.implicitConversions
    import ASMRegisterFile.{ Ib, Lb, Ob }

    var PC: Bits32 = 0

    def error(msg: String): Nothing =
      throw new EvalError(s"${msg} (at PC = ${PC})")

    implicit def bitsToValue(i: Bits32): Value = BitsV(i)
    implicit def valueToBits(v: Value): Bits32 = v match {
      case BitsV(i) => i
      case BlockV(a, _, _) => a
      case _ => error(s"expected bits, found $v")
    }
    implicit def valueToBlock(v: Value): BlockV = v match {
      case b: BlockV => b
      case _ => error(s"expected block, found $v")
    }

    trait Value
    case class BitsV(value: Bits32) extends Value
    case class BlockV(addr: Bits32, tag: L3BlockTag, contents: Array[Value])
        extends Value
    case object UndefV extends Value

    var nextBlockAddr = 0
    def allocBlock(tag: L3BlockTag, size: Bits32): BlockV = {
      nextBlockAddr += 4
      BlockV(nextBlockAddr, tag, Array.fill(size)(UndefV))
    }

    val I0 = ASMRegisterFile.in(0)
    val I1 = ASMRegisterFile.in(1)
    val I2 = ASMRegisterFile.in(2)
    val I3 = ASMRegisterFile.in(3)
    val O0 = ASMRegisterFile.out(0)
    val O1 = ASMRegisterFile.out(1)
    val O2 = ASMRegisterFile.out(2)
    val O3 = ASMRegisterFile.out(3)

    object R {
      private val Cb: Value = {
        val constBlock = allocBlock(BlockTag.RegisterFrame.id, 32)
        for (i <- 0 until 32)
          constBlock.contents(i) = i
        constBlock
      }
      private var Ib: Value = UndefV
      private var Lb: Value = UndefV
      private var Ob: Value = UndefV

      private def checkedContents(r: ASMRegister): Array[Value] = {
        val contents = this(r.base).contents
        if (0 <= r.index && r.index <= contents.length)
          contents
        else
          error(s"unmapped register: $r")
      }

      def apply(r: ASMBaseRegister): Value = (r: @unchecked) match {
        case ASMRegisterFile.Cb => Cb
        case ASMRegisterFile.Ib => Ib
        case ASMRegisterFile.Lb => Lb
        case ASMRegisterFile.Ob => Ob
      }

      def apply(r: ASMRegister): Value =
        checkedContents(r)(r.index)

      def update(r: ASMRegister, v: Value): Unit =
        checkedContents(r)(r.index) = v

      def update(r: ASMBaseRegister, v: Value): Unit = (r: @unchecked) match {
        case ASMRegisterFile.Ib => Ib = v
        case ASMRegisterFile.Lb => Lb = v
        case ASMRegisterFile.Ob => Ob = v
      }
    }

    def call(targetPc: Bits32,
             savedIb: Value,
             savedLb: Value,
             savedOb: Value,
             retPc: Bits32): Unit = {
      // save caller context
      R(O0) = savedIb
      R(O1) = savedLb
      R(O2) = savedOb
      R(O3) = retPc
      // initialize callee context
      R(Ib) = R(Ob)
      R(Lb) = UndefV
      R(Ob) = UndefV
      PC = targetPc
    }

    def ret(retValue: Value): Unit = {
      PC = R(I3)
      R(Ob) = R(I2)
      R(Lb) = R(I1)
      R(Ib) = R(I0)
      R(O0) = retValue
    }

    while (true) {
      program(PC) match {
        case ADD(a, b, c) =>
          R(a) = R(b) + R(c)
          PC += 1

        case SUB(a, b, c) =>
          R(a) = R(b) - R(c)
          PC += 1

        case MUL(a, b, c) =>
          R(a) = R(b) * R(c)
          PC += 1

        case DIV(a, b, c) =>
          R(a) = R(b) / R(c)
          PC += 1

        case MOD(a, b, c) =>
          R(a) = R(b) % R(c)
          PC += 1

        case LSL(a, b, c) =>
          R(a) = R(b) << R(c)
          PC += 1

        case LSR(a, b, c) =>
          R(a) = R(b) >> R(c)
          PC += 1

        case AND(a, b, c) =>
          R(a) = R(b) & R(c)
          PC += 1

        case OR(a, b, c) =>
          R(a) = R(b) | R(c)
          PC += 1

        case XOR(a, b, c) =>
          R(a) = R(b) ^ R(c)
          PC += 1

        case JLT(a, b, d) =>
          PC += (if (R(a) < R(b)) d else 1)

        case JLE(a, b, d) =>
          PC += (if (R(a) <= R(b)) d else 1)

        case JEQ(a, b, d) =>
          PC += (if (R(a) == R(b)) d else 1)

        case JNE(a, b, d) =>
          PC += (if (R(a) != R(b)) d else 1)

        case JI(d) =>
          PC += d

        case CALL_NI(a) =>
          call(R(a) >> 2, R(Ib), R(Lb), R(Ob), PC + 1)

        case CALL_ND(d) =>
          call(PC + d, R(Ib), R(Lb), R(Ob), PC + 1)

        case CALL_TI(a) =>
          call(R(a) >> 2, R(I0), R(I1), R(I2), R(I3))

        case CALL_TD(d) =>
          call(PC + d, R(I0), R(I1), R(I2), R(I3))

        case RET(a) =>
          ret(R(a))

        case HALT(a) =>
          return R(a)

        case LDLO(a, s) =>
          R(a) = s
          PC += 1

        case LDHI(a, u) =>
          R(a) = (u << 16) | (R(a) & 0xFFFF)
          PC += 1

        case MOVE(a, b) =>
          R(a) = R(b)
          PC += 1

        case RALO(l, o) =>
          if (l > 0) R(Lb) = allocBlock(BlockTag.RegisterFrame.id, l)
          if (o > 0) R(Ob) = allocBlock(BlockTag.RegisterFrame.id, o)
          PC += 1

        case BALO(a, b, t) =>
          R(a) = allocBlock(t, R(b))
          PC += 1

        case BSIZ(a, b) =>
          R(a) = R(b).contents.length
          PC += 1

        case BTAG(a, b) =>
          R(a) = R(b).tag
          PC += 1

        case BGET(a, b, c) =>
          R(a) = R(b).contents(R(c))
          PC += 1

        case BSET(a, b, c) =>
          R(b).contents(R(c)) = R(a)
          PC += 1

        case BREA(a) =>
          R(a) = readByte()
          PC += 1

        case BWRI(a) =>
          writeByte(R(a))
          PC += 1
      }
    }
    0 // should not be needed
  }
}
