package l3

import java.io.{ PrintWriter, OutputStreamWriter, FileOutputStream }
import java.nio.charset.StandardCharsets.UTF_8

import scala.util.Using.{resource => using}

import PCRelativeASMInstructionModule._

/**
  * Assembly program writer. Dumps a program to a textual file, in
  * which each line is composed of an encoded instruction represented
  * as a 32-bit hexadecimal value, followed by a textual
  * representation of the instruction.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

object ASMFileWriter extends (String => (Program => TerminalPhaseResult)) {
  def apply(fileName: String): (Program => TerminalPhaseResult) = { program =>
    using(new PrintWriter(
            new OutputStreamWriter(
              new FileOutputStream(fileName), UTF_8))) { outWriter =>
      for (instr <- program)
        outWriter.println(f"${encode(instr)}%08x  ${instr}%s")
    }
    Right((0, Some(s"Wrote assembly program to ${fileName}")))
  }

  private object Opcode extends Enumeration {
    val ADD, SUB, MUL, DIV, MOD = Value
    val LSL, LSR, AND, OR, XOR = Value
    val JLT, JLE, JEQ, JNE, JI = Value
    val CALL_NI, CALL_ND, CALL_TI, CALL_TD, RET, HALT = Value
    val LDLO, LDHI, MOVE = Value
    val RALO, BALO, BSIZ, BTAG, BGET, BSET = Value
    val BREA, BWRI = Value
  }

  private def encode(instr: Instruction): Int = instr match {
    case ADD(a, b, c) => packRRR(Opcode.ADD, a, b, c)
    case SUB(a, b, c) => packRRR(Opcode.SUB, a, b, c)
    case MUL(a, b, c) => packRRR(Opcode.MUL, a, b, c)
    case DIV(a, b, c) => packRRR(Opcode.DIV, a, b, c)
    case MOD(a, b, c) => packRRR(Opcode.MOD, a, b, c)

    case LSL(a, b, c) => packRRR(Opcode.LSL, a, b, c)
    case LSR(a, b, c) => packRRR(Opcode.LSR, a, b, c)
    case AND(a, b, c) => packRRR(Opcode.AND, a, b, c)
    case OR(a, b, c) => packRRR(Opcode.OR, a, b, c)
    case XOR(a, b, c) => packRRR(Opcode.XOR, a, b, c)

    case JLT(a, b, d) => packRRD(Opcode.JLT, a, b, d)
    case JLE(a, b, d) => packRRD(Opcode.JLE, a, b, d)
    case JEQ(a, b, d) => packRRD(Opcode.JEQ, a, b, d)
    case JNE(a, b, d) => packRRD(Opcode.JNE, a, b, d)
    case JI(d) => packD(Opcode.JI, d)

    case CALL_NI(r) => packR(Opcode.CALL_NI, r)
    case CALL_ND(d) => packD(Opcode.CALL_ND, d)
    case CALL_TI(r) => packR(Opcode.CALL_TI, r)
    case CALL_TD(d) => packD(Opcode.CALL_TD, d)
    case RET(r) => packR(Opcode.RET, r)
    case HALT(r) => packR(Opcode.HALT, r)

    case LDLO(a, s) =>
      pack(encOp(Opcode.LDLO), encSInt(s, 19), encReg(a))
    case LDHI(a, u) =>
      pack(encOp(Opcode.LDHI), pad(3), encUInt(u, 16), encReg(a))
    case MOVE(a, b) => packRR(Opcode.MOVE, a, b)

    case RALO(l, o) =>
      pack(encOp(Opcode.RALO), pad(11), encUInt(o, 8), encUInt(l, 8))
    case BALO(a, b, t) =>
      pack(encOp(Opcode.BALO), pad(3), encUInt(t, 8), encReg(b), encReg(a))
    case BSIZ(a, b) => packRR(Opcode.BSIZ, a, b)
    case BTAG(a, b) => packRR(Opcode.BTAG, a, b)
    case BGET(a, b, c) => packRRR(Opcode.BGET, a, b, c)
    case BSET(a, b, c) => packRRR(Opcode.BSET, a, b, c)

    case BREA(a) => packR(Opcode.BREA, a)
    case BWRI(a) => packR(Opcode.BWRI, a)
  }

  private type BitField = (Int, Int)

  private def packD(opcode: Opcode.Value, d: Int): Int =
    pack(encOp(opcode), encSInt(d, 27))

  private def packR(opcode: Opcode.Value, a: ASMRegister): Int =
    pack(encOp(opcode), pad(19), encReg(a))

  private def packRR(opcode: Opcode.Value,
                     a: ASMRegister, b: ASMRegister): Int =
    pack(encOp(opcode), pad(11), encReg(b), encReg(a))

  private def packRRR(opcode: Opcode.Value,
                      a: ASMRegister, b: ASMRegister, c: ASMRegister): Int =
    pack(encOp(opcode), pad(3), encReg(c), encReg(b), encReg(a))

  private def packRRD(opcode: Opcode.Value,
                      a: ASMRegister, b: ASMRegister, d: Int): Int =
    pack(encOp(opcode), encSInt(d, 11), encReg(b), encReg(a))

  private def encOp(opcode: Opcode.Value): BitField =
    encUInt(opcode.id, 5)

  private def encReg(r: ASMRegister): BitField = (r: @unchecked) match {
    case ASMRegister(ASMRegisterFile.Cb, i) => encUInt(0 * 32 + i, 8)
    case ASMRegister(ASMRegisterFile.Ib, i) => encUInt(1 * 32 + i, 8)
    case ASMRegister(ASMRegisterFile.Lb, i) => encUInt(2 * 32 + i, 8)
    case ASMRegister(ASMRegisterFile.Ob, i) => encUInt(7 * 32 + i, 8)
  }

  private def encUInt(i: Int, len: Int): BitField = {
    require(0 <= i && i < (1 << len))
    (i, len)
  }

  private def encSInt(i: Int, len: Int): BitField = {
    require(-(1 << (len - 1)) <= i && i < (1 << (len - 1)))
    (i & ((1 << len) - 1), len)
  }

  private def pad(len: Int): BitField =
    encUInt(0, len)

  private def pack(values: BitField*): Int = {
    var packed: Int = 0
    for ((value, length) <- values)
      packed = (packed << length) | value
    packed
  }
}
