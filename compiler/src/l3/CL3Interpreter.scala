package l3

import scala.collection.mutable.{ Map => MutableMap }
import SymbolicCL3TreeModule._
import IO._

/**
  * A tree-based interpreter for the CL₃ language.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

object CL3Interpreter extends (Tree => TerminalPhaseResult) {
  def apply(program: Tree): TerminalPhaseResult =
    try {
      eval(program)(Map.empty)
      Right(0, None)
    } catch {
      case e: EvalHlt =>
        Right((e.retCode, None))
      case e: EvalErr =>
        val Seq(m1, ms @ _*) = e.messages
        Left((m1 +: ms.reverse).mkString("\n"))
    }

  // Values
  private sealed trait Value {
    override def toString(): String = this match {
      case BlockV(t, c) => s"<$t>[${c mkString ","}]"
      case IntV(i) => i.toString
      case CharV(c) => s"'${new String(Array(c), 0, 1)}'"
      case BoolV(b) => if (b) "#t" else "#f"
      case UnitV => "#u"
      case FunctionV(_, _, _) => "<function>"
    }
  }
  private case class BlockV(tag: L3BlockTag, contents: Array[Value])
      extends Value
  private case class IntV(i: L3Int) extends Value
  private case class CharV(c: L3Char) extends Value
  private case class BoolV(b: Boolean) extends Value
  private case object UnitV extends Value

  private case class FunctionV(args: Seq[Symbol], body: Tree, env: Env)
               extends Value

  // Environment
  private type Env = PartialFunction[Symbol, Value]

  // Error/halt handling (termination)
  private class EvalErr(val messages: Seq[String]) extends Exception()
  private class EvalHlt(val retCode: Int) extends Exception()

  private def error(pos: Position, msg: String): Nothing =
    throw new EvalErr(Seq(msg, s"  at $pos"))
  private def halt(r: Int): Nothing =
    throw new EvalHlt(r)

  private def validIndex(a: Array[Value], i: L3Int): Boolean =
    0 <= i.toInt && i.toInt < a.length

  private final def eval(tree: Tree)(implicit env: Env): Value = tree match {
    case Let(bdgs, body) =>
      eval(body)(Map(bdgs map { case (n, e) => n -> eval(e) } : _*) orElse env)

    case LetRec(funs, body) =>
      val recEnv = MutableMap[Symbol, Value]()
      val env1 = recEnv orElse env
      for (Fun(name, args, body) <- funs)
        recEnv(name) = BlockV(BlockTag.Function.id,
                              Array(FunctionV(args, body, env1)))
      eval(body)(env1)

    case If(cond, thenE, elseE) =>
      eval(cond) match {
        case BoolV(false) => eval(elseE)
        case _ => eval(thenE)
      }

    case App(fun, args) =>
      eval(fun) match {
        case BlockV(_, Array(FunctionV(cArgs, cBody, cEnv))) =>
          if (args.length != cArgs.length)
            error(tree.pos,
                  s"expected ${cArgs.length} arguments, got ${args.length}")
          try {
            eval(cBody)(Map(cArgs zip (args map eval) : _*) orElse cEnv)
          } catch {
            case e: EvalErr =>
              throw new EvalErr(e.messages :+ s"  at ${fun.pos}")
          }
        case _ => error(fun.pos, "function value expected")
      }

    case Prim(p, args) => (p, args map eval) match {
      case (L3BlockAlloc(t), Seq(IntV(i))) =>
        BlockV(t, Array.fill(i.toInt)(UnitV))
      case (L3BlockP, Seq(BlockV(_, _))) => BoolV(true)
      case (L3BlockP, Seq(_)) => BoolV(false)
      case (L3BlockTag, Seq(BlockV(t, _))) => IntV(L3Int(t))
      case (L3BlockLength, Seq(BlockV(_, c))) => IntV(L3Int(c.length))
      case (L3BlockGet, Seq(BlockV(_, v), IntV(i))) if (validIndex(v, i)) =>
        v(i.toInt)
      case (L3BlockSet, Seq(BlockV(_, v), IntV(i), o)) if (validIndex(v, i)) =>
        v(i.toInt) = o; UnitV

      case (L3IntP, Seq(IntV(_))) => BoolV(true)
      case (L3IntP, Seq(_)) => BoolV(false)

      case (L3IntAdd, Seq(IntV(v1), IntV(v2))) => IntV(v1 + v2)
      case (L3IntSub, Seq(IntV(v1), IntV(v2))) => IntV(v1 - v2)
      case (L3IntMul, Seq(IntV(v1), IntV(v2))) => IntV(v1 * v2)
      case (L3IntDiv, Seq(IntV(v1), IntV(v2))) => IntV(v1 / v2)
      case (L3IntMod, Seq(IntV(v1), IntV(v2))) => IntV(v1 % v2)

      case (L3IntShiftLeft, Seq(IntV(v1), IntV(v2))) => IntV(v1 << v2)
      case (L3IntShiftRight, Seq(IntV(v1), IntV(v2))) => IntV(v1 >> v2)
      case (L3IntBitwiseAnd, Seq(IntV(v1), IntV(v2))) => IntV(v1 & v2)
      case (L3IntBitwiseOr, Seq(IntV(v1), IntV(v2))) => IntV(v1 | v2)
      case (L3IntBitwiseXOr, Seq(IntV(v1), IntV(v2))) => IntV(v1 ^ v2)

      case (L3IntLt, Seq(IntV(v1), IntV(v2))) => BoolV(v1 < v2)
      case (L3IntLe, Seq(IntV(v1), IntV(v2))) => BoolV(v1 <= v2)
      case (L3Eq, Seq(v1, v2)) => BoolV(v1 == v2)

      case (L3IntToChar, Seq(IntV(i))) if Character.isValidCodePoint(i.toInt) =>
        CharV(i.toInt)

      case (L3CharP, Seq(CharV(_))) => BoolV(true)
      case (L3CharP, Seq(_)) => BoolV(false)

      case (L3ByteRead, Seq()) => IntV(L3Int(readByte()))
      case (L3ByteWrite, Seq(IntV(c))) => writeByte(c.toInt); UnitV

      case (L3CharToInt, Seq(CharV(c))) => IntV(L3Int(c))

      case (L3BoolP, Seq(BoolV(_))) => BoolV(true)
      case (L3BoolP, Seq(_)) => BoolV(false)

      case (L3UnitP, Seq(UnitV)) => BoolV(true)
      case (L3UnitP, Seq(_)) => BoolV(false)

      case (p, vs) =>
        error(tree.pos,
              s"""cannot apply primitive $p to values ${vs.mkString(", ")}""")
    }

    case Halt(arg) => eval(arg) match {
      case IntV(c) => halt(c.toInt)
      case c => error(tree.pos, s"halt with code $c")
    }

    case Ident(n) => env(n)

    case Lit(IntLit(i)) => IntV(i)
    case Lit(CharLit(c)) => CharV(c)
    case Lit(BooleanLit(b)) => BoolV(b)
    case Lit(UnitLit) => UnitV
  }
}
