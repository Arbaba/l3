package l3

import scala.annotation.tailrec
import scala.collection.mutable.{ Map => MutableMap }
import IO._

/**
  * A tree-based interpreter for the CPS languages.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

sealed abstract class CPSInterpreter[M <: CPSTreeModule](
  protected val treeModule: M,
  log: M#Tree => Unit = { _ : M#Tree => () }) {

  import treeModule._

  def apply(tree: Tree): TerminalPhaseResult =
    Right((eval(tree, emptyEnv), None))

  protected sealed trait Value
  protected case class FunV(retC: Name, args: Seq[Name], body: Tree, env: Env)
      extends Value
  protected case class CntV(args: Seq[Name], body: Tree, env: Env)
      extends Value

  protected type Env = PartialFunction[Name, Value]
  protected val emptyEnv: Env = Map.empty

  @tailrec
  private def eval(tree: Tree, env: Env): Int = {
    def resolve(a: Atom): Value = a match {
      case AtomN(n) => env(n)
      case AtomL(l) => evalLit(l)
    }

    log(tree)

    (tree: @unchecked) match {
      case LetP(name, prim, args, body) =>
        eval(body, Map(name->evalValuePrim(prim, args map resolve)) orElse env)

      case LetC(cnts, body) =>
        val recEnv = MutableMap[Name, Value]()
        val env1 = recEnv orElse env
        for (Cnt(name, args, body) <- cnts)
          recEnv(name) = CntV(args, body, env1)
        eval(body, env1)

      case LetF(funs, body) =>
        val recEnv = MutableMap[Name, Value]()
        val env1 = recEnv orElse env
        for (Fun(name, retC, args, body) <- funs)
          recEnv(name) = wrapFunV(FunV(retC, args, body, env1))
        eval(body, env1)

      case AppC(cnt, args) =>
        val CntV(cArgs, cBody, cEnv) = env(cnt)
        assume(cArgs.length == args.length)
        eval(cBody, (cArgs zip (args map resolve)).toMap orElse cEnv)

      case AppF(fun, retC, args) =>
        val FunV(fRetC, fArgs, fBody, fEnv) = unwrapFunV(resolve(fun))
        assume(fArgs.length == args.length)
        val rArgs = args map resolve
        val env1 = ((fRetC +: fArgs) zip (env(retC) +: rArgs)).toMap orElse fEnv
        eval(fBody, env1)

      case If(cond, args, thenC, elseC) =>
        val cnt = if (evalTestPrim(cond, args map resolve)) thenC else elseC
        val cntV = env(cnt).asInstanceOf[CntV]
        eval(cntV.body, cntV.env)

      case Halt(name) =>
        extractInt(resolve(name))
    }
  }

  protected def extractInt(v: Value): Int

  protected def wrapFunV(funV: FunV): Value
  protected def unwrapFunV(v: Value): FunV

  protected def evalLit(l: Literal): Value
  protected def evalValuePrim(p: ValuePrimitive, args: Seq[Value]): Value
  protected def evalTestPrim(p: TestPrimitive, args: Seq[Value]): Boolean
}

object CPSInterpreterHigh extends CPSInterpreter(SymbolicCPSTreeModule)
    with (SymbolicCPSTreeModule.Tree => TerminalPhaseResult) {
  import treeModule._

  private case class BlockV(tag: L3BlockTag, contents: Array[Value])
      extends Value
  private case class IntV(value: L3Int) extends Value
  private case class CharV(value: L3Char) extends Value
  private case class BooleanV(value: Boolean) extends Value
  private case object UnitV extends Value

  protected def extractInt(v: Value): Int = v match { case IntV(i) => i.toInt }

  protected def wrapFunV(funV: FunV): Value =
    BlockV(BlockTag.Function.id, Array(funV))
  protected def unwrapFunV(v: Value): FunV = v match {
    case BlockV(id, Array(funV: FunV)) if id == BlockTag.Function.id => funV
  }

  protected def evalLit(l: Literal): Value = l match {
    case IntLit(i) => IntV(i)
    case CharLit(c) => CharV(c)
    case BooleanLit(b) => BooleanV(b)
    case UnitLit => UnitV
  }

  protected def evalValuePrim(p: ValuePrimitive, args: Seq[Value]): Value =
    (p, args) match {
      case (L3BlockAlloc(t), Seq(IntV(i))) =>
        BlockV(t, Array.fill(i.toInt)(UnitV))
      case (L3BlockTag, Seq(BlockV(t, _))) => IntV(L3Int(t))
      case (L3BlockLength, Seq(BlockV(_, c))) => IntV(L3Int(c.length))
      case (L3BlockGet, Seq(BlockV(_, v), IntV(i))) => v(i.toInt)
      case (L3BlockSet, Seq(BlockV(_, v), IntV(i), o)) => v(i.toInt) = o; UnitV

      case (L3IntAdd, Seq(IntV(v1), IntV(v2))) => IntV(v1 + v2)
      case (L3IntSub, Seq(IntV(v1), IntV(v2))) => IntV(v1 - v2)
      case (L3IntMul, Seq(IntV(v1), IntV(v2))) => IntV(v1 * v2)
      case (L3IntDiv, Seq(IntV(v1), IntV(v2))) => IntV(v1 / v2)
      case (L3IntMod, Seq(IntV(v1), IntV(v2))) => IntV(v1 % v2)
      case (L3IntToChar, Seq(IntV(v))) => CharV(v.toInt)

      case (L3IntShiftLeft, Seq(IntV(v1), IntV(v2))) => IntV(v1 << v2)
      case (L3IntShiftRight, Seq(IntV(v1), IntV(v2))) => IntV(v1 >> v2)
      case (L3IntBitwiseAnd, Seq(IntV(v1), IntV(v2))) => IntV(v1 & v2)
      case (L3IntBitwiseOr, Seq(IntV(v1), IntV(v2))) => IntV(v1 | v2)
      case (L3IntBitwiseXOr, Seq(IntV(v1), IntV(v2))) => IntV(v1 ^ v2)

      case (L3ByteRead, Seq()) => IntV(L3Int(readByte()))
      case (L3ByteWrite, Seq(IntV(c))) => writeByte(c.toInt); UnitV
      case (L3CharToInt, Seq(CharV(c))) => IntV(L3Int(c))

      case (L3Id, Seq(v)) => v
    }

  protected def evalTestPrim(p: TestPrimitive, args: Seq[Value]): Boolean =
    (p, args) match {
      case (L3BlockP, Seq(BlockV(_, _))) => true
      case (L3BlockP, Seq(_)) => false

      case (L3IntP, Seq(IntV(_))) => true
      case (L3IntP, Seq(_)) => false
      case (L3IntLt, Seq(IntV(v1), IntV(v2))) => v1 < v2
      case (L3IntLe, Seq(IntV(v1), IntV(v2))) => v1 <= v2

      case (L3CharP, Seq(CharV(_))) => true
      case (L3CharP, Seq(_)) => false

      case (L3BoolP, Seq(BooleanV(_))) => true
      case (L3BoolP, Seq(_)) => false

      case (L3UnitP, Seq(UnitV)) => true
      case (L3UnitP, Seq(_)) => false

      case (L3Eq, Seq(v1, v2)) => v1 == v2
    }
}
