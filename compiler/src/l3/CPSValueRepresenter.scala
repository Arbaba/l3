package l3

import l3.{SymbolicCPSTreeModule => H} 
import l3.{SymbolicCPSTreeModuleLow => L} 

object CPSValueRepresenter extends (H.Tree => L.Tree) {
  val one = apply_(H.AtomL(IntLit(L3Int(1))))
  def apply(tree: H.Tree): L.Tree = tree match {
    case H.LetP(name: H.Name, p@L3IntAdd, Seq(x,y ) , body) => 
      tempLetP(CPSXOr, Seq(apply_(x), L.AtomL(1))){ux => 
        L.LetP(name, CPSAdd, Seq(ux, apply_(y)), apply(body))
      }
    case H.LetC(continuations, e) => L.LetC(continuations.map{
      case H.Cnt(ni, ai, ei) => L.Cnt(ni, ai, apply(ei))
    }, apply(e))
    case H.AppC(cntName, valueBindings) => L.AppC(cntName, valueBindings.map(apply_))
    case H.LetF(functions, body) => L.LetF(functions.map{
      case H.Fun(name, retC, args, body) => L.Fun(name, retC, args, apply(body))
    }, apply(body))
    case H.AppF(fun, retC, args) => L.AppF(apply_(fun), retC, args.map(apply_))
    //Arithmetic primitives
    case H.LetP(name, L3IntAdd, atoms@Seq(_, _), body) => 
      val t1 = Symbol.fresh("t1")
      L.LetP(t1, CPSAdd, atoms.map(apply_), 
        L.LetP(name, CPSSub, Seq(L.AtomN(t1), one),
          apply(body)
      ))
    case H.LetP(name, L3IntSub, atoms@Seq(_, _), body) => 
      val t1 = Symbol.fresh("t1")
      L.LetP(t1, CPSSub, atoms.map(apply_),
        L.LetP(name, CPSAdd, Seq(L.AtomN(t1), one), 
          apply(body)
        )
      )
    case H.LetP(name, L3IntMul, atoms@Seq(v1, v2), body) =>
      val n = Symbol.fresh("n")
      val m = Symbol.fresh("m")
      val x = Symbol.fresh("x")
      val t = Symbol.fresh("t")
      L.LetP(n, CPSSub, Seq(apply_(v1), one), 
        L.LetP(m, CPSShiftRight, Seq(apply_(v2), one), 
          L.LetP(x, CPSMul, Seq(L.AtomN(n), L.AtomN(m)), 
            L.LetP(t, CPSAdd, Seq(L.AtomN(x), one), 
              apply(body)
            )
          )
        )
      )
     /*
      2(([n]-1)/2 / ([m] - 1)/2) + 1
    = 2(([n] - 1) / ([m] - 1)) + 1
    = ([n] - 1) << 1 / ([m] - 1) + 1
    = ([n] - 1) 
     */ 
    //case H.LetP(name, )
    //Logical primitives
    case H.If(L3IntP, Seq(v), ct, cf) => 
      val t1 = Symbol.fresh("t1")
      L.LetP(t1, CPSAnd, Seq(L.AtomN(t1), apply_(v)), 
          L.If(CPSEq, 
            Seq(L.AtomN(t1), one),
              ct, cf))
    case H.If(L3IntLt, atoms@Seq(_, _), ct, cf) =>
      L.If(CPSLt, atoms.map(apply_), ct, cf) 
    case H.If(L3IntLe, atoms@Seq(_, _), ct, cf) =>
      L.If(CPSLe, atoms.map(apply_), ct, cf) 
    case H.If(L3Eq, atoms@Seq(_, _), ct, cf) => 
      L.If(CPSEq, atoms.map(apply_), ct, cf)
  }
/*
case object L3IntDiv extends L3ValuePrimitive("/", 2)
case object L3IntMod extends L3ValuePrimitive("%", 2)
*/
  def primitiveApply(testPrimitive: H.TestPrimitive): L.TestPrimitive = testPrimitive match {
      case L3BlockP => ???
      case L3IntP => ???
      case L3IntLt => CPSLt
      case L3IntLe => CPSLe
      case L3CharP => ???
      case L3BoolP => ???
      case L3UnitP => ???
      case L3Eq => CPSEq
    }

  def tempLetP(p: L.ValuePrimitive, args: Seq[L.Atom])(body: L.AtomN => L.Tree): L.Tree = {
      val tmp = Symbol.fresh("ux")
      L.LetP(tmp, p,args, body(L.AtomN(tmp)))
    }
  def apply_(a: H.Atom): L.Atom =  a match {
    case H.AtomN(n) => 
      L.AtomN(n)
    case H.AtomL(IntLit(v)) =>
      L.AtomL((v.toInt << 1) | 1) 
    case _ => 
    ???
  }
}
