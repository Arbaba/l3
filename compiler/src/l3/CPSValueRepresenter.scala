package l3

import l3.{SymbolicCPSTreeModule => H} 
import l3.{SymbolicCPSTreeModuleLow => L} 

object CPSValueRepresenter extends (H.Tree => L.Tree) {
  def apply(tree: H.Tree): L.Tree = tree match {
    case H.LetP(name: H.Name, p@L3IntAdd, Seq(x,y ) , body) => 
      tempLetP(CPSXOr, Seq(apply(x), L.AtomL(1))){ux => 
        L.LetP(name, CPSAdd, Seq(ux, apply(y)), apply(body))
      }
    case H.LetP(name, L3BlockAlloc(tag), Seq(arg), body) => 
      val t1 = Symbol.fresh("t1_Alloc")
      L.LetP(t1, CPSShiftRight, Seq(apply(arg), L.AtomL(1)), 
            L.LetP(name,CPSBlockAlloc(tag) , Seq(L.AtomN(t1)), apply(body)))
    

  }

  def tempLetP(p: L.ValuePrimitive, args: Seq[L.Atom])(body: L.AtomN => L.Tree): L.Tree = {
      val tmp = Symbol.fresh("ux")
      L.LetP(tmp, p,args, body(L.AtomN(tmp)))


    }
  def apply(a: H.Atom): L.Atom =  a match {
    case H.AtomN(n) => 
      L.AtomN(n)
    case H.AtomL(IntLit(v)) =>
      L.AtomL((v.toInt << 1) | 1) 
    case H.AtomL(BooleanLit(b)) => 
      val n = if(b) 26 else 12
      L.AtomL(n)
    case H.AtomL(UnitLit) =>
       L.AtomL(2)
    
    case _  => 
    ???
  }
}
