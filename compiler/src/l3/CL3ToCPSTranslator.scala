package l3

import l3.{ SymbolicCL3TreeModule => S }
import l3.{ SymbolicCPSTreeModule => C }

object CL3ToCPSTranslator extends (S.Tree => C.Tree) {
  def apply(tree: S.Tree): C.Tree = 
    transform(tree){ v : C.Atom => 
    //(halt 0)
    C.Halt(C.Atom(IntLit(L3Int(0))))
  }
  private def transform(tree: S.Tree)(ctx: C.Atom =>  C.Tree) : C.Tree = tree match {
    case Ident(name) => 
      ctx(C.AtomN(name))
    case Lit(v) => 
      ctx(C.AtomL(v))
  }
}
