package l3

import l3.{ SymbolicCL3TreeModule => S }
import l3.{ SymbolicCPSTreeModule => C }

object CL3ToCPSTranslator extends (S.Tree => C.Tree) {
  def apply(tree: S.Tree): C.Tree = {
    
    transform(tree){ v : C.Atom => 
      C.Halt(C.AtomL(IntLit(L3Int(0))))
    }
  }
  private def transform(tree: S.Tree)(ctx: C.Atom =>  C.Tree) : C.Tree = {
    implicit val pos = tree.pos
    tree match {
      case S.Ident(name) => ctx(C.AtomN(name))
      case S.Lit(v) => ctx(C.AtomL(v))
      case S.Let(Seq((n1, e1), otherArgs @ _*), e) => {
        transform(e1){ v1: C.Atom =>
          C.LetP(n1, L3Id, Seq(v1), transform(S.Let(otherArgs, e))(ctx))
        }
      }
      case S.Let(Seq(), e) => transform(e)(ctx)
    }
  }
}
