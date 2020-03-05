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
      case S.LetRec(funs, body ) => 
        val c = Symbol.fresh("c")
      
        val fs  = funs.map(f => C.Fun(f.name, c, f.args, transform(f.body){v: C.Atom => C.AppC(c, Seq(v))})) 
      
        C.LetF(fs, transform(body){v: C.Atom => C.AppC(c, Seq(v))})
      case S.App(f, args) => 
        transform(f){v :C.Atom => 
          
          val (c, r) = (Symbol.fresh("c"), Symbol.fresh("r"))

          val appStacker =  (ei, C.LetC(x, AppF(cnt, seq))) : (S.Tree, C.LetC) =>transform(ei){vi => C.LetC(AppF(cnt, vi::seq))}
          args.foldRight(C.LetC(  Seq(Cnt(c, r, C.AtomN(r))),Appf(v, c , Seq())))(appStacker)
        }
      case S.Prim(S.L3TestPrimitive(name, arity), args) => C.If(L3TestPrimitive(Symbol.fresh(name), arity), args,  Lit(BooleanLit(true)), Lit(BooleanLit(false)))
      case S.Prim(S.L3Primitive(name, arity)  , args) =>
          val f = Symbol.fresh("f")
          val c = Symbol.fresh("c")
          val newArgs = args.map(transform)
          C.LetP(f, C.L3TestPrimitve(name, arity), newArgs, C.AppC(c, newArgs ))
          

    }

  }
}
