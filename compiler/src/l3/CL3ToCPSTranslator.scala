package l3

import l3.{ SymbolicCL3TreeModule => S }
import l3.{ SymbolicCPSTreeModule => C }

object CL3ToCPSTranslator extends (S.Tree => C.Tree) {
  def apply(tree: S.Tree): C.Tree = {
    
    transform(tree){ v : C.Atom => 
      C.Halt(C.AtomL(IntLit(L3Int(0))))
    }
  }
  private def transform(tree: S.Tree)(implicit ctx: C.Atom =>  C.Tree) : C.Tree = {
    implicit val pos = tree.pos
    tree match {
      //f(name, args, body)
      //case S.LetRec(f, e) => C.LetF(, transform(e))
      case S.App(e, args) => transform(e) { v: C.Atom =>
        val c = Symbol.fresh("c")
        val r = Symbol.fresh("r")
        val z: C.Tree = C.LetC(Seq(C.Cnt(c, Seq(r), ctx(C.AtomN(r)))), C.AppF(v, c, Seq()))
        args.foldRight(z){
          case (symbolic, C.LetC(x, C.AppF(v, c, seq))) => transform(symbolic) {
            v1: C.Atom => C.LetC(x, C.AppF(v, c, Seq(v1) ++ seq)) 
          }
        }
      }
      case S.Ident(name) => ctx(C.AtomN(name))
      case S.Lit(v) => ctx(C.AtomL(v))
      case S.Let(Seq((n1, e1), otherArgs @ _*), e) => {
        transform(e1){ v1: C.Atom =>
          C.LetP(n1, L3Id, Seq(v1), transform(S.Let(otherArgs, e))(ctx))
        }
      }
      case S.Let(Seq(), e) => transform(e)
      //if-node with a primitive cond
      //L3TestPrimitive
      case S.If(S.Prim(p: L3TestPrimitive, Seq(e1)), e2, e3) => {
        val r = Symbol.fresh("r")
        val c = Symbol.fresh("c")
        val ct = Symbol.fresh("ct")
        val cf = Symbol.fresh("cf")
        C.LetC(
          Seq(C.Cnt(c, Seq(r), ctx(C.AtomN(r)))), 
          C.LetC(
            Seq(C.Cnt(ct, Seq(), transform(e2){ (v2: C.Atom) => 
              C.AppC(c, Seq(v2))
            })), C.LetC(
                Seq(C.Cnt(cf, Seq(), transform(e3){ (v3: C.Atom) => 
                  C.AppC(c, Seq(v3))
                }
                )), transform(e1) { v1: C.Atom => 
                  C.If(p, Seq(v1), ct, cf)
                }
              )
            )
          )
      }
      //if-node sugared
      //
      case S.If(e1, e2, e3) => transform(S.If(S.Prim(L3Eq, Seq(e1, S.Lit(BooleanLit(false)))), e3, e2))
      //halt(e) => halt()
      case S.Halt(e) => transform(e){v: C.Atom => C.Halt(v)}
    }
  }
}
