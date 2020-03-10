package l3

import l3.{ SymbolicCL3TreeModule => S }
import l3.{ SymbolicCPSTreeModule => C }

object CL3ToCPSTranslator extends (S.Tree => C.Tree) {
  val stub = C.Halt(C.AtomL(IntLit(L3Int(0))))
  def apply(tree: S.Tree): C.Tree = {
    //println(tree)
    transform(tree){ v : C.Atom => 
      C.Halt(C.AtomL(IntLit(L3Int(0))))
    }
  }
  var cnt = 0

  private def atomStacker(trees: Seq[S.Tree], acc: Seq[C.Atom])( ctx: Seq[C.Atom] => C.Tree): C.Tree = trees match {
    case Seq() => ctx(acc)
    case Seq(head, others@_*) => 
      transform(head){v: C.Atom => {
          atomStacker(others, v +: acc)(ctx)
        }
      }
  }
  private def tail(t: S.Tree, c: Symbol): C.Tree = t match {
    case _ => stub//case S.If()
  }

  private def cond(t: S.Tree, ct: Symbol, cf: Symbol): C.Tree = {
    stub
  }
  private def nonTail(t: S.Tree)(ctx: C.Atom => C.Tree): C.Tree = {
    implicit val pos = t.pos
    t match {
      case S.Ident(name) => ctx(C.AtomN(name))
      case S.Lit(v) => ctx(C.AtomL(v))
      case S.Halt(e) => nonTail(e){v: C.Atom => C.Halt(v)}
      case prim@S.Prim(p: L3TestPrimitive, args) =>
        nonTail{
          S.If(prim, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false)))
        }(ctx)
      case S.Prim(p: L3ValuePrimitive, args) =>
        val nil :Seq[C.Atom] = Seq()
        val r = Symbol.fresh("primRes")
        val context = {atoms: Seq[C.Atom] => {
          C.LetP(r,p, atoms, ctx(C.AtomN(r)))
        }}
        atomStacker(args.reverse, nil)(context)  
      case S.LetRec(funs, body) => 
        val fs  = funs.map(f => {
          val c = Symbol.fresh("c_LetRec")
          C.Fun(f.name, c, f.args, tail(f.body, c))
        })
        C.LetF(fs, nonTail(body)(ctx))
      case S.Let(seq, S.Let(otherLet, body)) => 
        nonTail(S.Let(seq ++ otherLet, body))(ctx)
      case S.Let(Seq((n1, e1), otherArgs @ _*), e) => {
        nonTail(e1){ v1: C.Atom =>
          C.LetP(n1, L3Id, Seq(v1), nonTail(S.Let(otherArgs, e))(ctx))
        }
      }
      case S.Let(Seq(), e) => 
        nonTail(e)(ctx)
      case S.If(S.Prim(p: L3TestPrimitive, e), e2, e3) => {
        val nil: Seq[C.Atom] = Seq()
    
        val r = Symbol.fresh("r_If")
        val c = Symbol.fresh("c_If")
        val ct = Symbol.fresh("ct")
        val cf = Symbol.fresh("cf")
  
        val plugin = C.Cnt(c, Seq(r), ctx(C.AtomN(r)))
        val thenCnt = C.Cnt(ct, Seq(), tail(e2, ct)) // { v2: C.Atom =>C.AppC(c, Seq(v2))}
        val elseCnt = C.Cnt(cf, Seq(),tail(e3, cf)) // { v3: C.Atom =>C.AppC(c, Seq(v3))}

        C.LetC(Seq(plugin),             
          C.LetC(Seq(thenCnt),
            C.LetC(Seq(elseCnt), 
              atomStacker(e.reverse, nil){atoms: Seq[C.Atom] => 
                    C.If(p, atoms, ct, cf)
              })))
      }
      case S.If(e1, e2, e3) => {
        nonTail(S.If(S.Prim(L3Eq, Seq(e1, S.Lit(BooleanLit(false)))), e3, e2))(ctx)
      }
      case S.App(e, args) => 
        val nil :Seq[C.Atom] = Seq()
        val c = Symbol.fresh("c_App")
        val r = Symbol.fresh("r_App")
        val cnt = C.Cnt(c, Seq(r), ctx(C.AtomN(r)))
        val context = {atoms: Seq[C.Atom] => {
            val body = nonTail(e){v: C.Atom =>         
              C.AppF(v, c, atoms)
            }
            C.LetC(Seq(cnt),body)
          }
        }
        atomStacker(args.reverse, nil)(context)  
      case _ => throw new Exception("Unhandled AST node")
    }
  }
  


  private def transform(tree: S.Tree)(ctx: C.Atom =>  C.Tree) : C.Tree = {
    implicit val pos = tree.pos
    nonTail(tree)(ctx)
  }
}
