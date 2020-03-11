package l3

import l3.{ SymbolicCL3TreeModule => S }
import l3.{ SymbolicCPSTreeModule => C }

object CL3ToCPSTranslator extends (S.Tree => C.Tree) {
  val stub = C.Halt(C.AtomL(IntLit(L3Int(0))))
  def apply(tree: S.Tree): C.Tree = {
    transform(tree){ v : C.Atom => 
      C.Halt(C.AtomL(IntLit(L3Int(0))))
    }
  }
  var cnt = 0
  val nilAtoms :Seq[C.Atom] = Seq()
  private def atomStacker(trees: Seq[S.Tree], acc: Seq[C.Atom])( ctx: Seq[C.Atom] => C.Tree): C.Tree = trees match {
    case Seq() => ctx(acc.reverse)
    case Seq(head, others@_*) => 
      transform(head){v: C.Atom => {
          atomStacker(others, v +: acc)(ctx)
        }
      }
  }
def bool(v: Boolean): S.Lit = S.Lit(BooleanLit(v))(UnknownPosition)
  /**
    translation of the form λv (appc c v)
    It gets as argument the name of the continuation c 
    to which the value of expression should be applied. 
  */
  private def tail(t: S.Tree, c: Symbol): C.Tree = {
    implicit val pos = t.pos

    t match  {

    case S.Ident(n) => 
        C.AppC(c, Seq(C.AtomN(n)))
    case S.Lit(v) => 
        C.AppC(c, Seq(C.AtomL(v)))
    case S.Let(Seq(), e) => 
      tail(e, c)
    case S.Let(Seq((n1, e1), others@_*), e) => 
      nonTail(e1){v: C.Atom => C.LetP(n1, L3Id,Seq(v), tail(S.Let(others, e), c))}
    case S.LetRec(funs, e) => 
      val fs  = funs.map(f => {
                val c = Symbol.fresh("c_LetRecT")
                C.Fun(f.name, c, f.args, tail(f.body, c))
              })
        C.LetF(fs, tail(e, c))    
    case S.App(e, args) => 
        atomStacker(args, nilAtoms){atoms: Seq[C.Atom] => nonTail(e){f => C.AppF(f, c, atoms)}}
    case S.If(e1, e2, e3) => 
        val ct = Symbol.fresh("ctT")
        val cf = Symbol.fresh("cfT")
        val thenCnt = C.Cnt(ct, Seq(), tail(e2, c)) // { v2: C.Atom =>C.AppC(c, Seq(v2))}
        val elseCnt = C.Cnt(cf, Seq(),tail(e3, c)) // { v3: C.Atom =>C.AppC(c, Seq(v3))}
        C.LetC(Seq(thenCnt),
          C.LetC(Seq(elseCnt), 
            cond(e1, ct, cf)
        ))
    case S.Prim(p:L3TestPrimitive, args) => 
        tail(S.If(t, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))), c)
    case S.Prim(p:L3ValuePrimitive, args) =>
        val primRes = Symbol fresh "primResT"
        atomStacker(args, nilAtoms){
          atoms => C.LetP(primRes, p, atoms, C.AppC(c, Seq(C.AtomN(primRes))) )

        }
    case S.Halt(e) => 
      nonTail(e){v => C.Halt(v)}
    case _ => nonTail(t){v: C.Atom => C.AppC(c, Seq(v))}
    }

  }
  val tru = S.Lit(BooleanLit(true))(UnknownPosition)
  val fal = S.Lit(BooleanLit(false))(UnknownPosition)
  /*
  ct cf are continuation names
  */
  private def cond(t: S.Tree, ct: Symbol, cf: Symbol): C.Tree = {
    implicit val pos = t.pos
    t match {
      case S.Lit(BooleanLit(v)) => 
        C.AppC(if(v == true) ct else cf, 
          Seq())
      case name: S.Ident => 
        cond(S.Prim(L3Eq, Seq(name, fal)), cf, ct)
      case S.Let(Seq(), bod) => 
        cond(bod, ct, cf)
      case S.Let(Seq((n1, e1), otherArgs @ _*), body) => 
        nonTail(e1){ v1: C.Atom =>
          C.LetP(n1, L3Id, Seq(v1), cond(S.Let(otherArgs, body), ct, cf))
        }
      case S.If(e1, S.Lit(BooleanLit(v1)), S.Lit(BooleanLit(v2))) => 
        if(v1 == v2) throw new Exception("Unhandled case")//cond(e1, ct, cf)//trivial case. we still have to evaluate the condition in case it produces a side effect
        else if(v1 == true) cond(e1, ct, cf)
        else cond(e1, cf, ct)
      case S.If(e1, e2, S.Lit(BooleanLit(v3))) => 
        val ac = Symbol fresh "ac"
        val cnt = C.Cnt(ac, Seq(), cond(e2, ct, cf))
        C.LetC(Seq(cnt), cond(e1, ac, cf))
      case S.If(e1, e2@S.Lit(BooleanLit(_)), e3) => 
        cond(S.If(e1, e3, e2), cf, ct)
      case S.If(e1, e2, e3) => nonTail(e1){v: C.Atom => 
        C.If(L3Eq, Seq(v, C.AtomL(BooleanLit(false))), ct, cf)
      }
      case arbitrary => nonTail(arbitrary){v: C.Atom => 
        C.If(L3Eq, Seq(v, C.AtomL(BooleanLit(true))), ct, cf )
      }
      case _ => throw new Exception(s"$t ($cf, $ct)")
    }
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
        atomStacker(args, nil)(context)  
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
        val thenCnt = C.Cnt(ct, Seq(), tail(e2, c)) // { v2: C.Atom =>C.AppC(c, Seq(v2))}
        val elseCnt = C.Cnt(cf, Seq(),tail(e3, c)) // { v3: C.Atom =>C.AppC(c, Seq(v3))}

        C.LetC(Seq(plugin),             
          C.LetC(Seq(thenCnt),
            C.LetC(Seq(elseCnt), 
              atomStacker(e, nil){atoms: Seq[C.Atom] => 
                    C.If(p, atoms, ct, cf)
              })))
              /**/
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
        atomStacker(args, nil)(context)  
      case _ => throw new Exception("Unhandled AST node")
    }
  }
  


  private def transform(tree: S.Tree)(ctx: C.Atom =>  C.Tree) : C.Tree = {
    implicit val pos = tree.pos
    nonTail(tree)(ctx)
  }
}
