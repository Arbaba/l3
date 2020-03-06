package l3

import l3.{ SymbolicCL3TreeModule => S }
import l3.{ SymbolicCPSTreeModule => C }

object CL3ToCPSTranslator extends (S.Tree => C.Tree) {
  def apply(tree: S.Tree): C.Tree = {
    
    transform(tree){ v : C.Atom => 
      C.Halt(C.AtomL(IntLit(L3Int(0))))
    }
  }
  var cnt = 0
  private def transform(tree: S.Tree)(implicit ctx: C.Atom =>  C.Tree) : C.Tree = {
    implicit val pos = tree.pos
    //println(tree.toString.toCharArray.take(100).mkString(""))
    tree match {
      //f(name, args, body)
      //case S.LetRec(f, e) => C.LetF(, transform(e))
      case S.Prim(p: L3TestPrimitive, args) => {
        println("transforming logiaal primitive")
        transform{
        S.If(S.Prim(p, args), S.Lit(BooleanLit(true)), S.Lit(BooleanLit(true)))
      }(ctx)
      }
      case S.Prim(prim: L3ValuePrimitive, args) => {
        println("transforming value primitive")
        val primEval = Symbol.fresh("v")
        val id = Symbol.fresh("id")
        val idRet = Symbol.fresh("id")
        val arg = Symbol.fresh("a")
        val identity = C.Fun(id, idRet, Seq(arg), C.AppF(C.AtomN(id), idRet, Seq(C.AtomN(arg))))
        val c = Symbol.fresh("c")
        val r = Symbol.fresh("r")
        val app: C.Tree = C.LetC(Seq(C.Cnt(c, Seq(r), ctx(C.AtomN(r)))), C.AppF(C.AtomN(id), c, Seq(C.AtomN(primEval))))
        val retFunc = C.LetF(Seq(identity), app)
        val z: C.Tree = C.LetP(primEval, prim, Seq(), retFunc)
        /*args.foldRight(z){
          case ()
        }*/
        args.foldRight(z){
          case (symbolicArg, C.LetP(primEval, prim, transformedArgs, retFunc)) => {
            transform(symbolicArg){ v1: C.Atom => 
              C.LetP(primEval, prim, Seq(v1) ++ transformedArgs, retFunc)
            }
          }
        }
      }
      case S.LetRec(funs, body ) => 
        println("transforming letrec")
        val c = Symbol.fresh("c")
      
        val fs  = funs.map(f => C.Fun(f.name, c, f.args, transform(f.body){v: C.Atom => C.AppC(c, Seq(v))})) 
      
        C.LetF(fs, transform(body){v: C.Atom => C.AppC(c, Seq(v))})
      case S.App(e, args) => {
        println("transforming app")
        transform(e) { v: C.Atom =>
        val c = Symbol.fresh("c")
        val r = Symbol.fresh("r")
        val z: C.Tree = C.LetC(Seq(C.Cnt(c, Seq(r), ctx(C.AtomN(r)))), C.AppF(v, c, Seq()))
        args.foldRight(z){
          case (symbolic, C.LetC(x, C.AppF(v, c, seq))) => transform(symbolic) {
            v1: C.Atom => C.LetC(x, C.AppF(v, c, Seq(v1) ++ seq)) 
          }
        }
      }
      }
      case S.Ident(name) => ctx(C.AtomN(name))
      case S.Lit(v) => ctx(C.AtomL(v))
      case S.Let(Seq((n1, e1), otherArgs @ _*), e) => {
        println("transforming let1")
        transform(e1){ v1: C.Atom =>
          C.LetP(n1, L3Id, Seq(v1), transform(S.Let(otherArgs, e))(ctx))
        }
      }
      case S.Let(Seq(), e) => 
      println("transforming let2")
      transform(e)
      //if-node with a primitive cond
      //L3TestPrimitive
      
      case S.If(S.Prim(p: L3TestPrimitive, e), e2, e3) => {
        println("transforming logical if")
        val r = Symbol.fresh("r")
        val c = Symbol.fresh("c")
        val ct = Symbol.fresh("ct")
        val cf = Symbol.fresh("cf")
        val e1 = e(0)
        transform(e2){ v2: C.Atom => 
          transform(e3){ v3: C.Atom => 
            val condCnt = C.Cnt(c, Seq(r), ctx(C.AtomN(r)))
            val thenCnt = C.Cnt(ct, Seq(), C.AppC(c, Seq(v2)))
            val elseCnt = C.Cnt(cf, Seq(), C.AppC(c, Seq(v3)))
            C.LetC(Seq(condCnt), 
              C.LetC(Seq(thenCnt), 
                C.LetC(Seq(elseCnt), 
                  transform(e1){v1: C.Atom => 
                    C.If(p, Seq(v1), ct, cf)
                  })))
          }
        }
      }
      //if-node sugared
      //
      case S.If(e1, e2, e3) => {
        println(s"Transforming if $tree")
        cnt += 1
        if(cnt > 3) throw new Exception("stack overflow")
        transform(S.If(S.Prim(L3Eq, Seq(e1, S.Lit(BooleanLit(false)))), e3, e2))
      }
      //halt(e) => halt()
      case S.Halt(e) => transform(e){v: C.Atom => C.Halt(v)}
    }

  }
}
