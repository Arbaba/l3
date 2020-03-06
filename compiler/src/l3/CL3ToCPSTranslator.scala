package l3

import l3.{ SymbolicCL3TreeModule => S }
import l3.{ SymbolicCPSTreeModule => C }

object CL3ToCPSTranslator extends (S.Tree => C.Tree) {
  def apply(tree: S.Tree): C.Tree = {
    println(tree)
    transform(tree){ v : C.Atom => 
      println("Atom after translation ")
      println(v)
      C.Halt(C.AtomL(IntLit(L3Int(0))))
    }
  }
  private def transform(tree: S.Tree)(implicit ctx: C.Atom =>  C.Tree) : C.Tree = {
    implicit val pos = tree.pos
    tree match {
      //f(name, args, body)
      //case S.LetRec(f, e) => C.LetF(, transform(e))
      case S.Prim(prim: L3ValuePrimitive, args) => {
        val primEval = Symbol.fresh("v_valPrim")
        val id = Symbol.fresh("id_valPrim")
        val idRet = Symbol.fresh("idRet_valPrim")
        val arg = Symbol.fresh("a_valPrim")
        val identity = C.Fun(id, idRet, Seq(arg), C.AppF(C.AtomN(id), idRet, Seq(C.AtomN(arg))))
        val c = Symbol.fresh("c_valPrim")
        val r = Symbol.fresh("r_valPrim")
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
              //C.LetP(primEval, prim, Seq(v1) ++ transformedArgs, ctx(C.AtomN(primEval)))
            }
          }
        }
      }
      case prim@S.Prim(p: L3TestPrimitive, args) =>
            C.Halt(C.AtomL(IntLit(L3Int(1))))

      transform{
        S.If(prim, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(true)))
      }(ctx)
      case S.LetRec(funs, body ) => 
  /*      val id_arg = Symbol.fresh("cntArg_LetRec")
        val identity_cnt = C.Cnt(c,Seq(id_arg), transform(S.Ident(id_arg)){v:C.Atom => (C.Halt(v))})*/
        val fs  = funs.map(f => {
          val c = Symbol.fresh("c_LetRec")
          C.Fun(f.name, c, f.args, transform(f.body){v: C.Atom => C.AppC(c, Seq(v))})
        })
        C.LetF(fs, transform(body)(ctx))
      case S.App(e, args) => transform(e) { v: C.Atom =>
        val c = Symbol.fresh("c_App")
        val r = Symbol.fresh("r_App")
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
                    println("debug let 1")

      
        transform(e1){ v1: C.Atom =>
          C.LetP(n1, L3Id, Seq(v1), transform(S.Let(otherArgs, e))(ctx))
        }
      }
      case S.Let(Seq(), e) => 
      println("debug let 2")
      transform(e)
      //if-node with a primitive cond
      //L3TestPrimitive
      
      case S.If(S.Prim(p: L3TestPrimitive, Seq(e1)), e2, e3) => {
        val r = Symbol.fresh("r_If")
        val c = Symbol.fresh("c_If")
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
