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
  var cnt = 0
  private def transform(tree: S.Tree)(implicit ctx: C.Atom =>  C.Tree) : C.Tree = {
    implicit val pos = tree.pos
    tree match {
      case S.Prim(prim: L3ValuePrimitive, args) if args.collect{
        case id: S.Ident => id
      }.size == args.size => {
        val res = Symbol.fresh("primRes")
        C.LetP(res, prim, args.map{ case S.Ident(arg) => C.AtomN(arg) }, ctx(C.AtomN(res)))
      }
      case S.Prim(prim: L3ValuePrimitive, args: Seq[S.Tree]) => {
        val argNames = 0.until(args.size).map{i: Int => Symbol.fresh(s"a$i")}
        transform(S.Let(argNames.zip(args), S.Prim(prim, argNames.map{argName: S.Name => S.Ident(argName)})))

      }
      

      case prim@S.Prim(p: L3TestPrimitive, args) =>
        transform{
          S.If(prim, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(true)))
        }(ctx)
      case S.LetRec(funs, body ) => 
        val fs  = funs.map(f => {
          val c = Symbol.fresh("c_LetRec")
          C.Fun(f.name, c, f.args, transform(f.body){v: C.Atom => C.AppC(c, Seq(v))})
        })
        C.LetF(fs, transform(body)(ctx))

      case S.App(e, args) => {
        println("transforming app")
        transform(e) { v: C.Atom =>
        val c = Symbol.fresh("c_App")
        val r = Symbol.fresh("r_App")
        val z: C.Tree = C.LetC(Seq(C.Cnt(c, Seq(r), ctx(C.AtomN(r)))), C.AppF(v, c, Seq()))
        args.foldRight(z){
          case (symbolic, C.LetC(x, C.AppF(v, c, seq))) => transform(symbolic) {
            v1: C.Atom => C.LetC(x, C.AppF(v, c, Seq(v1) ++ seq)) 
          }
          case _ => throw new Exception("problem with application folding")
        }
      }
      }
      case S.Ident(name) => ctx(C.AtomN(name))
      case S.Lit(v) => {
        println("literal matching")
        val res = ctx(C.AtomL(v))
        println("literal matched")
        res
      }

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
        println(s"transforming logical if (then::$e2) (else::$e3)")
        val r = Symbol.fresh("r_If")
        val c = Symbol.fresh("c_If")
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
        transform(S.If(S.Prim(L3Eq, Seq(e1, S.Lit(BooleanLit(false)))), e3, e2))
      }
      //halt(e) => halt()
      case S.Halt(e) => transform(e){v: C.Atom => C.Halt(v)}
      case _ => throw new Exception("unhandled case")
    }

  }
}
