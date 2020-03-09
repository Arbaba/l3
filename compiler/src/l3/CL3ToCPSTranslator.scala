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

  private def atomStacker(trees: Seq[S.Tree], acc: Seq[C.Atom])( ctx: Seq[C.Atom] => C.Tree): C.Tree = trees match {
    case Seq() => ctx(acc)
    case Seq(head, tail@_*) => 
      transform(head){v: C.Atom => {
          atomStacker(tail, v +: acc)(ctx)
        }
      }
  }

  private def transform(tree: S.Tree)(ctx: C.Atom =>  C.Tree) : C.Tree = {
    implicit val pos = tree.pos
    //println(tree.toString.toCharArray.take(100).mkString(""))
    tree match {
    
      case prim@S.Prim(p: L3TestPrimitive, args) =>
        transform{
          S.If(prim, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false)))
        }(ctx)
      
    
      case S.LetRec(funs, body ) => 
        
        val fs  = funs.map(f => {
          val c = Symbol.fresh("c_LetRec")
          C.Fun(f.name, c, f.args, transform(f.body){v: C.Atom => C.AppC(c, Seq(v))})
        })
        //println(transform(body)(ctx))
        C.LetF(fs, transform(body)(ctx))
      case S.Prim(p: L3ValuePrimitive, args) =>
        println("ss" +args)
        val nil :Seq[C.Atom] = Seq()
        val c = Symbol.fresh("c_prim")
        val a = Symbol.fresh("c_arg")
        val r = Symbol.fresh("primRes")
        //val cnt = C.Cnt(c, Seq(a), (C.AtomN(a)))
        val context = {atoms: Seq[C.Atom] => {
          C.LetP(r,p, atoms, ctx(C.AtomN(r)))
      
        }}
        atomStacker(args, nil)(context)  
  
      case S.App(e, args) => 
        val nil :Seq[C.Atom] = Seq()
        val c = Symbol.fresh("c_App")
        val r = Symbol.fresh("r_App")
        val cnt = C.Cnt(c, Seq(r), ctx(C.AtomN(r)))
        val context = {atoms: Seq[C.Atom] => {
          println("xx" +atoms )
          val body = transform(e){v: C.Atom => C.AppF(v, c, atoms)}
          println(body)
          C.LetC(Seq(cnt),body)

        }}
        atomStacker(args, nil)(context)  
       
        
      
      case S.Ident(name) => ctx(C.AtomN(name))
      case S.Lit(v) => ctx(C.AtomL(v))

      case S.Let(Seq((n1, e1), otherArgs @ _*), e) => {
        println("transforming let1")
        transform(e1){ v1: C.Atom =>
          C.LetP(n1, L3Id, Seq(v1), transform(S.Let(otherArgs, e))(ctx))
        }
      }
      case S.Let(Seq(), e) => transform(e)(ctx)
      //if-node with a primitive cond
      //L3TestPrimitive
      case S.If(S.Prim(p: L3TestPrimitive, e), e2, e3) => {
        val nil: Seq[C.Atom] = Seq()
        println(tree)
        println("e3" +e3)
        atomStacker(e, nil){atoms: Seq[C.Atom] => 
          val r = Symbol.fresh("r_If")
          val c = Symbol.fresh("c_If")
          val ct = Symbol.fresh("ct")
          val cf = Symbol.fresh("cf")
          val e1 = e(0)
         // transform(S.Prim(p, atoms.collect{ case  C.AtomN(n) => S.Ident(n)})){
         //   primRes: C.Atom =>
            transform(e2){ v2: C.Atom => 
              transform(e3){ v3: C.Atom =>
                println("v3" + v3) 
                val plugin = C.Cnt(c, Seq(r), ctx(C.AtomN(r)))
                val thenCnt = C.Cnt(ct, Seq(), C.AppC(c, Seq(v2)))
                val elseCnt = C.Cnt(cf, Seq(), C.AppC(c, Seq(v3)))
                val bool = Symbol.fresh("bool")
                val x =
                C.LetC(Seq(plugin), 
                  C.LetC(Seq(thenCnt), 
                    C.LetC(Seq(elseCnt), 
                        C.If(p, atoms, ct, cf)//We need to somehow put the result of the primitive application result
                                              //instead of atoms 
                      )))
                println(x.body)
                      x
              } 
            }
          //}
        }
      }
     
      case S.If(e1, e2, e3) => {

        transform(S.If(S.Prim(L3Eq, Seq(e1, S.Lit(BooleanLit(false)))), e3, e2))(ctx)
      }
      //halt(e) => halt()
      case S.Halt(e) => transform(e){v: C.Atom => C.Halt(v)}
    }

  }
}
