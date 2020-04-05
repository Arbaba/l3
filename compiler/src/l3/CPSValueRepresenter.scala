package l3

import l3.{SymbolicCPSTreeModule => H} 
import l3.{SymbolicCPSTreeModuleLow => L} 

object CPSValueRepresenter extends (H.Tree => L.Tree) {
  def lowLiteral(i: Int) = apply_(H.AtomL(IntLit(L3Int(i))))
  val one = apply_(H.AtomL(IntLit(L3Int(1))))
  val unboxedOne = L.AtomL(1)
  /* 
    Helper functions 
  */ 
  def add1(a: L.Atom)(body : L.Atom => L.Tree): L.Tree = letpFresh(CPSAdd, Seq(a, unboxedOne))(body)
  def sl1(a: L.Atom)(body : L.Atom => L.Tree): L.Tree = letpFresh(CPSShiftLeft, Seq(a, unboxedOne))(body)
  def min1(a: L.Atom)(body : L.Atom => L.Tree): L.Tree = letpFresh(CPSSub, Seq(a, unboxedOne))(body)
  
  def letpFresh(p: L.ValuePrimitive, args: Seq[L.Atom])(ctx: L.AtomN => L.Tree): L.Tree = {
    val tmp = Symbol.fresh("ux")
    L.LetP(tmp, p,args, ctx(L.AtomN(tmp)))
  }

  def letp(name: L.Name, p: L.ValuePrimitive, args: Seq[L.Atom], body:L.Tree): L.Tree = {
    L.LetP(name, p,args, body)
  }

  def boxInt(v: L.Atom, name: H.Name = Symbol.fresh("t2"))(callback: L.Atom => L.Tree) = {
    sl1(v){
      t1 => L.LetP(name, CPSAdd, Seq(t1, unboxedOne),
                  callback(L.AtomN(name)))
    }
  }
  def unboxInt(atom: H.Atom)(callback: L.Atom => L.Tree): L.Tree =  {
    val f = Symbol fresh "int"
    L.LetP(f, CPSShiftRight, Seq(apply_(atom), unboxedOne),callback(L.AtomN(f)))

  }

  /*def freeVariables(tree_: H.Tree, fv: Set[Name]): Set[Name] = {
    def freeVariables_(tree: H.Tree, fv: Set[Name]): Set[Name] = tree match {
      case H.LetP(n, p, v, e) => 
        freeVariables_(e, fv) - n + 
    }
  }*/
  def freeVariables(tree: H.Tree): Set[Symbol] = {
    def atomAsFV(atom: H.Atom): Set[Symbol] = atom match {
      case H.AtomN(name) => Set(name)
      case _ => Set()
    }
    tree match {
      case H.LetP(n, p, v, e) => freeVariables(e) ++ v.flatMap(atomAsFV) - n
      case H.LetC(cs, e) => freeVariables(e) ++ cs.flatMap{ case H.Cnt(_, args, body) => freeVariables(body) -- args.toSet }
      case H.LetF(fs, e) => 
        val funFv = fs.flatMap{ case H.Fun(name, _, args, body) => freeVariables(body) -- args.toSet}
        freeVariables(e) ++ funFv -- fs.map(_.name).toSet
      case H.AppC(_, atoms) => atoms.flatMap(atomAsFV).toSet
      case H.AppF(v, c, vs) => atomAsFV(v) ++ vs.flatMap(atomAsFV)
      case H.If(_, v, _, _) => v.flatMap(atomAsFV).toSet
      case H.Halt(atom) => atomAsFV(atom)
    }
  }
  def freeVariablesFun(fun: H.Fun): Set[Symbol] = freeVariables(fun.body) -- Set(fun.name) -- fun.args.toSet

  def substitute(tree: L.Tree)(implicit ctx: Subst[Symbol]): L.Tree = {
      def subst(atom: L.Atom): L.Atom = atom match {
        case L.AtomL(_) => atom
        case L.AtomN(n) => L.AtomN(ctx.getOrElse(n,n))
      }  
      def substCnt(c: L.Cnt) = c match {
        case L.Cnt(name, args, e) => L.Cnt(name, args, substitute(e))
      }
      tree match  {
        case L.LetP(n, p, v, e) => L.LetP(n, p, v.map{a => subst(a)}, substitute(e))
        case L.LetC(cs, e) => L.LetC(cs.map(substCnt), substitute(e))
        case L.LetF(fs, e) => L.LetF(fs, substitute(e))
        
        case L.AppC(c, atoms) => L.AppC(c, atoms.map{a => subst(a)}) 
        case L.AppF(v, c, vs) => L.AppF(subst(v), c, vs.map(subst))
        case L.If(a, v, b, c) => L.If(a, v.map(subst), b,c) 
        case L.Halt(atom) => L.Halt(subst(atom))
        //case atom: L.Atom => subst(atom)  
      }
  
  }
  def closure(letf: H.LetF): L.Tree = {
    //Close fv calls with environment access
    def blockGet(f: Symbol, env: Symbol , fv: Seq[(Symbol, Int)], ctx: Subst[Symbol], body: L.Tree): (L.Tree, Subst[Symbol]) =   fv match {
       case Seq((symbol, idx),tail@_*) => 
        val v = Symbol.fresh("v")
        val (letbody, ctxAcc) = blockGet(f, env, tail, ctx + (symbol ->v), body)
      
        (letp(v, CPSBlockGet, Seq(L.AtomN(env), L.AtomL(idx)), substitute(letbody)(ctxAcc) ), ctxAcc)
        case Seq() => 
  
         (substitute(body)(ctx), ctx)
    }

    //Closure initialization
    def blockSet(f: Symbol, fv: Seq[(Symbol, Int)], body: L.Tree): L.Tree =   fv match {
      case Seq((symbol, idx),tail@_*) => 
        letpFresh(CPSBlockSet, Seq(L.AtomN(f),L.AtomL(idx), L.AtomN(symbol))){_ => blockSet(f, fv.tail, body)}
      case Seq() => 
        body
    }

    //Returns the closed function with FVs mapping and worker symbol for the blocksets
    def close(fun: H.Fun): (L.Fun, (Symbol, Seq[Symbol]), Symbol) = {
      val w1 = Symbol.fresh("w")
      val env1 = Symbol.fresh("env")
      val fv = freeVariablesFun(fun).toSeq
      val fvzipped = fv.zip(1 to fv.size)
      val (body, ctx) =  blockGet(fun.name, env1, fvzipped, Map(fun.name -> env1), apply(fun.body))
      val funFV = Set(fun.name) ++ fun.args.toSet
      val removArgs = ctx.filter{case (freeName , newName) => !funFV.contains(freeName)}
      (L.Fun(w1, fun.retC, Seq(env1) ++ fun.args, body ), (fun.name,removArgs.keys.toSeq), w1)
    }
    /*
     * Initialize closures blocks
     * @param ctxs Sequence of zipped closured name and corresponding free variables
     * @param body The closure body
     * @param ws   The closure worker symobol
     * @return     The nested tree of blocksets followed by the body
     * */
    def initClosures(ctxs: Seq[(Symbol, Seq[Symbol])], body: H.Tree, ws: Seq[Symbol]): L.Tree = {
      def recHelper(ctxs: Seq[(Symbol, Seq[Symbol])], body: H.Tree) = ctxs match {
        case Seq() => 
          apply(body)
        case Seq((fi , fvs), otherFVs@_*) =>  
          blockSet(fi, fvs.zip(1 to fvs.length), initClosures(otherFVs, body, ws.tail))
      }
      ctxs match {
        case Seq(head, tail@_*) => 
          val (fi, fvs) = ctxs.head
              letpFresh(CPSBlockSet, Seq(L.AtomN(fi), L.AtomL(0),L.AtomN(ws.head))){_ => recHelper(ctxs, body)}
        case Seq() => 
          apply(body)
      }
    
    }
    /*
     * Allocates and initializes closures blocks
     * @param closuresInfo Sequence of zipped closured name and block size
     * @param body The expression to evaluate after the closures allocation
     * @return Tree of closures followed by the body
     * */
    def createClosures(closuresInfo: Seq[(Symbol, Int)], body: L.Tree): L.Tree = closuresInfo match {
      case Seq() => 
        body
      case Seq((fname, blockSize), others@_*) => 
        letp(fname, CPSBlockAlloc(202), Seq(L.AtomL(blockSize)), createClosures(others, body))

    }
    val (closedfs,  ctxs, ws) = letf.funs.map(close).unzip3
    val closuresInfo = ctxs.map{case (name, fvs) => (name, fvs.size + 1)}
    L.LetF(closedfs, createClosures(closuresInfo, initClosures(ctxs, letf.body, ws)))
  

  }

  /* 
    Tree Transformation 
  */
  def apply(tree: H.Tree): L.Tree = tree match {
    case H.LetP(name: H.Name, p@L3IntAdd, Seq(x,y ) , body) => 
      letpFresh(CPSXOr, Seq(apply_(x), L.AtomL(1))){ux => 
        L.LetP(name, CPSAdd, Seq(ux, apply_(y)), apply(body))
      }
    case H.LetP(name, L3BlockAlloc(tag), Seq(arg), body) => 
      unboxInt(arg){t1 => L.LetP(name,CPSBlockAlloc(tag) , Seq(t1), apply(body))}
    
  /*
    Continuations
  */
    case H.LetC(continuations, e) => L.LetC(continuations.map{
      case H.Cnt(ni, ai, ei) => L.Cnt(ni, ai, apply(ei))
    }, apply(e))
    case H.AppC(cntName, valueBindings) => L.AppC(cntName, valueBindings.map(apply_))
    /*
      Functions
    */
    case letf@H.LetF(functions, body) => closure(letf)

    case H.AppF(fun, retC, args) => {
      val f = Symbol.fresh("f")
      val v = apply_(fun)
      L.LetP(f, CPSBlockGet, Seq(v, L.AtomL(0)),
        L.AppF(L.AtomN(f), retC, Seq(v) ++ args.map(apply_))
      )
    }
    //Arithmetic primitives
    case H.LetP(name, L3IntAdd, atoms@Seq(_, _), body) => 
      letpFresh(CPSAdd, atoms.map(apply_)){
        t1 => L.LetP(name, CPSSub, Seq(t1, unboxedOne), apply(body))
      }
        
    case H.LetP(name, L3IntSub, atoms@Seq(_, _), body) => 
      letpFresh(CPSSub, atoms.map(apply_)){
        t1 =>  L.LetP(name, CPSAdd, Seq(t1, unboxedOne), apply(body))
      }
       
    case H.LetP(name, L3IntMul, atoms@Seq(v1, v2), body) =>
      letpFresh(CPSSub, Seq(apply_(v1), unboxedOne))
       {n => unboxInt(v2)
        {m => letpFresh(CPSMul, Seq(n, m))
          {x => letp(name, CPSAdd,  Seq(x, unboxedOne),apply(body)) }
        }
       }
      
     /*
      [n / m] = ([n] - 1)/ ([m] - 1) + 1
     */ 

    case H.LetP(name, L3IntDiv, atoms@Seq(v1, v2), body) => 
 
      min1(apply_(v1)){t1: L.Atom => 
        min1(apply_(v2)){t2: L.Atom => 
            letpFresh(CPSDiv, Seq(t1, t2)){
              r => boxInt(r, name){
               _ => apply(body)
              }
            }            
        }
      }
    
    case H.LetP(name, L3IntMod, atoms@Seq(v1, v2), body) => 
      unboxInt(v1){
        s1 => unboxInt(v2){
          s2 => letpFresh(CPSMod, Seq(s1,s2)){
            mod => boxInt(mod, name){
              _ => apply(body)
            }
          }
        }
      }
     
    case H.LetP(name, L3IntShiftLeft, atoms@Seq(v1, v2), body) => 

      min1(apply_(v1)){
        t1 => unboxInt(v2){
          t2 => letpFresh(CPSShiftLeft, Seq(t1,t2)){
            shift => letp(name, CPSAdd, Seq(shift, unboxedOne), apply(body))
          }
        }
      }
      
    case H.LetP(name, L3IntShiftRight, atoms@Seq(v1, v2), body) =>
      unboxInt(v1){
        t1 => unboxInt(v2){
          t2 => letpFresh(CPSShiftRight, Seq(t1,t2)){
            shift => boxInt(shift,name){ _ => apply(body)}
          }
        }
      }

             
    case H.LetP(name, L3IntBitwiseAnd, atoms@Seq(_, _), body)=> 
      L.LetP(name, CPSAnd, atoms.map(apply_), apply(body))
    case H.LetP(name, L3IntBitwiseOr, atoms@Seq(_, _), body) =>
      L.LetP(name, CPSOr, atoms.map(apply_), apply(body))
    case H.LetP(name, L3IntBitwiseXOr, atoms@Seq(_, _), body) =>
      letpFresh(CPSXOr, atoms.map(apply_)){
        tmp => L.LetP(name, CPSOr, Seq(tmp, unboxedOne), apply(body))
      }
    


    /*
    2(([n] - 1)/2 % ([m] - 1)/2) + 1
    */
    //Logical primitives
    case H.If(L3IntP, Seq(v), ct, cf) => 
      val t1 = Symbol.fresh("t1")
      L.LetP(t1, CPSAnd, Seq(unboxedOne, apply_(v)), 
          L.If(CPSEq, 
            Seq(L.AtomN(t1), unboxedOne),
              ct, cf))
    case H.If(L3IntLt, atoms@Seq(_, _), ct, cf) =>
      L.If(CPSLt, atoms.map(apply_), ct, cf) 
    case H.If(L3IntLe, atoms@Seq(_, _), ct, cf) =>
      L.If(CPSLe, atoms.map(apply_), ct, cf) 
    case H.If(L3Eq, atoms@Seq(_, _), ct, cf) => 
      L.If(CPSEq, atoms.map(apply_), ct, cf)
    case H.If(L3UnitP, atom@Seq(v), ct, cf) => 
      L.If(CPSEq, Seq(apply_(v), L.AtomL(2)), ct, cf)
    case H.If(L3BoolP, Seq(v), ct, cf) =>
      val t = Symbol.fresh("t")
      L.LetP(t, CPSAnd, Seq(apply_(v), L.AtomL(0xF)),
        L.If(CPSEq, Seq(L.AtomN(t), L.AtomL(0xA)), ct, cf)
      )
      /*val t = Symbol.fresh("t")
      L.LetP(t, CPSEq, Seq(apply_(v), lowLiteral(2)), 
        L.If()
      )*/
    /*Blocks*/
    case H.If(L3BlockP, Seq(v), ct, cf) =>  
      letpFresh(CPSAnd, Seq(apply_(v), L.AtomL(3))){
        unboxed => L.If(CPSEq, Seq(unboxed, L.AtomL(0)), ct, cf)
      }
      
    
    case H.LetP(name, L3BlockAlloc(tag), Seq(v), body) => 
      unboxInt(v){
        unboxed => L.LetP(name, CPSBlockAlloc(tag), Seq(unboxed), apply(body))
      }
      
    case H.LetP(name, L3BlockTag, Seq(v), body) => 
      letpFresh(CPSBlockTag, Seq(apply_(v))){
        t1 => boxInt(t1,name){
            _ => apply(body)
        }
      }
          
    case H.LetP(name, L3BlockLength, Seq(v), body) => 
      letpFresh(CPSBlockLength, Seq(apply_(v))){
         t1 => sl1(t1){
           t2 =>  L.LetP(name, CPSAdd, Seq(t2, unboxedOne),apply(body))
         }
       }
    case H.LetP(name, L3BlockGet, Seq(block, slot), body) => 
      unboxInt(slot){
        t2 => L.LetP(name, CPSBlockGet, Seq(apply_(block), t2),apply(body))
      }
    case H.LetP(name, L3BlockSet, Seq(v1, v2, v3), body) => 
      unboxInt(v2){
        t1 => L.LetP(name, CPSBlockSet, Seq(apply_(v1), t1,(apply_(v3))),apply(body))
      }
               
    //bytes
    case H.LetP(name, L3ByteRead, Seq(), body) => 
      letpFresh(CPSByteRead, Seq()){ 
        t1 => boxInt(t1,name){ _ => apply(body)}
      }
      
    case H.LetP(name, L3ByteWrite, Seq(v), body) => 
      unboxInt(v){
        n => letp(name, CPSByteWrite, Seq(n), apply(body))
      }
      
    //chars
    case H.LetP(name, L3CharToInt, Seq(v1), e) => 
      L.LetP(name, CPSShiftRight, Seq(apply_(v1), L.AtomL(2)), 
        apply(e)
      )
    case H.LetP(name, L3IntToChar, Seq(v1), e) => 
      letpFresh(CPSShiftLeft, Seq(apply_(v1), L.AtomL(2))){
        t1 =>  L.LetP(name, CPSAdd, Seq(t1, L.AtomL(2)), apply(e))
        
      }
       
      
    case H.If(L3CharP, Seq(v), ct, cf) => 
       letpFresh(CPSAnd, Seq(apply_(v), L.AtomL(7)))
      { n =>L.If(CPSEq, Seq(n, L.AtomL(6)), ct, cf)}
    case H.Halt(atom) => 
      unboxInt(atom){symbol => L.Halt(symbol)}
      
    case H.LetP(name, L3Id, Seq(v), body) => 
      L.LetP(name, CPSId, Seq(apply_(v)),  apply(body)
      )
    case x => throw new Exception(s"$x not implemented!")
  }


  def apply_(a: H.Atom): L.Atom =  a match {
    case H.AtomN(n) => 
      L.AtomN(n)
    case H.AtomL(IntLit(v)) =>
      L.AtomL((v.toInt << 1) | 1) 
    case H.AtomL(BooleanLit(b)) => L.AtomL(if(b) 0x1A else 0xA)
    case H.AtomL(CharLit(c)) => L.AtomL((c << 3) | 6 )
    case H.AtomL(UnitLit) => L.AtomL(2)
  }

}
