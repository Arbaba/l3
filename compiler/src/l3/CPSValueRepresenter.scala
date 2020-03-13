package l3

import l3.{SymbolicCPSTreeModule => H} 
import l3.{SymbolicCPSTreeModuleLow => L} 

object CPSValueRepresenter extends (H.Tree => L.Tree) {
  def lowLiteral(i: Int) = apply_(H.AtomL(IntLit(L3Int(i))))
  val one = apply_(H.AtomL(IntLit(L3Int(1))))
  val unboxedOne = L.AtomL(1)
  type IntBoxer = L.Atom => (L.Atom => L.Tree) => L.Tree
  def intOp(op: CPSValuePrimitive, y: L.Atom): (L.Atom) => (L.Atom => L.Tree) => L.Tree = {
    v: L.Atom => 
      {callback: (L.Atom => L.Tree) => 
        val t = Symbol.fresh("t")
        L.LetP(t, op, Seq(v, y), callback(L.AtomN(t)))
      }
        
  }
  val add1: L.Atom => (L.Atom => L.Tree) => L.Tree = intOp(CPSAdd, one)
  val sl1: IntBoxer = intOp(CPSShiftLeft, one)
  val min1: IntBoxer = intOp(CPSSub, one)
  def add12(v: H.Atom)(callback: L.Atom => L.Tree): L.Tree = {
    val t = Symbol.fresh("t")
    L.LetP(t, CPSAdd, Seq(apply_(v), one), callback(L.AtomN(t)))
  }
  def apply(tree: H.Tree): L.Tree = tree match {
    case H.LetP(name: H.Name, p@L3IntAdd, Seq(x,y ) , body) => 
      tempLetP(CPSXOr, Seq(apply_(x), L.AtomL(1))){ux => 
        L.LetP(name, CPSAdd, Seq(ux, apply_(y)), apply(body))
      }
    case H.LetP(name, L3BlockAlloc(tag), Seq(arg), body) => 
      val t1 = Symbol.fresh("t1_Alloc")
      L.LetP(t1, CPSShiftRight, Seq(apply_(arg), L.AtomL(1)), 
            L.LetP(name,CPSBlockAlloc(tag) , Seq(L.AtomN(t1)), apply(body)))
    
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
    case H.LetF(functions, body) => L.LetF(functions.map{
      case H.Fun(name, retC, args, body) => L.Fun(name, retC, args, apply(body))
    }, apply(body))

    case H.AppF(fun, retC, args) => L.AppF(apply_(fun), retC, args.map(apply_))
    //Arithmetic primitives
    case H.LetP(name, L3IntAdd, atoms@Seq(_, _), body) => 
      val t1 = Symbol.fresh("t1")
      L.LetP(t1, CPSAdd, atoms.map(apply_), 
        L.LetP(name, CPSSub, Seq(L.AtomN(t1), one),
          apply(body)
      ))
    case H.LetP(name, L3IntSub, atoms@Seq(_, _), body) => 
      val t1 = Symbol.fresh("t1")
      L.LetP(t1, CPSSub, atoms.map(apply_),
        L.LetP(name, CPSAdd, Seq(L.AtomN(t1), one), 
          apply(body)
        )
      )
    case H.LetP(name, L3IntMul, atoms@Seq(v1, v2), body) =>
      val n = Symbol.fresh("n")
      val m = Symbol.fresh("m")
      val x = Symbol.fresh("x")
      L.LetP(n, CPSSub, Seq(apply_(v1), one), 
        L.LetP(m, CPSShiftRight, Seq(apply_(v2), one), 
          L.LetP(x, CPSMul, Seq(L.AtomN(n), L.AtomN(m)), 
            L.LetP(name, CPSAdd, Seq(L.AtomN(x), one), 
              apply(body)
            )
          )
        )
      )
     /*
      2(([n]-1)/2 / ([m] - 1)/2) + 1
    = 2(([n] - 1) / ([m] - 1)) + 1
    = ([n] - 1) << 1 / ([m] - 1) + 1
    = ([n] - 1) 
     */ 
    case H.LetP(name, L3IntDiv, atoms@Seq(v1, v2), body) => 
      min1(apply_(v1)){t1: L.Atom => 
        sl1(t1){t2: L.Atom => 
          min1(apply_(v2)){t2: L.Atom => 
            val r = Symbol.fresh("r")
            L.LetP(r, CPSDiv, Seq(t1, t2), 
              L.LetP(name, CPSAdd, Seq(L.AtomN(r), one), apply(body))
            )
          }
        }
      }
    case H.LetP(name, L3IntMod, atoms@Seq(v1, v2), body) => 
      val s1 = Symbol.fresh("s")
      val s2 = Symbol.fresh("s")
      val mod = Symbol.fresh("mod")
      val l = Symbol.fresh("l")
      L.LetP(s1, CPSShiftRight, Seq(apply_(v1), one),
        L.LetP(s2, CPSShiftRight, Seq(apply_(v2), one),
          L.LetP(mod, CPSMod, Seq(L.AtomN(s1), L.AtomN(s2)),
            L.LetP(l, CPSShiftLeft, Seq(L.AtomN(mod), one),
              L.LetP(name, CPSAdd, Seq(L.AtomN(l), one),
                apply(body)
              )
            )
          )
        )
      )
    case H.LetP(name, L3IntShiftLeft, atoms@Seq(v1, v2), body) => 
      val t1 = Symbol.fresh("t1")
      val t2 = Symbol.fresh("t2")
      val shift = Symbol.fresh("s")
      L.LetP(t1, CPSSub, Seq(apply_(v1), one),
        L.LetP(t2, CPSShiftRight, Seq(apply_(v2), one),
          L.LetP(shift, CPSShiftLeft, Seq(L.AtomN(t1), L.AtomN(t2)),
            L.LetP(name, CPSAdd, Seq(L.AtomN(shift), one),
              apply(body)
            )
          )
        )
      )
    case H.LetP(name, L3IntShiftRight, atoms@Seq(v1, v2), body) =>
      val t1 = Symbol.fresh("t1")
      val t2 = Symbol.fresh("t2")
      val shift = Symbol.fresh("s")
      L.LetP(t1, CPSSub, Seq(apply_(v1), one),
        L.LetP(t2, CPSShiftRight, Seq(apply_(v2), one), 
          L.LetP(shift, CPSShiftRight, Seq(L.AtomN(t1), L.AtomN(t2)),
            L.LetP(name, CPSAdd, Seq(L.AtomN(shift), one),
              apply(body)
            )
          )
        )
      )
    case H.LetP(name, L3IntBitwiseAnd, atoms@Seq(_, _), body)=> 
      L.LetP(name, CPSAnd, atoms.map(apply_), apply(body))
    case H.LetP(name, L3IntBitwiseOr, atoms@Seq(_, _), body) =>
      L.LetP(name, CPSOr, atoms.map(apply_), apply(body))
    case H.LetP(name, L3IntBitwiseXOr, atoms@Seq(_, _), body) =>
      val tmp = Symbol.fresh("t")
      L.LetP(tmp, CPSXOr, atoms.map(apply_), 
        L.LetP(name, CPSOr, Seq(L.AtomN(tmp), one), apply(body))
      )
    //  val n = Symbol.fresh("n")

    /*
    2(([n] - 1)/2 % ([m] - 1)/2) + 1
    */
    //Logical primitives
    case H.If(L3IntP, Seq(v), ct, cf) => 
      val t1 = Symbol.fresh("t1")
      L.LetP(t1, CPSAnd, Seq(L.AtomN(t1), apply_(v)), 
          L.If(CPSEq, 
            Seq(L.AtomN(t1), one),
              ct, cf))
    case H.If(L3IntLt, atoms@Seq(_, _), ct, cf) =>
      L.If(CPSLt, atoms.map(apply_), ct, cf) 
    case H.If(L3IntLe, atoms@Seq(_, _), ct, cf) =>
      L.If(CPSLe, atoms.map(apply_), ct, cf) 
    case H.If(L3Eq, atoms@Seq(_, _), ct, cf) => 
      L.If(CPSEq, atoms.map(apply_), ct, cf)
    case H.If(L3UnitP, atom@Seq(v), ct, cf) => 
      L.If(CPSEq, Seq(apply_(v), lowLiteral(2)), ct, cf)
    case H.If(L3BoolP, Seq(v), ct, cf) =>
      val t = Symbol.fresh("t")
      L.LetP(t, CPSAnd, Seq(apply_(v), lowLiteral(0xF)),
        L.If(CPSEq, Seq(L.AtomN(t), lowLiteral(0xA)), ct, cf)
      )
      /*val t = Symbol.fresh("t")
      L.LetP(t, CPSEq, Seq(apply_(v), lowLiteral(2)), 
        L.If()
      )*/
    /*Blocks*/
    case H.If(L3BlockP, Seq(v), ct, cf) =>  
      val unboxed = Symbol.fresh("u")
      L.LetP(unboxed, CPSAnd, Seq(apply_(v), lowLiteral(3)), 
        L.If(CPSEq, Seq(L.AtomN(unboxed), lowLiteral(0)), ct, cf)
      )
    case H.LetP(name, L3BlockAlloc(tag), Seq(v), body) => 
      val unboxed = Symbol.fresh("u")
      L.LetP(unboxed, CPSShiftRight, Seq(apply_(v), one),
        L.LetP(name, CPSBlockAlloc(tag), Seq(L.AtomN(unboxed)), apply(body))
      )
    case H.LetP(name, L3BlockTag, Seq(v), body) => 
      val t1 = Symbol.fresh("t1")
      val t2 = Symbol.fresh("t2")
      L.LetP(t1, CPSBlockTag, Seq(apply_(v)),
        L.LetP(t2, CPSShiftLeft, Seq(L.AtomN(t1), one),
          L.LetP(name, CPSAdd, Seq(L.AtomN(t2), one),
            apply(body)
          )
        )
      )
    case H.LetP(name, L3BlockLength, Seq(v), body) => 
      val t1 = Symbol.fresh("t")
      val t2 = Symbol.fresh("t")
      L.LetP(t1, CPSBlockLength, Seq(apply_(v)),
        L.LetP(t2, CPSShiftLeft, Seq(L.AtomN(t1), one),
          L.LetP(name, CPSAdd, Seq(L.AtomN(t2), one),
            apply(body)
          )
        )
      )
    case H.LetP(name, L3BlockGet, Seq(v1, v2), body) => 
      val t1 = Symbol.fresh("t")
      val t2 = Symbol.fresh("t")
      L.LetP(t1, CPSShiftRight, Seq(apply_(v1), one),
        L.LetP(t2, CPSShiftRight, Seq(apply_(v2), one),
          L.LetP(name, CPSBlockGet, Seq(L.AtomN(t1), L.AtomN(t2)),
              apply(body)
          )
        )
      )
    case H.LetP(name, L3BlockSet, Seq(v1, v2, v3), body) => 
      val t1 = Symbol.fresh("t")
      val t2 = Symbol.fresh("t")
      val t3 = Symbol.fresh("t")
      L.LetP(t1, CPSShiftRight, Seq(apply_(v1), one), 
        L.LetP(t2, CPSShiftRight, Seq(apply_(v2), one),
          L.LetP(t3, CPSShiftRight, Seq(apply_(v3), one),
            apply(body)
          )
        )
      )
    //bytes
    case H.LetP(name, L3ByteRead, Seq(), body) => 
      val t1 = Symbol.fresh("t1")
      L.LetP(t1, CPSByteRead, Seq(), 
        sl1(L.AtomN(t1)){t2: L.Atom => 
          L.LetP(name, CPSAdd, Seq(t2, one), 
            apply(body)
          )
        }
      )
    /*
      L
    */
    case H.LetP(name, L3ByteWrite, Seq(v), body) => 
      val unboxed = Symbol.fresh("u")
      L.LetP(unboxed, CPSShiftRight, Seq(apply_(v), one),
        L.LetP(name, CPSByteWrite, Seq(L.AtomN(unboxed)), 
          apply(body)
        )
      )
    //chars
    case H.LetP(name, L3CharToInt, Seq(v1), e) => 
      L.LetP(name, CPSShiftRight, Seq(apply_(v1), lowLiteral(2)), 
        apply(e)
      )
    case H.LetP(name, L3IntToChar, Seq(v1), e) => 
      val t1 = Symbol.fresh("t1")
      L.LetP(t1, CPSShiftLeft, Seq(apply_(v1), lowLiteral(2)), 
        L.LetP(name, CPSAdd, Seq(L.AtomN(t1), lowLiteral(2)), 
          apply(e)
        )
      )
    case H.If(L3CharP, Seq(v), ct, cf) => 
      val unboxed = Symbol.fresh("u")
      L.LetP(unboxed, CPSAnd, Seq(apply_(v), lowLiteral(7)), 
        L.If(CPSEq, Seq(L.AtomN(unboxed), lowLiteral(6)), 
          ct, cf
        )
      )
    case H.Halt(atom) => 
      val raw = Symbol.fresh("r")
      L.LetP(raw, CPSShiftRight, Seq(apply_(atom), unboxedOne),
        L.Halt(L.AtomN(raw))
      )
    case H.LetP(name, L3Id, Seq(v), body) => 
      L.LetP(name, CPSId, Seq(apply_(v)), 
        apply(body)
      )
    case x => println(x); ???
  }

  def tempLetP(p: L.ValuePrimitive, args: Seq[L.Atom])(body: L.AtomN => L.Tree): L.Tree = {
      val tmp = Symbol.fresh("ux")
      L.LetP(tmp, p,args, body(L.AtomN(tmp)))
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
