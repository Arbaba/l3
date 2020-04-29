package l3

import scala.collection.mutable.{ Map => MutableMap }

abstract class CPSOptimizer[T <: CPSTreeModule { type Name = Symbol }]
  (val treeModule: T) {
  import treeModule._
  protected def rewrite(tree: Tree): Tree = {
    val simplifiedTree = fixedPoint(tree)(shrink)
    val maxSize = size(simplifiedTree) * 3 / 2
    fixedPoint(simplifiedTree, 8) { t => inline(t, maxSize) }
  }

  private case class Count(applied: Int = 0, asValue: Int = 0)

  private case class State(
    census: Map[Name, Count],
    aSubst: Subst[Atom] = emptySubst,
    cSubst: Subst[Name] = emptySubst,
    eInvEnv: Map[(ValuePrimitive, Seq[Atom]), Atom] = Map.empty, //Map from primitives and arguments to names -> for common sub expr elimination
    cEnv: Map[Name, Cnt] = Map.empty,
    fEnv: Map[Name, Fun] = Map.empty) {

    def dead(s: Name): Boolean =
      ! census.contains(s)
    def appliedOnce(s: Name): Boolean =
      census.get(s).contains(Count(applied = 1, asValue = 0))

    def withASubst(from: Atom, to: Atom): State =
      copy(aSubst = aSubst + (from -> aSubst(to)))
    def withASubst(from: Name, to: Atom): State =
      withASubst(AtomN(from), to)
    def withASubst(from: Name, to: Literal): State =
      withASubst(from, AtomL(to))
    def withASubst(from: Seq[Name], to: Seq[Atom]): State =
      copy(aSubst = aSubst ++ (from.map(AtomN) zip to.map(aSubst)))

    def withCSubst(from: Name, to: Name): State =
      copy(cSubst = cSubst + (from -> cSubst(to)))

    def withExp(atom: Atom, prim: ValuePrimitive, args: Seq[Atom]): State =
      copy(eInvEnv = eInvEnv + ((prim, args) -> atom))
    def withExp(name: Name, prim: ValuePrimitive, args: Seq[Atom]): State =
      withExp(AtomN(name), prim, args)

    def withCnts(cnts: Seq[Cnt]): State =
      copy(cEnv = cEnv ++ (cnts.map(_.name) zip cnts))
    def withFuns(funs: Seq[Fun]): State =
      copy(fEnv = fEnv ++ (funs.map(_.name) zip funs))
    def substitute(tree: Tree)(implicit ctx: Map[Atom, Atom]): Tree = {
      def subst(atom: Atom): Atom = atom match {
        case AtomL(_) => atom
        case AtomN(n) => {
          val tmp = ctx.getOrElse(atom,atom)
          println(s"substituting $atom with $tmp")
          tmp
        }
      }  
      def substCnt(c: Cnt) = c match {
        case Cnt(name, args, e) => Cnt(name, args, substitute(e))
      }
      def substFun(f: Fun) = f match {
        case Fun(name, ret, args, body) => Fun(name, ret, args, substitute(body))
      }
      tree match  {
        case LetP(n, p, v, e) => LetP(n, p, v.map{a => subst(a)}, substitute(e))
        case LetC(cs, e) => LetC(cs.map(substCnt), substitute(e))
        case LetF(fs, e) => LetF(fs.map(substFun), substitute(e))
        
        case AppC(c, atoms) => AppC(c, atoms.map{a => subst(a)}) 
        case AppF(v, c, vs) => AppF(subst(v), c, vs.map(subst))
        case If(a, v, b, c) => If(a, v.map(subst), b,c) 
        case Halt(atom) => Halt(subst(atom))
        //case atom: Atom => subst(atom)  
      }  
    }
  }

  // Shrinking optimizations

  private def shrink(tree: Tree): Tree ={
    println(s"shrinking $tree...")
    val res = shrink(tree, State(census(tree)))
    println(s"[RESULT] $res")
    res
}
  private def shrink(tree: Tree, s: State): Tree = {
    def toLits(a: Seq[Atom]) = a.flatMap(_.asLiteral) 
      
      println(s"[processing]> $tree with ${s.fEnv.keys}"); (tree) match {
        case halt@Halt(at@AtomN(name)) => (s.cSubst.get(name), s.aSubst.get(at)) match {
          case (Some(otherName), None) => Halt(AtomN(otherName))
          case (None, Some(otherAtom)) => Halt(otherAtom)
          case _ => halt
        }
        case LetF(funs, body) => {
          val (unchangedFuns, inlinedFuns) = funs.partition(f => s.appliedOnce(f.name))
          
          val newState = s.withFuns(inlinedFuns)
          println(s"inlined ${inlinedFuns.size} funs: $inlinedFuns; newState ${newState.fEnv.keys}")
          LetF(unchangedFuns, shrink(body, newState))
        }
        case LetC(cnts, body) => {
          val (untouchedCnts, inlinedCnts) = cnts.partition(c => s.appliedOnce(c.name))
          val newState = s.withCnts(inlinedCnts)
          println(s"inlined ${inlinedCnts.size} cnts: $inlinedCnts; new State ${newState.cEnv.keys}")
          LetC(untouchedCnts, shrink(body, newState))
        }
        case appc@AppC(cnt, args) if s.cSubst.contains(cnt) => {
          val newName = s.cSubst(cnt)
          println(s"replacing $cnt with ${newName}")
          shrink(AppC(newName, args), s) 
        } 
        case appc@AppC(cnt, args) => s.cEnv.get(cnt) match {
          case Some(inlinedCnt@Cnt(name, currentArgs, body)) => {
            val newState = s.withASubst(currentArgs, args)
            println(s"inlining cnt $name in $cnt")
            shrink(body, newState)
          }
          case None => {
            println(s"didn0t sub $cnt in ${s.cSubst.keys} ${s.aSubst.keys}")
            appc
          }
        }
        case appf@AppF(fun@AtomN(fName), retC, args) if s.aSubst.contains(fun) => {
          val newName = s.aSubst(fun)
          println(s"replacing $fName with $newName")
          shrink(AppF(newName, retC, args), s)
        }
        case appf@AppF(fun@AtomN(fName), retC, args) if s.cSubst.contains(fName) => {
          val newName = s.cSubst(fName)
          println(s"replacing $fName with $newName")
          shrink(AppF(AtomN(newName), retC, args), s)
        }
        case appf@AppF(fun@AtomN(fName), retC, args) => s.fEnv.get(fName) match {
          case Some(inlinable@Fun(inName, inRet, inArgs, inBody)) => {
            println(s"inlining $fName")
            shrink(inBody, s.withASubst(inArgs, args).withCSubst(inName, fName).withCSubst(inRet, retC))
          }
            
          case None => {
            println(s"$fName not inlined; env is ${s.fEnv.keys} ${s.aSubst.keys} ${s.cSubst.keys}")
            appf
          }
        }
        case LetP(name, prim, lits@Seq(AtomL(l1), AtomL(l2)), body) 
            if vEvaluator.isDefinedAt((prim,toLits(lits)))  =>
            println("constant folding")
            //constant folding arithmetic
            val cf = (vEvaluator)((prim, toLits(lits)))
            shrink(body, s.withASubst(name, cf))
        case LetP(name, this.identity, Seq(AtomN(sameName)), body) => {
          val newState = s.withCSubst(name, sameName)
           println(s"substituting $name for $sameName; env: ${newState.fEnv.keys}")
           shrink(body, newState)
         }
        case letp@LetP(name, prim, args, body) => {
          val updatedArgs = args.map(arg => s.aSubst.getOrElse(arg, arg))
          println(s"$tree before $args after $updatedArgs")
          LetP(name, prim, updatedArgs, shrink(body, s))
        }
        case LetC(cnts, body) => {
          LetC(cnts, shrink(body, s))
        }
        //name substitution
        case If(_, args, ct, cf) if s.cSubst.keys.toSet.contains(Set(ct, cf)) => {
          val newState = s
          println(s"substituting if")
          tree//shrink(If(args, ct, cf), s)
        }
        case If(cond,  lits@Seq(AtomL(l1), AtomL(l2)), ct, cf) 
            if cEvaluator.isDefinedAt((cond, toLits(lits)))  => {
              //constant folding boolean literals 
              println(s"constant folding")
              if((cEvaluator)((cond,  toLits(lits)))){
                shrink(AppC(ct, Seq()), s)
              }else {
                shrink(AppC(cf, Seq()), s)
              }
        }
              
        case If(cond,  Seq(v1, v2), ct, cf)  
          if v1 == v2  => {
            println(s"constant folding..")
            if(sameArgReduceC(cond)){
              shrink(AppC(ct, Seq()), s)
            }else {
              shrink(AppC(cf, Seq()), s)
            }
         }   
        case i@If(_, args, ct, cf) => {
          println(s"couldnt find $ct $cf in ${s.cSubst.keys} ${s.aSubst.keys}")
          i
        }
        //constant folding equal boolean values 
        
          /** Constant folding **/
          /*
          case LetP(name, prim, lits@Seq(v1, v2), body) 
            if v1 == v2 && sameArgReduce.isDefinedAt((prim,v1))  =>
              //constant folding equal arithmetic values or variables
              val result = (sameArgReduce)((prim, v1))
              val fold = s.substitute(body)(Map(AtomN(name) -> result))
              shrink(fold, s.withASubst(name, result))
          
          case If(cond,  lits@Seq(AtomL(l1), AtomL(l2)), ct, cf) 
            if cEvaluator.isDefinedAt((cond, toLits(lits)))  =>
              //constant folding boolean literals 
              if((cEvaluator)((cond,  toLits(lits)))){
                AppC(ct, Seq())
              }else {
                AppC(cf, Seq())
              }*/
          /* Neutral and absorbing elements */
          /*case LetP(name, prim, lits@Seq(AtomL(v1),v2), body) 
            if leftNeutral.contains((v1, prim)) => 
              shrink(s.substitute(body)(Map(AtomN(name) -> v2)), s.withASubst(name, v2))
         case LetP(name, prim, lits@Seq(v1,AtomL(v2)), body) 
            if rightNeutral.contains((prim, v2)) => 
              shrink(s.substitute(body)(Map(AtomN(name) -> v1)), s.withASubst(name, v1))
         case LetP(name, prim, lits@Seq(a1@AtomL(v1),_), body) 
            if leftAbsorbing.contains((v1, prim)) => 
              shrink(s.substitute(body)(Map(AtomN(name) -> a1)), s.withASubst(name, a1))
         case LetP(name, prim, lits@Seq(_,a2@AtomL(v2)), body) 
            if rightAbsorbing.contains((prim,v2)) => 
              shrink(s.substitute(body)(Map(AtomN(name) -> a2)), s.withASubst(name, a2))*/
         /*case LetP(name, this.identity, Seq(v), body) => {
           println(s"substituting $name $v")
           val tmp = s.substitute(body)(Map(AtomN(name) -> v))
           println(s"[TEST] $tmp")
           shrink(tmp, s)
         }*/
            
              
          /* Common subexpression elimination */
          /*case LetP(name, prim, args, body)   =>
            //common subexpression elimination
            val n1 = s.eInvEnv.get((prim, args))
            val cse = n1 match {
              case Some(n) => 
                shrink(s.substitute(body)(Map(AtomN(name) -> n)), s)
              case None =>
                val state = if(impure(prim)) s else s.withExp(name, prim, args)
                LetP(name, prim, args, shrink(body, state))
            }
            cse*/
          /* Dead code elimination */
          /*case LetC(cnts, body) => {
            println(s"letc ${cnts.filter(c => s.appliedOnce(c.name)).size}")
            LetC(cnts, shrink(body))
          }
          case LetF(funs, body) => {
            println(s"letf ${funs.filter(f => s.appliedOnce(f.name)).size}")
            LetF(funs.filter(f => !s.appliedOnce(f.name)), shrink(body))
          }
          case appf@AppF(fun@AtomN(fName), retC, args) => s.fEnv.get(fName) match {
            case Some(Fun(name, rC, as, body)) => {
              println(s"shrinking inlining")
              val m: Map[Atom, Atom] = as.map(AtomN).zip(args).toMap
              s.substitute(body)(m + (AtomN(rC) -> AtomN(retC)))
            }
            case None => appf
          }*/
              //case LetC(cnts, body) => LetC(cnts, shrink(body, s.withCnts(cnts)))
          /*case LetF(funs, body) => {
            println(s"shrinking ${funs.map(_.name)}")
            LetF(funs, shrink(body))
          }*/
            /*case appf@AppF(AtomN(f), ret, args) => s.fEnv.get(f) match {
              case Some(Fun(n, r, a, b)) => 
                println("inlining...")
                tree
              case None => {
                println(s"not found in ${s.fEnv.keys} [$f]")
                appf
              }
            }*/
          case _ => 
            tree
            
      
    }
  }

  // (Non-shrinking) inlining

  private def inline(tree: Tree, maxSize: Int): Tree = {
    def copyT(tree: Tree, subV: Subst[Atom], subC: Subst[Name]): Tree = {
      (tree: @unchecked) match {
        case LetP(name, prim, args, body) =>
          val name1 = name.copy
          LetP(name1, prim, args map subV,
               copyT(body, subV + (AtomN(name) -> AtomN(name1)), subC))
        case LetC(cnts, body) =>
          val names = cnts map (_.name)
          val names1 = names map (_.copy)
          val subC1 = subC ++ (names zip names1)
          LetC(cnts map (copyC(_, subV, subC1)), copyT(body, subV, subC1))
        case LetF(funs, body) =>
          val names = funs map (_.name)
          val names1 = names map (_.copy)
          val subV1 = subV ++ ((names map AtomN) zip (names1 map AtomN))
          LetF(funs map (copyF(_, subV1, subC)), copyT(body, subV1, subC))
        case AppC(cnt, args) =>
          AppC(subC(cnt), args map subV)
        case AppF(fun, retC, args) =>
          AppF(subV(fun), subC(retC), args map subV)
        case If(cond, args, thenC, elseC) =>
          If(cond, args map subV, subC(thenC), subC(elseC))
        case Halt(arg) =>
          Halt(subV(arg))
      }
    }

    def copyC(cnt: Cnt, subV: Subst[Atom], subC: Subst[Name]): Cnt = {
      val args1 = cnt.args map (_.copy)
      val subV1 = subV ++ ((cnt.args map AtomN) zip (args1 map AtomN))
      Cnt(subC(cnt.name), args1, copyT(cnt.body, subV1, subC))
    }

    def copyF(fun: Fun, subV: Subst[Atom], subC: Subst[Name]): Fun = {
      val retC1 = fun.retC.copy
      val subC1 = subC + (fun.retC -> retC1)
      val args1 = fun.args map (_.copy)
      val subV1 = subV ++ ((fun.args map AtomN) zip (args1 map AtomN))
      val AtomN(funName1) = subV(AtomN(fun.name))
      Fun(funName1, retC1, args1, copyT(fun.body, subV1, subC1))
    }

    val fibonacci = Seq(1, 2, 3, 5, 8, 13)

    val trees = LazyList.iterate((0, tree), fibonacci.length){ case (i, tree) =>
      val funLimit = fibonacci(i)
      val cntLimit = i

      def sameLen[T,U](formalArgs: Seq[T], actualArgs: Seq[U]): Boolean =
        formalArgs.length == actualArgs.length

      def inlineT(tree: Tree)(implicit s: State): Tree = tree match {
        /*case AppF(AtomN(fName), retC, args) if s.fEnv.contains(fName) => {
          val fun = s.fEnv(fName)
          inlineT(fun.body)(s.withASubst(fun.retC, AtomN(retC)).withASubst(fun.args, args))
        }
        case AppC(cName, args) if s.cEnv.contains(cName) => {
          val cnt = s.cEnv(cName)
          println("...inlining cnt...")
          inlineT(cnt.body)
        } 
        case LetF(funs, body) => {
          //println(s"adding ${funs.map(_.name)}...")
          LetF(funs, 
            inlineT(body)(s.withFuns(funs))
          )
        }
        case LetC(cnts, body) => LetC(cnts, inlineT(body)(s.withCnts(cnts)))
        case LetP(name, prim, args, body) => LetP(name, prim, args, inlineT(body))
        case appf@AppF(AtomN(fName), _, _) => {
          //println(s"appf $fName not found in ${s.fEnv.keys}")
          appf
        }
        case appc@AppC((cName), _) => {
          //println(s"appc $cName not found in ${s.cEnv.keys}")
          appc
        }*/
        //Cnt and Fun are not inlined
        case _ => tree
      }

      (i + 1, fixedPoint(inlineT(tree)(State(census(tree))))(shrink))
    }
    trees.takeWhile{ case (_, tree) => size(tree) <= maxSize }.last._2
  }

  // Census computation
  private def census(tree: Tree): Map[Name, Count] = {
    val census = MutableMap[Name, Count]().withDefault(_ => Count())
    val rhs = MutableMap[Name, Tree]()

    def incAppUseN(name: Name): Unit = {
      val currCount = census(name)
      census(name) = currCount.copy(applied = currCount.applied + 1)
      rhs.remove(name).foreach(addToCensus)
    }

    def incAppUseA(atom: Atom): Unit =
      atom.asName.foreach(incAppUseN(_))

    def incValUseN(name: Name): Unit = {
      val currCount = census(name)
      census(name) = currCount.copy(asValue = currCount.asValue + 1)
      rhs.remove(name).foreach(addToCensus)
    }

    def incValUseA(atom: Atom): Unit =
      atom.asName.foreach(incValUseN(_))

    def addToCensus(tree: Tree): Unit = (tree: @unchecked) match {
      case LetP(_, _, args, body) =>
        args foreach incValUseA; addToCensus(body)
      case LetC(cnts, body) =>
        rhs ++= (cnts map { c => (c.name, c.body) }); addToCensus(body)
      case LetF(funs, body) =>
        rhs ++= (funs map { f => (f.name, f.body) }); addToCensus(body)
      case AppC(cnt, args) =>
        incAppUseN(cnt); args foreach incValUseA
      case AppF(fun, retC, args) =>
        incAppUseA(fun); incValUseN(retC); args foreach incValUseA
      case If(_, args, thenC, elseC) =>
        args foreach incValUseA; incValUseN(thenC); incValUseN(elseC)
      case Halt(arg) =>
        incValUseA(arg)
    }

    addToCensus(tree)
    census.toMap
  }

  private def size(tree: Tree): Int = (tree: @unchecked) match {
    case LetP(_, _, _, body) => size(body) + 1
    case LetC(cs, body) => (cs map { c => size(c.body) }).sum + size(body)
    case LetF(fs, body) => (fs map { f => size(f.body) }).sum + size(body)
    case AppC(_, _) | AppF(_, _, _) | If(_, _, _, _) | Halt(_) => 1
  }

  protected val impure: ValuePrimitive => Boolean
  protected val unstable: ValuePrimitive => Boolean

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal]
  protected val blockTag: ValuePrimitive
  protected val blockLength: ValuePrimitive

  protected val identity: ValuePrimitive

  protected val leftNeutral: Set[(Literal, ValuePrimitive)]
  protected val rightNeutral: Set[(ValuePrimitive, Literal)]
  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)]
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)]

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom]
  protected val sameArgReduceC: TestPrimitive => Boolean

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal]
  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean]
}

object CPSOptimizerHigh extends CPSOptimizer(SymbolicCPSTreeModule)
    with (SymbolicCPSTreeModule.Tree => SymbolicCPSTreeModule.Tree) {
  import treeModule._

  def apply(tree: Tree): Tree =
    rewrite(tree)

  import scala.language.implicitConversions
  private[this] implicit def l3IntToLit(i: L3Int): Literal = IntLit(i)
  private[this] implicit def intToLit(i: Int): Literal = IntLit(L3Int(i))

  protected val impure: ValuePrimitive => Boolean = Set(L3ByteRead, L3ByteWrite, L3BlockSet)

  protected val unstable: ValuePrimitive => Boolean = {
    case L3BlockAlloc(_) | L3BlockGet | L3ByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case L3BlockAlloc(tag) => tag
  }
  protected val blockTag: ValuePrimitive = L3BlockTag
  protected val blockLength: ValuePrimitive = L3BlockLength

  protected val identity: ValuePrimitive = L3Id
  private def int(x: Int) = intToLit(x)
  protected val leftNeutral: Set[(Literal, ValuePrimitive)] = 
    Set((int(0), L3IntAdd), (int(1), L3IntMul), (int(0), L3IntBitwiseOr), (int(0), L3IntBitwiseXOr), (int(~0), L3IntBitwiseAnd))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] = 
      Set((L3IntAdd, int(0)), (L3IntSub, int(0)), (L3IntMul, int(1)), (L3IntDiv, int(1)),
        (L3IntShiftLeft, int(0)), (L3IntShiftRight, int(0)),
        (L3IntBitwiseAnd, int(~0)), (L3IntBitwiseOr, int(0)), (L3IntBitwiseXOr, int(0)))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] = 
      Set((int(0), L3IntMul), (int(0), L3IntDiv),
        (int(0), L3IntShiftLeft), (int(0), L3IntShiftRight),
        (int(0), L3IntBitwiseAnd), (int(~0), L3IntBitwiseOr))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =    
    Set((L3IntMul, int(0)), (L3IntBitwiseAnd, int(0)), (L3IntBitwiseOr, int(~0)))
  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] = {
    case (L3IntBitwiseAnd | L3IntBitwiseOr, a) => a
    case (L3IntSub | L3IntMod | L3IntBitwiseXOr, _) => AtomL(int(0))
    case (L3IntDiv, _) => AtomL(int(1))
  }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case L3IntLe | L3Eq => true
    case L3IntLt => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    case (L3IntAdd, Seq(IntLit(x), IntLit(y))) => x + y
    case (L3IntSub, Seq(IntLit(x), IntLit(y))) => x - y
    case (L3IntMul, Seq(IntLit(x), IntLit(y))) => x * y
    case (L3IntDiv, Seq(IntLit(x), IntLit(y))) if y.toInt != 0 => x / y
    case (L3IntMod, Seq(IntLit(x), IntLit(y))) if y.toInt != 0 => x % y

    case (L3IntShiftLeft,  Seq(IntLit(x), IntLit(y))) => x << y
    case (L3IntShiftRight, Seq(IntLit(x), IntLit(y))) => x >> y
    case (L3IntBitwiseAnd, Seq(IntLit(x), IntLit(y))) => x & y
    case (L3IntBitwiseOr,  Seq(IntLit(x), IntLit(y))) => x | y
    case (L3IntBitwiseXOr, Seq(IntLit(x), IntLit(y))) => x ^ y
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {
    case (L3IntLt, Seq(IntLit(x), IntLit(y))) => x < y
    case (L3IntLe, Seq(IntLit(x), IntLit(y))) => x <= y
    case (L3Eq, Seq(IntLit(x), IntLit(y))) => x == y
  }
}

object CPSOptimizerLow extends CPSOptimizer(SymbolicCPSTreeModuleLow)
    with (SymbolicCPSTreeModuleLow.LetF => SymbolicCPSTreeModuleLow.LetF) {
  import treeModule._

  def apply(tree: LetF): LetF = rewrite(tree) match {
    case tree @ LetF(_, _) => tree
    case other => LetF(Seq(), other)
  }

  protected val impure: ValuePrimitive => Boolean =
    Set(CPSBlockSet, CPSByteRead, CPSByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case CPSBlockAlloc(_) | CPSBlockGet | CPSByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case CPSBlockAlloc(tag) => tag
  }
  protected val blockTag: ValuePrimitive = CPSBlockTag
  protected val blockLength: ValuePrimitive = CPSBlockLength

  protected val identity: ValuePrimitive = CPSId

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, CPSAdd), (1, CPSMul), (~0, CPSAnd), (0, CPSOr), (0, CPSXOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((CPSAdd, 0), (CPSSub, 0), (CPSMul, 1), (CPSDiv, 1),
        (CPSShiftLeft, 0), (CPSShiftRight, 0),
        (CPSAnd, ~0), (CPSOr, 0), (CPSXOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, CPSMul), (0, CPSDiv),
        (0, CPSShiftLeft), (0, CPSShiftRight),
        (0, CPSAnd), (~0, CPSOr))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((CPSMul, 0), (CPSAnd, 0), (CPSOr, ~0))

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] = {
    case (CPSAnd | CPSOr, a) => a
    case (CPSSub | CPSMod | CPSXOr, _) => AtomL(0)
    case (CPSDiv, _) => AtomL(1)
  }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case CPSLe | CPSEq => true
    case CPSLt => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    case (CPSAdd, Seq(x, y)) => x + y
    case (CPSSub, Seq(x, y)) => x - y
    case (CPSMul, Seq(x, y)) => x * y
    case (CPSDiv, Seq(x, y)) if y.toInt != 0 => x / y
    case (CPSMod, Seq(x, y)) if y.toInt != 0 => x % y

    case (CPSShiftLeft,  Seq(x, y)) => x << y
    case (CPSShiftRight, Seq(x, y)) => x >> y
    case (CPSAnd, Seq(x, y)) => x & y
    case (CPSOr,  Seq(x, y)) => x | y
    case (CPSXOr, Seq(x, y)) => x ^ y
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {
    case (CPSLt, Seq(x, y)) => x < y
    case (CPSLe, Seq(x, y)) => x <= y
    case (CPSEq, Seq(x, y)) => x == y
  }
}
