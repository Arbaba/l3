package l3

import SymbolicCPSTreeModuleLow._

object CPSHoister extends (Tree => LetF) {
  def apply(tree: Tree): LetF = {
    def collectCnt(cnt: Cnt): (Cnt, Seq[Fun]) = {
      val (e, f) = collect(cnt.body, Seq())
      (Cnt(cnt.name, cnt.args, e), f)
    }
    def collectFun(fun: Fun): (Seq[Fun]) = {
      val (e, f) = collect(fun.body, Seq())
      Seq(Fun(fun.name, fun.retC, fun.args, e)) ++ f
    }
    def collect(subTree: Tree, funs: Seq[Fun]): (Tree, Seq[Fun]) = subTree match {
      case LetP(n, p, args, e) => 
        val (e_, fs) = collect(e, funs)
        (LetP(n, p, args, e_), fs)
      case LetC(cnts, body) => 
        val (e, fs) = collect(body, funs)
        val (cnts_, fs1) = cnts.map(collectCnt).unzip
        (LetC(cnts_, e), fs1.flatten++fs)
      case LetF(funs, body) => 
        val (e, f) = collect(body, Seq())
        (e, funs.flatMap(collectFun) ++ f)
      case t => (t, Seq())
    }
    val (subTree, fs) = collect(tree, Seq())
    LetF(fs, subTree)
  }

}
