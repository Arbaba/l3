package l3

/**
  * A class for L₃ primitives.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

sealed abstract class L3Primitive(val name: String, val arity: Int) {
  override def toString: String = name
}

sealed abstract class L3ValuePrimitive(name: String, arity: Int)
    extends L3Primitive(name, arity)
sealed abstract class L3TestPrimitive(name: String, arity: Int)
    extends L3Primitive(name, arity)

// Primitives on blocks
case class L3BlockAlloc(tag: L3BlockTag)
    extends L3ValuePrimitive(s"block-alloc-${tag}", 1)
case object L3BlockP extends L3TestPrimitive("block?", 1)
case object L3BlockTag extends L3ValuePrimitive("block-tag", 1)
case object L3BlockLength extends L3ValuePrimitive("block-length", 1)
case object L3BlockGet extends L3ValuePrimitive("block-get", 2)
case object L3BlockSet extends L3ValuePrimitive("block-set!", 3)

// Primitives on integers
case object L3IntP extends L3TestPrimitive("int?", 1)

case object L3IntAdd extends L3ValuePrimitive("+", 2)
case object L3IntSub extends L3ValuePrimitive("-", 2)
case object L3IntMul extends L3ValuePrimitive("*", 2)
case object L3IntDiv extends L3ValuePrimitive("/", 2)
case object L3IntMod extends L3ValuePrimitive("%", 2)

case object L3IntShiftLeft extends L3ValuePrimitive("shift-left", 2)
case object L3IntShiftRight extends L3ValuePrimitive("shift-right", 2)
case object L3IntBitwiseAnd extends L3ValuePrimitive("and", 2)
case object L3IntBitwiseOr extends L3ValuePrimitive("or", 2)
case object L3IntBitwiseXOr extends L3ValuePrimitive("xor", 2)


case object L3IntLt extends L3TestPrimitive("<", 2)
case object L3IntLe extends L3TestPrimitive("<=", 2)


case object L3ByteRead extends L3ValuePrimitive("byte-read", 0)
case object L3ByteWrite extends L3ValuePrimitive("byte-write", 1)

case object L3IntToChar extends L3ValuePrimitive("int->char", 1)

// Primitives on characters
case object L3CharP extends L3TestPrimitive("char?", 1)

case object L3CharToInt extends L3ValuePrimitive("char->int", 1)

// Primitives on booleans
case object L3BoolP extends L3TestPrimitive("bool?", 1)

// Primitives on unit
case object L3UnitP extends L3TestPrimitive("unit?", 1)

// Primitives on arbitrary values

case object L3Eq extends L3TestPrimitive("=", 2)
case object L3Id extends L3ValuePrimitive("id", 1)

object L3Primitive {
  def isDefinedAt(name: String): Boolean =
    byName isDefinedAt name

  def isDefinedAt(name: String, arity: Int): Boolean =
    (byName isDefinedAt name) && (byName(name).arity == arity)

  def apply(name: String): L3Primitive =
    byName(name)

  private val blockAllocators = for (i <- 0 to 200) yield L3BlockAlloc(i)

  // Note: private primitives (id and block-alloc-n for n > 200) are ommitted
  // on purpose from this map, as they are not meant to be used by user code.
  private val byName: Map[String, L3Primitive] =
    Map((Seq(L3BlockP, L3BlockTag, L3BlockLength, L3BlockGet, L3BlockSet,
             L3IntP, L3IntAdd, L3IntSub, L3IntMul, L3IntDiv, L3IntMod,
             L3IntShiftLeft, L3IntShiftRight,
             L3IntBitwiseAnd, L3IntBitwiseOr, L3IntBitwiseXOr,
             L3IntLt, L3IntLe, L3Eq, L3IntToChar,
             L3CharP, L3ByteRead, L3ByteWrite, L3CharToInt,
             L3BoolP,
             L3UnitP) ++ blockAllocators)
        map { p => (p.name, p) } : _*)
}
