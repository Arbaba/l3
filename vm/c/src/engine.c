#include <assert.h>
#include <stdio.h>

#include "vmtypes.h"
#include "engine.h"
#include "opcode.h"
#include "memory.h"
#include "fail.h"

typedef enum { Cb, Ib, Lb, Lb1, Lb2, Lb3, Lb4, Ob } reg_bank_t;

static void* memory_start;
static void* memory_end;

static value_t* R[8];          /* (pseudo)base registers */

void engine_setup(void) {
  memory_start = memory_get_start();
  memory_end = memory_get_end();

  engine_set_Lb(memory_start);
  engine_set_Ib(memory_start);
  engine_set_Ob(memory_start);
}

void engine_cleanup(void) {
  // nothing to do
}

void engine_emit(instr_t instr, instr_t** instr_ptr) {
  if ((void*)(*instr_ptr + 1) > memory_end)
    fail("not enough memory to load code");
  **instr_ptr = instr;
  *instr_ptr += 1;
}

value_t* engine_get_Cb(void) { return R[Cb]; }
value_t* engine_get_Ib(void) { return R[Ib]; }
value_t* engine_get_Lb(void) { return R[Lb]; }
value_t* engine_get_Ob(void) { return R[Ob]; }

void engine_set_Cb(value_t* new_value) { R[Cb] = new_value; }
void engine_set_Ib(value_t* new_value) { R[Ib] = new_value; }
void engine_set_Lb(value_t* new_value) {
  for (reg_bank_t pseudo_bank = Lb; pseudo_bank <= Lb4; ++pseudo_bank)
    R[pseudo_bank] = new_value + (pseudo_bank - Lb) * 32;
}
void engine_set_Ob(value_t* new_value) { R[Ob] = new_value; }

// Virtual <-> physical address translation

static void* addr_v_to_p(value_t v_addr) {
  return (char*)memory_start + v_addr;
}

static value_t addr_p_to_v(void* p_addr) {
  assert(memory_start <= p_addr && p_addr <= memory_end);
  return (value_t)((char*)p_addr - (char*)memory_start);
}

// Instruction decoding

static reg_bank_t reg_bank(reg_id_t r) {
  return r >> 5;
}

static unsigned int reg_index(reg_id_t r) {
  return r & 0x1F;
}

static unsigned int instr_extract_u(instr_t instr, int start, int len) {
  return (instr >> start) & ((1 << len) - 1);
}

static int instr_extract_s(instr_t instr, int start, int len) {
  int bits = (int)instr_extract_u(instr, start, len);
  int m = 1 << (len - 1);
  return (bits ^ m) - m;
}

static opcode_t instr_opcode(instr_t instr) {
  unsigned int opcode = instr_extract_u(instr, 27, 5);
  return (opcode_t)opcode;
}

static reg_id_t instr_ra(instr_t instr) {
  return (reg_id_t)instr_extract_u(instr, 0, 8);
}

static reg_id_t instr_rb(instr_t instr) {
  return (reg_id_t)instr_extract_u(instr, 8, 8);
}

static reg_id_t instr_rc(instr_t instr) {
  return (reg_id_t)instr_extract_u(instr, 16, 8);
}

static int instr_d(instr_t instr) {
  return instr_extract_s(instr, 16, 11);
}

// Call/return

static value_t* call(value_t target_pc,
                     value_t ib,
                     value_t lb,
                     value_t ob,
                     value_t ret_pc) {
  R[Ob][0] = ib;
  R[Ob][1] = lb;
  R[Ob][2] = ob;
  R[Ob][3] = ret_pc;
  engine_set_Ib(R[Ob]);
  engine_set_Lb(memory_start);
  engine_set_Ob(memory_start);
  return addr_v_to_p(target_pc);
}

static value_t* ret(value_t ret_value) {
  value_t* ret_pc = addr_v_to_p(R[Ib][3]);
  engine_set_Ob(addr_v_to_p(R[Ib][2]));
  engine_set_Lb(addr_v_to_p(R[Ib][1]));
  engine_set_Ib(addr_v_to_p(R[Ib][0]));
  R[Ob][0] = ret_value;
  return ret_pc;
}

// (Pseudo-)register access

#define Ra (R[reg_bank(instr_ra(*pc))][reg_index(instr_ra(*pc))])
#define Rb (R[reg_bank(instr_rb(*pc))][reg_index(instr_rb(*pc))])
#define Rc (R[reg_bank(instr_rc(*pc))][reg_index(instr_rc(*pc))])

#define GOTO_NEXT goto *labels[instr_opcode(*pc)]

value_t engine_run() {
  instr_t* pc = memory_start;

  void** labels[] =
    {
     [opcode_ADD]     = &&l_ADD,
     [opcode_SUB]     = &&l_SUB,
     [opcode_MUL]     = &&l_MUL,
     [opcode_DIV]     = &&l_DIV,
     [opcode_MOD]     = &&l_MOD,
     [opcode_LSL]     = &&l_LSL,
     [opcode_LSR]     = &&l_LSR,
     [opcode_AND]     = &&l_AND,
     [opcode_OR]      = &&l_OR,
     [opcode_XOR]     = &&l_XOR,
     [opcode_JLT]     = &&l_JLT,
     [opcode_JLE]     = &&l_JLE,
     [opcode_JEQ]     = &&l_JEQ,
     [opcode_JNE]     = &&l_JNE,
     [opcode_JI]      = &&l_JI,
     [opcode_CALL_NI] = &&l_CALL_NI,
     [opcode_CALL_ND] = &&l_CALL_ND,
     [opcode_CALL_TI] = &&l_CALL_TI,
     [opcode_CALL_TD] = &&l_CALL_TD,
     [opcode_RET]     = &&l_RET,
     [opcode_HALT]    = &&l_HALT,
     [opcode_LDLO]    = &&l_LDLO,
     [opcode_LDHI]    = &&l_LDHI,
     [opcode_MOVE]    = &&l_MOVE,
     [opcode_RALO]    = &&l_RALO,
     [opcode_BALO]    = &&l_BALO,
     [opcode_BSIZ]    = &&l_BSIZ,
     [opcode_BTAG]    = &&l_BTAG,
     [opcode_BGET]    = &&l_BGET,
     [opcode_BSET]    = &&l_BSET,
     [opcode_BREA]    = &&l_BREA,
     [opcode_BWRI]    = &&l_BWRI,
    };

  GOTO_NEXT;

 l_ADD: {
    Ra = Rb + Rc;
    pc += 1;
  } GOTO_NEXT;

 l_SUB: {
    Ra = Rb - Rc;
    pc += 1;
  } GOTO_NEXT;

 l_MUL: {
    Ra = Rb * Rc;
    pc += 1;
  } GOTO_NEXT;

 l_DIV: {
    Ra = (value_t)((svalue_t)Rb / (svalue_t)Rc);
    pc += 1;
  } GOTO_NEXT;

 l_MOD: {
    Ra = (value_t)((svalue_t)Rb % (svalue_t)Rc);
    pc += 1;
  } GOTO_NEXT;

 l_LSL: {
    Ra = Rb << (Rc & 0x1F);
    pc += 1;
  } GOTO_NEXT;

 l_LSR: {
    Ra = (value_t)((svalue_t)Rb >> (Rc & 0x1F));
    pc += 1;
  } GOTO_NEXT;

 l_AND: {
    Ra = Rb & Rc;
    pc += 1;
  } GOTO_NEXT;

 l_OR: {
    Ra = Rb | Rc;
    pc += 1;
  } GOTO_NEXT;

 l_XOR: {
    Ra = Rb ^ Rc;
    pc += 1;
  } GOTO_NEXT;

 l_JLT: {
    pc += ((svalue_t)Ra < (svalue_t)Rb ? instr_d(*pc) : 1);
  } GOTO_NEXT;

 l_JLE: {
    pc += ((svalue_t)Ra <= (svalue_t)Rb ? instr_d(*pc) : 1);
  } GOTO_NEXT;

 l_JEQ: {
    pc += (Ra == Rb ? instr_d(*pc) : 1);
  } GOTO_NEXT;

 l_JNE: {
    pc += (Ra != Rb ? instr_d(*pc) : 1);
  } GOTO_NEXT;

 l_JI: {
    pc += instr_extract_s(*pc, 0, 27);
  } GOTO_NEXT;

 l_CALL_NI: {
    pc = call(Ra,
              addr_p_to_v(R[Ib]),
              addr_p_to_v(R[Lb]),
              addr_p_to_v(R[Ob]),
              addr_p_to_v(pc + 1));
  } GOTO_NEXT;

 l_CALL_ND: {
    pc = call(addr_p_to_v(pc + instr_extract_s(*pc, 0, 27)),
              addr_p_to_v(R[Ib]),
              addr_p_to_v(R[Lb]),
              addr_p_to_v(R[Ob]),
              addr_p_to_v(pc + 1));
  } GOTO_NEXT;

 l_CALL_TI: {
    pc = call(Ra, R[Ib][0], R[Ib][1], R[Ib][2], R[Ib][3]);
  } GOTO_NEXT;

 l_CALL_TD: {
    pc = call(addr_p_to_v(pc + instr_extract_s(*pc, 0, 27)),
              R[Ib][0],
              R[Ib][1],
              R[Ib][2],
              R[Ib][3]);
  } GOTO_NEXT;

 l_RET: {
    pc = ret(Ra);
  } GOTO_NEXT;

 l_HALT: {
    return Ra;
  }

 l_LDLO: {
    Ra = (value_t)instr_extract_s(*pc, 8, 19);
    pc += 1;
  } GOTO_NEXT;

 l_LDHI: {
    Ra = ((value_t)instr_extract_u(*pc, 8, 16) << 16) | (Ra & 0xFFFF);
    pc += 1;
  } GOTO_NEXT;

 l_MOVE: {
    Ra = Rb;
    pc += 1;
  } GOTO_NEXT;

 l_RALO: {
    value_t l_size = instr_extract_u(*pc, 0, 8);
    if (l_size > 0)
      engine_set_Lb(memory_allocate(tag_RegisterFrame, l_size));
    value_t o_size = instr_extract_u(*pc, 8, 8);
    if (o_size > 0)
      engine_set_Ob(memory_allocate(tag_RegisterFrame, o_size));
    pc += 1;
  } GOTO_NEXT;

 l_BALO: {
    value_t* block = memory_allocate(instr_extract_u(*pc, 16, 8), Rb);
    Ra = addr_p_to_v(block);
    pc += 1;
  } GOTO_NEXT;

 l_BSIZ: {
    Ra = memory_get_block_size(addr_v_to_p(Rb));
    pc += 1;
  } GOTO_NEXT;

 l_BTAG: {
    Ra = memory_get_block_tag(addr_v_to_p(Rb));
    pc += 1;
  } GOTO_NEXT;

 l_BGET: {
    value_t* block = addr_v_to_p(Rb);
    value_t index = Rc;
    assert(index < memory_get_block_size(block));
    Ra = block[index];
    pc += 1;
  } GOTO_NEXT;

 l_BSET: {
    value_t* block = addr_v_to_p(Rb);
    value_t index = Rc;
    assert(index < memory_get_block_size(block));
    block[index] = Ra;
    pc += 1;
  } GOTO_NEXT;

 l_BREA: {
    int maybe_byte = getchar_unlocked();
    Ra = (value_t)(maybe_byte != EOF ? maybe_byte : -1);
    pc += 1;
  } GOTO_NEXT;

 l_BWRI: {
    uint8_t byte = (uint8_t)Ra;
    putchar_unlocked(byte);
    pc += 1;
  } GOTO_NEXT;
}
