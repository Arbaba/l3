#ifndef OPCODE_H
#define OPCODE_H

typedef enum {
  opcode_ADD, opcode_SUB, opcode_MUL, opcode_DIV, opcode_MOD,
  opcode_LSL, opcode_LSR, opcode_AND, opcode_OR, opcode_XOR,
  opcode_JLT, opcode_JLE, opcode_JEQ, opcode_JNE, opcode_JI,
  opcode_CALL_NI, opcode_CALL_ND, opcode_CALL_TI, opcode_CALL_TD, opcode_RET,
  opcode_HALT, opcode_LDLO, opcode_LDHI, opcode_MOVE,
  opcode_RALO, opcode_BALO, opcode_BSIZ, opcode_BTAG, opcode_BGET, opcode_BSET,
  opcode_BREA, opcode_BWRI,
} opcode_t;

#endif // OPCODE_H
