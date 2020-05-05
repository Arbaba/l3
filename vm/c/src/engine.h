#ifndef ENGINE__H
#define ENGINE__H

#include "vmtypes.h"

/* Setup the interpreter */
void engine_setup(void);

/* Tear down the interpreter */
void engine_cleanup(void);

/* Add an instruction to the code area of the memory */
void engine_emit(instr_t instr, instr_t** instr_ptr);

/* Return the heap address of the register bank */
value_t* engine_get_Cb(void);
value_t* engine_get_Ib(void);
value_t* engine_get_Lb(void);
value_t* engine_get_Ob(void);

/* Set the heap address of the register bank */
void engine_set_Cb(value_t* new_value);
void engine_set_Ib(value_t* new_value);
void engine_set_Lb(value_t* new_value);
void engine_set_Ob(value_t* new_value);

/* Interpret the program in the code area of the memory */
value_t engine_run(void);

#endif // ENGINE__H
