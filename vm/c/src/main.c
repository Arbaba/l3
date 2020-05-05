#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdalign.h>
#include <assert.h>

#include "memory.h"
#include "engine.h"
#include "fail.h"

typedef struct {
  size_t memory_size;
  char* file_name;
} options_t;

static options_t default_options = { 1000000, NULL };

// Argument parsing

static void display_usage(char* prog_name) {
  printf("Usage: %s [<options>] <asm_file>\n", prog_name);
  printf("\noptions:\n");
  printf("  -h         display this help message and exit\n");
  printf("  -m <size>  set memory size in bytes (default %zd)\n",
         default_options.memory_size);
  printf("  -v         display version and exit\n");
}

static void parse_args(int argc, char* argv[], options_t* opts) {
  int i = 1;
  while (i < argc) {
    char* arg = argv[i++];
    const size_t arg_len = strlen(arg);

    if (arg_len == 2 && arg[0] == '-') {
      switch (arg[1]) {
      case 'm': {
        if (i >= argc) {
          display_usage(argv[0]);
          fail("missing argument to -m");
        }
        opts->memory_size = strtoul(argv[i++], NULL, 10);
      } break;

      case 'h': {
        display_usage(argv[0]);
        exit(0);
      }

      case 'v': {
        printf("vm v1.0\n");
        printf("  memory module: %s\n", memory_get_identity());
        exit(0);
      }

      default:
        display_usage(argv[0]);
        fail("invalid option %s", arg);
      }
    } else
      opts->file_name = arg;
  }
}

// Memory/size alignment

static size_t align_down(size_t value, size_t align) {
  assert(align > 0 && (align & (align - 1)) == 0); /* check power of 2 */
  return value & ~(align - 1);
}

static void* align_up(void* address, size_t align) {
  assert(align > 0 && (align & (align - 1)) == 0); /* check power of 2 */
  uintptr_t int_address = (uintptr_t)address;
  uintptr_t aligned_address = (int_address + align - 1) & ~(align - 1);
  return (void*)aligned_address;
}

// ASM file loading

static void load_file(char* file_name, instr_t** instr_ptr) {
  FILE* file = fopen(file_name, "r");
  if (file == NULL)
    fail("cannot open file %s", file_name);

  char line[1000];
  while (fgets(line, sizeof(line), file) != NULL) {
    instr_t instr;
    int read_count = sscanf(line, "%8x", &instr);
    if (read_count != 1)
      fail("error while reading file %s", file_name);

    engine_emit(instr, instr_ptr);
  }

  fclose(file);
}

int main(int argc, char* argv[]) {
  options_t options = default_options;
  parse_args(argc, argv, &options);
  if (options.file_name == NULL) {
    display_usage(argv[0]);
    fail("missing input file name");
  }
  if (options.memory_size == 0)
    fail("invalid memory size %zd", options.memory_size);

  const int value_align = alignof(value_t);

  memory_setup(align_down(options.memory_size, value_align));
  engine_setup();

  instr_t* instr_ptr = memory_get_start();
  load_file(options.file_name, &instr_ptr);
  memory_set_heap_start(align_up(instr_ptr, value_align));

  value_t* const_regs = memory_allocate(tag_RegisterFrame, 32);
  for (value_t i = 0; i < 32; i += 1)
    const_regs[i] = i;
  engine_set_Cb(const_regs);

  value_t halt_code = engine_run();

  engine_cleanup();
  memory_cleanup();

  return (int)halt_code;
}
