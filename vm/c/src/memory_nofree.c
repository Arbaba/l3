#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>

#include "memory.h"
#include "fail.h"

static value_t* memory_start = NULL;
static value_t* memory_end = NULL;
static value_t* free_boundary = NULL;

#define HEADER_SIZE 1

// Header management

static value_t header_pack(tag_t tag, value_t size) {
  return (size << 8) | (value_t)tag;
}

static tag_t header_unpack_tag(value_t header) {
  return (tag_t)(header & 0xFF);
}

static value_t header_unpack_size(value_t header) {
  return header >> 8;
}

char* memory_get_identity() {
  return "no GC (memory is never freed)";
}

void memory_setup(size_t total_byte_size) {
  memory_start = calloc(total_byte_size, 1);
  if (memory_start == NULL)
    fail("cannot allocate %zd bytes of memory", total_byte_size);
  memory_end = memory_start + (total_byte_size / sizeof(value_t));
}

void memory_cleanup() {
  assert(memory_start != NULL);
  free(memory_start);
  memory_start = memory_end = free_boundary = NULL;
}

void* memory_get_start() {
  return memory_start;
}

void* memory_get_end() {
  return memory_end;
}

void memory_set_heap_start(void* heap_start) {
  assert(free_boundary == NULL);
  free_boundary = heap_start;
}

value_t* memory_allocate(tag_t tag, value_t size) {
  assert(free_boundary != NULL);

  const value_t total_size = size + HEADER_SIZE;
  if (free_boundary + total_size > memory_end)
    fail("no memory left (block of size %u requested)", size);

  *free_boundary = header_pack(tag, size);
  value_t* res = free_boundary + HEADER_SIZE;
  free_boundary += total_size;

  return res;
}

value_t memory_get_block_size(value_t* block) {
  return header_unpack_size(block[-1]);
}

tag_t memory_get_block_tag(value_t* block) {
  return header_unpack_tag(block[-1]);
}
