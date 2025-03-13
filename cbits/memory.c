#include <inttypes.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <stdatomic.h>

#include "align.h"
#include "flags.h"

void* accelerate_raw_alloc(uint64_t size, uint64_t align);
void accelerate_raw_free(void *ptr);

struct ObjectHeader {
  _Atomic uint64_t reference_count;
  uint64_t byte_size; // Size of the array. Does not include the header, and is not necessarily a multiple of the alignment.
} CACHE_ALIGNED;

void* accelerate_buffer_alloc(uint64_t byte_size) {
  uint64_t size = byte_size + sizeof(struct ObjectHeader);
  // Align size to the next multiple of CACHE_LINE_SIZE
  // Note: it is apparently a requirement on macOS that the size is a multiple
  // of the alignment, but it is not required on Linux.
  size = (size + CACHE_LINE_SIZE - 1) / CACHE_LINE_SIZE * CACHE_LINE_SIZE;
  void *ptr = accelerate_raw_alloc(size, CACHE_LINE_SIZE);

  // TODO: call ___tracy_emit_memory_alloc

  struct ObjectHeader* header = (struct ObjectHeader*) ptr;
  header->reference_count = 1;
  header->byte_size = byte_size;

  void* interior = ptr + sizeof(struct ObjectHeader);
  return interior;
}

uint64_t accelerate_buffer_byte_size(void* interior) {
  struct ObjectHeader* header = (struct ObjectHeader*) (interior - sizeof(struct ObjectHeader));
  return header->byte_size;
}

void accelerate_buffer_retain_by(void* interior, uint64_t amount) {
  if (amount == 0) return;
  struct ObjectHeader* header = (struct ObjectHeader*) (interior - sizeof(struct ObjectHeader));
  atomic_fetch_add_explicit(&header->reference_count, amount, memory_order_acquire);
}

void accelerate_buffer_retain(void* interior) {
  accelerate_buffer_retain_by(interior, 1);
}

void accelerate_buffer_release_by(void* interior, uint64_t amount) {
  if (amount == 0) return;
  struct ObjectHeader* header = (struct ObjectHeader*) (interior - sizeof(struct ObjectHeader));
  // Release is always needed, acquire only when the reference count drops to zero.
  uint64_t old = atomic_fetch_add_explicit(&header->reference_count, -amount, memory_order_acq_rel);
  if (old == amount) {
    // TODO: call ___tracy_emit_memory_free
    accelerate_raw_free(header);
  }
  if (old < amount) {
    printf("Reference count underflow\n");
  }
}

void accelerate_buffer_release(void* interior) {
  accelerate_buffer_release_by(interior, 1);
}
