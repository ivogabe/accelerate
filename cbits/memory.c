#include <inttypes.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <stdatomic.h>
#ifdef ACCELERATE_MEMORY_COUNTER
#include <pthread.h>
#endif  // ACCELERATE_MEMORY_COUNTER
#ifdef ACCELERATE_TRACY
#include "tracy/public/tracy/TracyC.h"
#endif  // ACCELERATE_TRACY

#include "align.h"
#include "alloc.h"
#include "flags.h"

#include "memory.h"

struct ObjectHeader {
  _Atomic uint64_t reference_count;
  uint64_t byte_size; // Size of the array. Does not include the header, and is not necessarily a multiple of the alignment.
} CACHE_ALIGNED;

#ifdef ACCELERATE_MEMORY_COUNTER

// For memory counting:
pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
uint64_t total_allocated = 0;
uint64_t current_allocated = 0;
uint64_t init_allocated = 0;
uint64_t max_allocated = 0;

void accelerate_memory_counter_reset() {
  pthread_mutex_lock(&mutex);
  total_allocated = 0;
  init_allocated = current_allocated;
  max_allocated = current_allocated;
  pthread_mutex_unlock(&mutex);
}

uint64_t accelerate_memory_counter_total() {
  pthread_mutex_lock(&mutex);
  uint64_t ret = total_allocated;
  pthread_mutex_unlock(&mutex);
  return ret;
}

uint64_t accelerate_memory_counter_init() {
  pthread_mutex_lock(&mutex);
  uint64_t ret = init_allocated;
  pthread_mutex_unlock(&mutex);
  return ret;
}

uint64_t accelerate_memory_counter_max() {
  pthread_mutex_lock(&mutex);
  uint64_t ret = max_allocated;
  pthread_mutex_unlock(&mutex);
  return ret;
}

#endif  // ACCELERATE_MEMORY_COUNTER


void* accelerate_buffer_alloc(uint64_t byte_size) {
  uint64_t size = byte_size + sizeof(struct ObjectHeader);
  // Align size to the next multiple of CACHE_LINE_SIZE
  // Note: it is apparently a requirement on macOS that the size is a multiple
  // of the alignment, but it is not required on Linux.
  size = (size + CACHE_LINE_SIZE - 1) / CACHE_LINE_SIZE * CACHE_LINE_SIZE;
  void *ptr = accelerate_raw_alloc(size, CACHE_LINE_SIZE);

  #ifdef ACCELERATE_TRACY
  ___tracy_emit_memory_alloc(ptr, size, 0);
  #endif  // ACCELERATE_TRACY

  #ifdef ACCELERATE_MEMORY_COUNTER
  // For benchmarking memory usage:
  pthread_mutex_lock(&mutex);
  total_allocated += byte_size;
  current_allocated += byte_size;
  if (current_allocated > max_allocated)
    max_allocated = current_allocated;
  pthread_mutex_unlock(&mutex);
  #endif  // ACCELERATE_MEMORY_COUNTER

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

    #ifdef ACCELERATE_TRACY
    ___tracy_emit_memory_free(header, 0);
    #endif  // ACCELERATE_TRACY

    #ifdef ACCELERATE_MEMORY_COUNTER
    pthread_mutex_lock(&mutex);
    current_allocated -= header->byte_size;
    pthread_mutex_unlock(&mutex);
    #endif  // ACCELERATE_MEMORY_COUNTER

    accelerate_raw_free(header);
  }
  if (old < amount) {
    printf("Reference count underflow\n");
  }
}

void accelerate_buffer_release(void* interior) {
  accelerate_buffer_release_by(interior, 1);
}
