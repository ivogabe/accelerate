#include "./parlaylib/include/parlay/alloc.h"

extern "C" {
  void* accelerate_raw_alloc(uint64_t size, uint64_t align) {
    return parlay::p_malloc(size, align);
  }
  void accelerate_raw_free(void *ptr) {
    parlay::p_free(ptr);
  }
}
