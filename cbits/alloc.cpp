#include <stdint.h>

#ifdef _WIN32
#include <cstdlib>
#else
#include "parlaylib/include/parlay/alloc.h"
#endif

#include "alloc.h"

// Windows uses `_aligned_malloc` and `_aligned_free` from MinGW rather than ParlayLib.
// ParlayLib should compile with MinGW, see: https://github.com/cmuparlay/parlaylib
// But we have not gotten it to work.
// TODO: Maybe try getting Parlaylib to work on windows.

extern "C" {

  void* accelerate_raw_alloc(uint64_t size, uint64_t align) {
#ifdef _WIN32
    return _aligned_malloc(size, align);
#else
    return parlay::p_malloc(size, align);
#endif
  }

  void accelerate_raw_free(void *ptr) {
#ifdef _WIN32
    _aligned_free(ptr);
#else
    parlay::p_free(ptr);
#endif
  }

}
