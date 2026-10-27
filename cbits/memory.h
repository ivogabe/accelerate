/*
 * Module      : Data.Array.Accelerate.FFI.Memory
 * Copyright   : [2008..2020] The Accelerate Team
 * License     : BSD3
 *
 * Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
 * Stability   : experimental
 * Portability : non-portable (GHC extensions)
 */

#ifndef __ACCELERATE_MEMORY_H__
#define __ACCELERATE_MEMORY_H__

#include <stdint.h>

#ifdef ACCELERATE_MEMORY_COUNTER
void accelerate_memory_counter_reset(void);
uint64_t accelerate_memory_counter_total(void);
uint64_t accelerate_memory_counter_init(void);
uint64_t accelerate_memory_counter_max(void);
#endif  // ACCELERATE_MEMORY_COUNTER

void* accelerate_buffer_alloc(uint64_t byte_size);
uint64_t accelerate_buffer_byte_size(void *interior);
void accelerate_buffer_retain(void *interior);
void accelerate_buffer_release(void *interior);

#endif // __ACCELERATE_MEMORY_H__
