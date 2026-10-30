/*
 * Module      : Data.Array.Accelerate.FFI.Memory
 * Copyright   : [2008..2020] The Accelerate Team
 * License     : BSD3
 *
 * Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
 * Stability   : experimental
 * Portability : non-portable (GHC extensions)
 */

#ifndef __ACCELERATE_ALLOC_H__
#define __ACCELERATE_ALLOC_H__

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

void* accelerate_raw_alloc(uint64_t size, uint64_t align);
void accelerate_raw_free(void *ptr);

#ifdef __cplusplus
}
#endif

#endif // __ACCELERATE_ALLOC_H__
