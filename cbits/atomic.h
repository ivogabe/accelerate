/*
 * Module      : Data.Array.Accelerate.FFI.Atomic
 * Copyright   : [2016..2020] The Accelerate Team
 * License     : BSD3
 *
 * Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
 * Stability   : experimental
 * Portability : non-portable (GHC extensions)
 */

#ifndef __ACCELERATE_ATOMIC_H__
#define __ACCELERATE_ATOMIC_H__

#include <stdint.h>

int64_t atomic_fetch_and_add_64(volatile int64_t* ptr, int64_t val);

int64_t atomic_fetch_and_sub_64(volatile int64_t* ptr, int64_t val);

int64_t atomic_fetch_and_and_64(volatile int64_t* ptr, int64_t val);

int64_t atomic_read_64(volatile int64_t* ptr);

void atomic_write_64(volatile int64_t* ptr, int64_t val);

#endif // __ACCELERATE_ATOMIC_H__
