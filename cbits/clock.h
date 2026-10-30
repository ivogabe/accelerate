/*
 * Module      : Data.Array.Accelerate.FFI.Clock
 * Copyright   : [2016..2020] The Accelerate Team
 * License     : BSD3
 *
 * Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
 * Stability   : experimental
 * Portability : non-portable (GHC extensions)
 */

#ifndef __ACCELERATE_CLOCK_H__
#define __ACCELERATE_CLOCK_H__

double clock_gettime_monotonic_seconds(void);
double clock_gettime_elapsed_seconds(void);

#endif // __ACCELERATE_CLOCK_H__
