//===-- asan_poisoning.h ----------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file is a part of AddressSanitizer, an address sanity checker.
//
// Shadow memory poisoning by ASan RTL and by user application.
//===----------------------------------------------------------------------===//

#include "asan_interceptors.h"
#include "asan_internal.h"
#include "asan_mapping.h"
#include "sanitizer_common/sanitizer_flags.h"
#include "sanitizer_common/sanitizer_platform.h"

namespace __asan {

// Enable/disable memory poisoning.
void SetCanPoisonMemory(bool value);
bool CanPoisonMemory();

// Poisons the shadow memory for "size" bytes starting from "addr".
void PoisonShadow(uptr addr, uptr size, u8 value);

// Poisons the shadow memory for "redzone_size" bytes starting from
// "addr + size".
void PoisonShadowPartialRightRedzone(uptr addr,
                                     uptr size,
                                     uptr redzone_size,
                                     u8 value);

// Fast versions of PoisonShadow and PoisonShadowPartialRightRedzone that
// assume that memory addresses are properly aligned. Use in
// performance-critical code with care.
ALWAYS_INLINE void FastPoisonShadow(uptr aligned_beg, uptr aligned_size,
                                    u8 value) {
  
  DCHECK(!value || CanPoisonMemory());
#if SANITIZER_FUCHSIA
  __sanitizer_fill_shadow(aligned_beg, aligned_size, value,
                          common_flags()->clear_shadow_mmap_threshold);
#else
  uptr shadow_beg = MEM_TO_SHADOW(aligned_beg);

  // Printf("FastPoisonShadow: aligned_beg: %p (shadow %p) with size %llu, %02X\n", aligned_beg, shadow_beg, aligned_size, value);

  uptr shadow_end =
      MEM_TO_SHADOW(aligned_beg + aligned_size - ASAN_SHADOW_GRANULARITY) + 1;

  /* Fast Shadow Poison for ASan */
  if (value) {
    if (value <= 7) value = 72 - value; // @acesrc: converting the ASan partial value into sparse table value.
    REAL(memset)((void*)shadow_beg, value, shadow_end - shadow_beg);
  }
  else {
    // @acesrc: Fill the sparse table [shadow_beg, shadow_end)
    unsigned char *p = (unsigned char *)shadow_end;
    uptr N = shadow_end - shadow_beg;
    switch (N) {
      default:
      case 7:
        *(p - 7) = 62; *(p - 6) = 62; *(p - 5) = 62; *(p - 4) = 62; *(p - 3) = 63; *(p - 2) = 63; *(p - 1) = 64; break;
      case 6:
        *(p - 6) = 62; *(p - 5) = 62; *(p - 4) = 62; *(p - 3) = 63; *(p - 2) = 63; *(p - 1) = 64; break;
      case 5:
        *(p - 5) = 62; *(p - 4) = 62; *(p - 3) = 63; *(p - 2) = 63; *(p - 1) = 64; break;
      case 4:
        *(p - 4) = 62; *(p - 3) = 63; *(p - 2) = 63; *(p - 1) = 64; break;
      case 3:
        *(p - 3) = 63; *(p - 2) = 63; *(p - 1) = 64; break;
      case 2:
        *(p - 2) = 63; *(p - 1) = 64; break;
      case 1:
        *(p - 1) = 64; break;
      case 0:
        break;
    }
    if (N >= 8) {
      for (uptr i = 3; ; ++i) {
        uptr bBegin = shadow_end - (1 << (i + 1)) + 1;
        if (bBegin <= shadow_beg) {
          uptr bEnd = shadow_end - (1 << i) + 1;
          REAL(memset)((void *)shadow_beg, 64 - i, bEnd - shadow_beg);
          break;
        }
        else {
          REAL(memset)((void *)bBegin, 64 - i, (1 << i));
        }
      }
    }
  }


  /*
  // FIXME: Page states are different on Windows, so using the same interface
  // for mapping shadow and zeroing out pages doesn't "just work", so we should
  // probably provide higher-level interface for these operations.
  // For now, just memset on Windows.
  if (value || SANITIZER_WINDOWS == 1 ||
      shadow_end - shadow_beg < common_flags()->clear_shadow_mmap_threshold) {
    REAL(memset)((void*)shadow_beg, value, shadow_end - shadow_beg);
  } else {
    uptr page_size = GetPageSizeCached();
    uptr page_beg = RoundUpTo(shadow_beg, page_size);
    uptr page_end = RoundDownTo(shadow_end, page_size);

    if (page_beg >= page_end) {
      REAL(memset)((void *)shadow_beg, 0, shadow_end - shadow_beg);
    } else {
      if (page_beg != shadow_beg) {
        REAL(memset)((void *)shadow_beg, 0, page_beg - shadow_beg);
      }
      if (page_end != shadow_end) {
        REAL(memset)((void *)page_end, 0, shadow_end - page_end);
      }
      ReserveShadowMemoryRange(page_beg, page_end - 1, nullptr);
    }
  }
  */
#endif // SANITIZER_FUCHSIA
}

ALWAYS_INLINE void FastPoisonShadowPartialRightRedzone(
    uptr aligned_addr, uptr size, uptr redzone_size, u8 value) {

  DCHECK(CanPoisonMemory());
  bool poison_partial = flags()->poison_partial;
  u8 *shadow = (u8*)MEM_TO_SHADOW(aligned_addr);

  // Printf("Poisoning %p (shadow %p) with size %llu, redzone_size %llu, %02X\n", aligned_addr, shadow, size, redzone_size, value);

  for (uptr i = 0; i < redzone_size; i += ASAN_SHADOW_GRANULARITY, shadow++) {
    if (i + ASAN_SHADOW_GRANULARITY <= size) {
      *shadow = 0;  // fully addressable
    } else if (i >= size) {
      *shadow =
          (ASAN_SHADOW_GRANULARITY == 128) ? 0xff : value;  // unaddressable
    } else {
      // first size-i bytes are addressable
      // *shadow = poison_partial ? static_cast<u8>(size - i) : 0; // @acesrc: change asan poisoning
      *shadow = poison_partial ? ASAN_SHADOW_GRANULARITY - (size & (ASAN_SHADOW_GRANULARITY - 1)): 0;
    }
  }
}

// Calls __sanitizer::ReleaseMemoryPagesToOS() on
// [MemToShadow(p), MemToShadow(p+size)].
void FlushUnneededASanShadowMemory(uptr p, uptr size);

}  // namespace __asan
