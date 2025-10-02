# Verification Status

This document tracks the verification status of functions in [src/lib.rs](src/lib.rs).

## Legend

- ✅ **Verified**: Complete spec theorem with proof
- 📝 **Has spec**: Spec theorem statement exists but proof is incomplete
- ❌ **No spec**: No verification work started

## Function Status

| Function          | Status      | Spec File                                                       | Notes                                                                   |
| ----------------- | ----------- | --------------------------------------------------------------- | ----------------------------------------------------------------------- |
| `reduce`          | ✅ Verified | [Reduce.lean](verify/Verify/Proofs/Reduce.lean)                 | Complete proof that reduction maintains value mod p and bounds limbs    |
| `clamp_integer`   | 📝 Has spec | [ClampInteger.lean](verify/Verify/Proofs/ClampInteger.lean)     | Spec shows divisibility by h=8 and bounds, remains to prove upper bound |
| `to_bytes`        | 📝 Has spec | [ToBytes.lean](verify/Verify/Proofs/ToBytes.lean)               | Spec shows byte array equals limbs as nat, one equality remains         |
| `m`               | ✅ Verified | [M.lean](verify/Verify/Proofs/M.lean)                           | Complete proof that u64\*u64=u128 multiply works correctly              |
| `mul_internal`    | ✅ Verified | [MulInternal.lean](verify/Verify/Proofs/MulInternal.lean)       | Complete proof that result equals product                               |
| `square_internal` | ✅ Verified | [SquareInternal.lean](verify/Verify/Proofs/SquareInternal.lean) | Complete proof that result equals square using `ring` tactic            |
| `ZERO`            | ✅ Verified | [Zero.lean](verify/Verify/Proofs/Zero.lean)                     | Trivial proof that ZERO represents 0                                    |

## Summary

- **Verified**: 5/7 (reduce, m, mul_internal, square_internal, ZERO)
- **Spec only**: 2/7 (clamp_integer, to_bytes)
- **No spec**: 0/7

## Next Steps

1. Complete the final equality proof in [to_bytes_spec](verify/Verify/Proofs/ToBytes.lean:39)
2. Prove the upper bound in [clamp_integer_spec](verify/Verify/Proofs/ClampInteger.lean:68)
