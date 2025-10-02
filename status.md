# Verification Status

This document tracks the verification status of functions in [src/lib.rs](src/lib.rs).

## Legend

- ✅ **Verified**: Complete spec theorem with proof
- 📝 **Has spec**: Spec theorem statement exists but proof is incomplete
- ❌ **No spec**: No verification work started

## Function Status

| Function          | Status      | Spec File                                                       | Notes                                                                |
| ----------------- | ----------- | --------------------------------------------------------------- | -------------------------------------------------------------------- |
| `reduce`          | ✅ Verified | [Reduce.lean](verify/Verify/Proofs/Reduce.lean)                 | Reduction maintains value mod p and bounds limbs                     |
| `clamp_integer`   | 📝 Has spec | [ClampInteger.lean](verify/Verify/Proofs/ClampInteger.lean)     | Proven divisibility by h and one bound, remains to prove other bound |
| `to_bytes`        | 📝 Has spec | [ToBytes.lean](verify/Verify/Proofs/ToBytes.lean)               | One equality remains to be proven                                    |
| `m`               | ✅ Verified | [M.lean](verify/Verify/Proofs/M.lean)                           | Trivial proof, corresponds to multiplication                         |
| `mul_internal`    | ✅ Verified | [MulInternal.lean](verify/Verify/Proofs/MulInternal.lean)       | Result equals product                                                |
| `square_internal` | ✅ Verified | [SquareInternal.lean](verify/Verify/Proofs/SquareInternal.lean) | Result equals square                                                 |
| `ZERO`            | ✅ Verified | [Zero.lean](verify/Verify/Proofs/Zero.lean)                     | Trivial proof, ZERO represents 0                                     |

## Summary

- **Verified**: 5/7 (reduce, m, mul_internal, square_internal, ZERO)
- **Spec only**: 2/7 (clamp_integer, to_bytes)
- **No spec**: 0/7

## Next Steps

1. Check the spec and complete the final equality proof in [to_bytes_spec](verify/Verify/Proofs/ToBytes.lean:39)
2. Prove the upper bound in [clamp_integer_spec](verify/Verify/Proofs/ClampInteger.lean:68)
