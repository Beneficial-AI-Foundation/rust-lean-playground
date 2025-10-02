# Verification Status

This document tracks the verification status of functions in [src/lib.rs](src/lib.rs).

## Legend

- ✅ **Verified**: Complete spec theorem with proof
- 📝 **Has spec**: Spec theorem statement exists but proof is incomplete
- ❌ **No spec**: No verification work started

## Function Status

| Function | Status | Spec File | Notes |
|----------|--------|-----------|-------|
| `reduce` | ✅ Verified | [Reduce.lean](verify/Verify/Proofs/Reduce.lean) | Complete proof that reduction maintains value mod p and bounds limbs |
| `clamp_integer` | 📝 Has spec | [clamp_integer.lean](verify/Verify/Proofs/clamp_integer.lean) | Spec shows divisibility by h=8 and bounds, but contains 2 sorries |
| `to_bytes` | 📝 Has spec | [ToBytes.lean](verify/Verify/Proofs/ToBytes.lean) | Spec shows byte array equals limbs as nat, final equality has sorry |
| `m` | ✅ Verified | [M.lean](verify/Verify/Proofs/M.lean) | Complete proof that u64*u64=u128 multiply works correctly |
| `mul_internal` | 📝 Has spec | [MulInternal.lean](verify/Verify/Proofs/MulInternal.lean) | Spec shows result equals product, final equality has sorry |
| `square_internal` | ✅ Verified | [SquareInternal.lean](verify/Verify/Proofs/SquareInternal.lean) | Complete proof that result equals square using `ring` tactic |
| `ZERO` | ✅ Verified | [Zero.lean](verify/Verify/Proofs/Zero.lean) | Trivial proof that ZERO represents 0 |

## Summary

- **Verified**: 4/7 (reduce, m, square_internal, ZERO)
- **Spec only**: 3/7 (clamp_integer, to_bytes, mul_internal)
- **No spec**: 0/7

## Next Steps

1. Complete the final `ring` proof in [mul_internal_spec](verify/Verify/Proofs/MulInternal.lean:131)
2. Complete the final equality proof in [to_bytes_spec](verify/Verify/Proofs/ToBytes.lean:39)
3. Fill in the 2 sorries in [clamp_integer_spec](verify/Verify/Proofs/clamp_integer.lean:70-73)
