# Verification Status

This document tracks the verification status of functions in [src/lib.rs](src/lib.rs).

## Legend

- ✅ **Verified**: Complete spec theorem with proof
- 📝 **Has spec**: Spec theorem statement exists but proof is incomplete
- 📄 **No spec**: No verification work started

## Function Status

| Function          | Status      | Source Code                   | Spec File                                                       | Notes                                                  |
| ----------------- | ----------- | ----------------------------- | --------------------------------------------------------------- | ------------------------------------------------------ |
| `clamp_integer`   | 📝 Has spec | [lib.rs:88](src/lib.rs#L88)   | [ClampInteger.lean](verify/Verify/Proofs/ClampInteger.lean)     | Proven divisibility, remains to prove additional bound |
| `from_bytes`      | 📄 No spec  | [lib.rs:237](src/lib.rs#L237) | -                                                               | Load field element from 32-byte little-endian encoding |
| `is_negative`     | 📝 Has spec | [lib.rs:197](src/lib.rs#L197) | [IsNegative.lean](verify/Verify/Proofs/IsNegative.lean)         | Checks if field element is negative (low bit set)      |
| `load8_at`        | 📄 No spec  | [lib.rs:238](src/lib.rs#L238) | -                                                               | Helper: load 8 bytes as u64 (little-endian)            |
| `LOW_51_BIT_MASK` | ✅ Verified | [lib.rs:4](src/lib.rs#L4)     | [Low51BitMask.lean](verify/Verify/Proofs/Low51BitMask.lean)     | Constant: 2^51 - 1                                     |
| `m`               | ✅ Verified | [lib.rs:142](src/lib.rs#L142) | [M.lean](verify/Verify/Proofs/M.lean)                           | Trivial proof, corresponds to multiplication           |
| `mul_internal`    | ✅ Verified | [lib.rs:149](src/lib.rs#L149) | [MulInternal.lean](verify/Verify/Proofs/MulInternal.lean)       | Result equals product                                  |
| `reduce`          | ✅ Verified | [lib.rs:35](src/lib.rs#L35)   | [Reduce.lean](verify/Verify/Proofs/Reduce.lean)                 | Reduction maintains value mod p and bounds limbs       |
| `square_internal` | ✅ Verified | [lib.rs:168](src/lib.rs#L168) | [SquareInternal.lean](verify/Verify/Proofs/SquareInternal.lean) | Result equals square                                   |
| `to_bytes`        | 📝 Has spec | [lib.rs:101](src/lib.rs#L101) | [ToBytes.lean](verify/Verify/Proofs/ToBytes.lean)               | One equality remains to be proven                      |
| `ZERO`            | ✅ Verified | [lib.rs:96](src/lib.rs#L96)   | [Zero.lean](verify/Verify/Proofs/Zero.lean)                     | Trivial proof, ZERO represents 0                       |

## Summary

- **Verified**: 6/11 (reduce, m, mul_internal, square_internal, ZERO, LOW_51_BIT_MASK)
- **Spec only**: 3/11 (clamp_integer, to_bytes, is_negative)
- **No spec**: 2/11 (from_bytes, load8_at)

## Next Steps

1. Check the spec and complete the final equality proof in [to_bytes_spec](verify/Verify/Proofs/ToBytes.lean:39)
2. Prove the upper bound in [clamp_integer_spec](verify/Verify/Proofs/ClampInteger.lean:68)
3. Complete the proof for [is_negative_spec](verify/Verify/Proofs/IsNegative.lean:26)
4. Create spec and proof for [from_bytes](src/lib.rs#L237)
