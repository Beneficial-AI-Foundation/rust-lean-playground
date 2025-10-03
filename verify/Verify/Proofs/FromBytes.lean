import Aeneas
import Verify.Src.RustLeanPlayground
import Mathlib
import Verify.Proofs.Aux
import Verify.Proofs.Defs

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

/-! # FromBytes

The main statements concerning `from_bytes` and `from_bytes.load8_at` are below.
-/

open Aeneas.Std Result
open rust_lean_playground

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `load8_at` -/

/-- **Spec for `load8_at`**:
- Does not error when i + 7 < input.length
- Returns the 8 bytes starting at position i as a u64 in little-endian order
- The result equals: input[i] + input[i+1]*2^8 + ... + input[i+7]*2^56 -/
theorem load8_at_spec (input : Slice U8) (i : Usize)
    (h : i.val + 7 < input.length) :
    ∃ result, from_bytes.load8_at input i = ok (result) ∧
    result.val = ∑ j ∈ Finset.range 8, 2^(8 * j) * (input.val[i.val + j]!).val := by
  unfold from_bytes.load8_at
  have h' : i.val + 7 < (input : List U8).length := by omega
  progress*
  simp [*]
  simp [U64.size, U64.numBits]
  simp [Finset.range_succ]
  have h' (k : Nat) (hk : k ≤ 7) : i.val + k < (input : List U8).length := by omega
  have h'' : i.val < (input : List U8).length := by omega
  simp [h', h'']

  have := Nat.shiftLeft_eq
  repeat rw [Nat.shiftLeft_eq]
  bvify 64 at *










  sorry

/-! ## Spec for `from_bytes` -/

/-- **Spec for `from_bytes`**:
- Does not overflow and hence returns a result
- The result limbs represent the same natural number as the input bytes
- Each output limb is bounded by 2^51 - 1 -/
theorem from_bytes_spec (bytes : Array U8 32#usize) :
    ∃ result, from_bytes bytes = ok (result) ∧
    U64x5_as_Nat result = U8x32_as_Nat bytes ∧
    (∀ i, i < 5 → (result[i]!).val ≤ 2^51 - 1) := by
  unfold from_bytes
  sorry
