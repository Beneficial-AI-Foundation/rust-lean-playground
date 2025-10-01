import Aeneas
import Verify.Src.RustLeanPlayground
import Mathlib
import Verify.Proofs.Aux
import Verify.Proofs.Defs

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

/-! # ToBytes

The main statement concerning `to_bytes` is `to_bytes_spec` (below).
-/

open Aeneas.Std Result
open rust_lean_playground

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `to_bytes` -/

/- Using the specs with bit-vectors -/
attribute [-progress] U64.add_spec U64.mul_spec U8.add_spec U8.mul_spec
attribute [local progress] U64.add_bv_spec U64.mul_bv_spec U8.add_bv_spec U8.mul_bv_spec

/-- **Spec for `to_bytes`**:
- Does not overflow and hence returns a result
- The result byte array represents the same natural number as the input limbs -/
theorem to_bytes_spec (limbs : Array U64 5#usize) :
    ∃ result, to_bytes limbs = ok (result) ∧
    ArrayU832_to_Nat result = ArrayU645_to_Nat limbs := by
  unfold to_bytes
  progress*
  -- remains to show that `ArrayU832_to_Nat result = ArrayU645_to_Nat limbs`
  simp [Finset.sum_range_succ, Nat.ModEq, *]

  sorry
