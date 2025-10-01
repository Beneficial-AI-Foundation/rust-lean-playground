import Aeneas
import Verify.Src.RustLeanPlayground
import Mathlib
import Verify.Proofs.Aux
import Verify.Proofs.Defs
import Verify.Proofs.M

set_option linter.style.longLine false
set_option maxHeartbeats 2000000

/-! # MulInternal

The main statement concerning `mul_internal` is `mul_internal_spec` (below).
-/

open Aeneas.Std Result
open rust_lean_playground

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Auxiliary definitions -/

/-- Auxiliary definition to interpret a 9-element u128 array as a natural number.
This represents the result of polynomial multiplication where each limb is at position 51*i bits. -/
@[simp]
def ArrayU1289_to_Nat (limbs : Array U128 9#usize) : Nat :=
  ∑ i ∈ Finset.range 9, 2^(51 * i) * (limbs[i]!).val

/-! ## Spec for `mul_internal` -/

/- Using the specs with bit-vectors -/
attribute [-progress] U64.add_spec U64.mul_spec U128.add_spec U128.mul_spec
attribute [local progress] U64.add_bv_spec U64.mul_bv_spec U128.add_bv_spec U128.mul_bv_spec

/-- **Spec for `mul_internal`**:
- Does not overflow and hence returns a result
- The result represents the product of the two input field elements modulo 2^255 - 19 -/
theorem mul_internal_spec (a b : Array U64 5#usize) :
    ∃ result, mul_internal a b = ok (result) ∧
    ArrayU1289_to_Nat result = ArrayU645_to_Nat a * ArrayU645_to_Nat b := by
  unfold mul_internal
  progress*
  -- remains to show that the result equals the product
  sorry
