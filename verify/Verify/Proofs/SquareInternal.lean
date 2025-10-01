import Aeneas
import Verify.Src.RustLeanPlayground
import Mathlib
import Verify.Proofs.Aux
import Verify.Proofs.Defs
import Verify.Proofs.M

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

/-! # SquareInternal

The main statement concerning `square_internal` is `square_internal_spec` (below).
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

/-! ## Spec for `square_internal` -/

/- Using the specs with bit-vectors -/
-- attribute [-progress] U64.add_spec U64.mul_spec U128.add_spec U128.mul_spec
-- attribute [local progress] U64.add_bv_spec U64.mul_bv_spec U128.add_bv_spec U128.mul_bv_spec
attribute [progress] m_spec

/-- **Spec for `square_internal`**:
- Does not error and hence returns a result
- The result represents the square of the input field element
- Requires that each input limb is at most 63 bits to prevent overflow in the doubling step -/
theorem square_internal_spec (a : Array U64 5#usize)
    (ha : ∀ i, i < 5 → (a[i]!).val < 2^62) :
    ∃ result, square_internal a = ok (result) ∧
    ArrayU1289_to_Nat result = ArrayU645_to_Nat a * ArrayU645_to_Nat a := by
  unfold square_internal
  progress*
  · simp [*];
    have := ha 0 (by simp); have := ha 1 (by simp); have := ha 2 (by simp); have := ha 3 (by simp); have := ha 4 (by simp)
    simp at *; scalar_tac_preprocess; omega
  · simp [*];
    have := ha 0 (by simp); have := ha 1 (by simp); have := ha 2 (by simp); have := ha 3 (by simp); have := ha 4 (by simp)
    simp at *; scalar_tac_preprocess; omega
  · simp [*];
    have := ha 0 (by simp); have := ha 1 (by simp); have := ha 2 (by simp); have := ha 3 (by simp); have := ha 4 (by simp)
    simp at *; scalar_tac_preprocess; omega
  · simp [*];
    have := ha 0 (by simp); have := ha 1 (by simp); have := ha 2 (by simp); have := ha 3 (by simp); have := ha 4 (by simp)
    simp at *; scalar_tac_preprocess; omega
  · simp [*];
    have := ha 0 (by simp); have := ha 1 (by simp); have := ha 2 (by simp); have := ha 3 (by simp); have := ha 4 (by simp)
    simp at *; scalar_tac_preprocess; omega
  · simp [*];
    have := ha 0 (by simp); have := ha 1 (by simp); have := ha 2 (by simp); have := ha 3 (by simp); have := ha 4 (by simp)
    simp at *; scalar_tac_preprocess; omega
  · simp [*];
    have := ha 0 (by simp); have := ha 1 (by simp); have := ha 2 (by simp); have := ha 3 (by simp); have := ha 4 (by simp)
    simp at *; scalar_tac_preprocess; omega
  · simp [*];
    have := ha 0 (by simp); have := ha 1 (by simp); have := ha 2 (by simp); have := ha 3 (by simp); have := ha 4 (by simp)
    simp at *; scalar_tac_preprocess; omega
  · simp [*];
    have := ha 0 (by simp); have := ha 1 (by simp); have := ha 2 (by simp); have := ha 3 (by simp); have := ha 4 (by simp)
    simp at *; scalar_tac_preprocess; omega
  · simp [*];
    have := ha 0 (by simp); have := ha 1 (by simp); have := ha 2 (by simp); have := ha 3 (by simp); have := ha 4 (by simp)
    simp at *; scalar_tac_preprocess; omega
  -- remains to show that `ArrayU1289_to_Nat result = ArrayU645_to_Nat a * ArrayU645_to_Nat a`
  unfold ArrayU1289_to_Nat ArrayU645_to_Nat
  simp [Finset.sum_range_succ, *]
  -- `Array.make` and `square_internale._proof_5` still preent in goal

  sorry
