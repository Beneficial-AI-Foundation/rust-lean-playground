import Verify.Proofs.Defs
import Verify.Proofs.M

set_option linter.style.setOption false
set_option maxHeartbeats 2000000

/-! # SquareInternal

The main statement concerning `square_internal` is `square_internal_spec` (below).
-/

open Aeneas.Std Result
open rust_lean_playground

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `square_internal` -/

/- Using the specs with bit-vectors -/
-- attribute [-progress] U64.add_spec U64.mul_spec U128.add_spec U128.mul_spec
-- attribute [local progress] U64.add_bv_spec U64.mul_bv_spec U128.add_bv_spec U128.mul_bv_spec
attribute [progress] m_spec

/-- **Spec for `square_internal`**:
- Does not error and hence returns a result
- The result represents the square of the input field element
- Requires each limb to be less than 62 bits to prevent overflow
(The optimal bound on the limbs is 2^64 / √5  ≈ 2^62.839) -/
theorem square_internal_spec (a : Array U64 5#usize)
    (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    ∃ result, square_internal a = ok (result) ∧
    ArrayU1289_to_Nat result = ArrayU645_to_Nat a * ArrayU645_to_Nat a := by
  unfold square_internal
  -- testing to see if avoiding progress* is quicker
  progress
  progress
  · have := ha 0 (by omega)
    scalar_tac
  progress
  progress
  · have := ha 1 (by omega)
    scalar_tac
  progress
  progress
  · have := ha 2 (by omega)
    scalar_tac
  progress
  progress
  · have := ha 3 (by omega)
    scalar_tac
  progress
  progress
  progress
  progress
  progress
  progress
  · subst_vars
    have := ha 1 (by simp)
    have := ha 2 (by simp)
    scalar_tac
  progress
  progress
  progress
  progress
  · subst_vars
    have := ha 3 (by simp)
    have := ha 2 (by simp)
    scalar_tac
  progress
  progress
  progress
  progress
  · subst_vars
    have := ha 3 (by simp);
    have := ha 4 (by simp)
    scalar_tac
  progress
  progress
  · subst_vars
    have := ha 3 (by simp)
    have := ha 4 (by simp)
    have := ha 2 (by simp)
    scalar_tac
  progress
  progress
  progress
  progress
  · subst_vars
    have := ha 3 (by simp)
    have := ha 4 (by simp)
    scalar_tac
  progress
  progress
  progress
  · subst_vars
    have := ha 3 (by simp)
    have := ha 4 (by simp)
    scalar_tac
  progress
  progress
  progress
  -- remains to show that `ArrayU1289_to_Nat result = ArrayU645_to_Nat a * ArrayU645_to_Nat a`
  simp [ArrayU1289_to_Nat, ArrayU645_to_Nat, Finset.sum_range_succ, *]
  unfold Array.make at *
  simp_all
  ring
