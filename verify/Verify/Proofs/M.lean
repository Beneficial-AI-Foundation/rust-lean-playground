import Verify.Src.RustLeanPlayground

/-! # M

The main statement concerning `m` is `m_spec` (below).
-/

open Aeneas.Std Result
open rust_lean_playground

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `m` -/

/-- **Spec for `m`**:
- Does not overflow and hence returns a result
- The result equals the product of the two input values -/
@[progress]
theorem m_spec (x y : U64) :
    ∃ result, m x y = ok (result) ∧
    result.val = x.val * y.val := by
  unfold m
  progress*
  simp [*]; scalar_tac
