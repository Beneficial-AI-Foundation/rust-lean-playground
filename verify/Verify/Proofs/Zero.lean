import Aeneas
import Verify.Src.RustLeanPlayground
import Mathlib
import Verify.Proofs.Aux
import Verify.Proofs.Defs

set_option linter.style.longLine false

/-! # Zero

The main statement concerning `ZERO` is `ZERO_spec` (below).
-/

open Aeneas.Std Result
open rust_lean_playground

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `ZERO` -/

/-- **Spec for `ZERO`**:
- The ZERO constant represents the scalar 0 -/
theorem ZERO_spec : ArrayU645_to_Nat ZERO = 0 := by
  unfold ZERO
  decide
