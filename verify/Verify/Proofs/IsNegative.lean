import Aeneas
import Verify.Src.RustLeanPlayground
import Verify.Proofs.Aux
import Verify.Proofs.Defs
import Verify.Proofs.ToBytes

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 3000000

set_option linter.hashCommand false
-- This activates/deactives some simps to reason about lists
#setup_aeneas_simps


/-! # IsNegative

The main statement concerning `is_negative` is `is_negative_spec` (below).
-/

open Aeneas.Std Result
open rust_lean_playground

attribute [-simp] Int.reducePow Nat.reducePow
attribute [progress] to_bytes_spec


/-! ## Spec for `is_negative` -/

/-- **Spec for `is_negative`**:
- Does not error and hence returns a result
- Returns true if and only if the least significant bit of the field element is 1
- This corresponds to checking if the field element is "negative" in the ed25519 sense -/
theorem is_negative_spec (limbs : Array U64 5#usize)
    (h : ∀ i, (h : i < 5) → (getElem limbs.val i (by scalar_tac)).val < 2 ^ 51) :
    ∃ result, is_negative limbs = ok (result) ∧
    (result = true ↔ U64x5_as_Nat limbs % 2 = 1) := by
  unfold is_negative
  sorry
