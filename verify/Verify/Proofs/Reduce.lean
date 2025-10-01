import Aeneas
import Verify.Src.RustLeanPlayground
import Mathlib
import Verify.Proofs.Aux
import Verify.Proofs.Defs

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 1000000

/-! # Reduce

The main statement concerning `reduce` is `reduce_spec` (below).
-/

open Aeneas.Std Result
open rust_lean_playground

attribute [-simp] Int.reducePow Nat.reducePow

/- The `scalar_tac_simps` is important in particular for `scalar_tac` to know
   about this constant (otherwise it treats it as an opaque definition). -/
attribute [simp, scalar_tac_simps] LOW_51_BIT_MASK_val_eq

/-- Curve25519 is the elliptic curve over the prime field with order p -/
def p : Nat := 2^255 - 19

/- Using the specs with bit-vectors -/
attribute [-progress] U64.add_spec U64.mul_spec
attribute [local progress] U64.add_bv_spec U64.mul_bv_spec


/-! ## Spec for `reduce` -/

/-- **Spec and proof concerning `reduce`**:
- Does not overflow and hence returns a result
- All the limbs of the result are small, ≤ 2^(51 + ε)
- The result is equal to the input mod p. -/
theorem reduce_spec (limbs : Array U64 5#usize) :
    ∃ result, reduce limbs = ok (result) ∧
    (∀ i, i < 5 → (result[i]!).val ≤ 2^51 + (2^13 - 1) * 19) ∧
    ArrayU645_to_Nat limbs ≡ ArrayU645_to_Nat result [MOD p] := by
  unfold reduce
  progress*
  all_goals try simp [*]; scalar_tac
  constructor
  · intro i _
    interval_cases i
    all_goals simp [*]; scalar_tac
  · simp [Finset.sum_range_succ, p, Nat.ModEq, *]; omega
