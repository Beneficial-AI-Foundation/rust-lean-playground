import Aeneas
import Verify.Src.RustLeanPlayground
import Mathlib
import Verify.Proofs.Aux

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

/-! # clamp_integer

-/

open Aeneas.Std Result
open rust_lean_playground

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Auxillary defs required for specs -/

/-- Auxiliary definition to interpret a vector of u32 as an integer -/
@[simp]
def ArrayU645_to_Nat (limbs : Array U64 5#usize) : Nat :=
  ∑ i ∈ Finset.range 5, 2^(51 * i) * (limbs[i]!).val

/-- Curve25519 is the elliptic curve over the prime field with order p -/
def p : Nat := 2^255 - 19

/-! ## Spec for `clamp_integer` -/

/-- **Spec and proof concerning `clamp_integer`**:
- No panic
- To do: The result is equal to the input mod p. -/
theorem clamp_integer_spec (bytes : Array U8 32#usize) :
    ∃ result, clamp_integer bytes = ok (result) := by
  unfold clamp_integer
  progress*
