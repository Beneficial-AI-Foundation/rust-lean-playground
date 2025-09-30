import Aeneas
import Verify.Src.RustLeanPlayground
import Mathlib
import Verify.Proofs.Aux

set_option linter.style.setOption false
set_option maxHeartbeats 1000000

/-! # clamp_integer

-/

open Aeneas.Std Result
open rust_lean_playground

attribute [-simp] Int.reducePow Nat.reducePow

/- Using the specs with bit-vectors -/
attribute [-progress] U8.add_spec U8.mul_spec
attribute [local progress] U8.add_bv_spec U8.mul_bv_spec


/-! ## Auxillary theorems -/

theorem dvd_and_248 (byte : U8) : 8 ∣ (byte &&& 248#u8).val := by
  -- 248 = 0b11111000, so and with 248 clears the lowest 3 bits
  sorry

/-! ## Auxillary defs required for specs -/

/-- Auxiliary definition to interpret a vector of u32 as an integer -/
@[simp]
def ArrayU832.as_Nat (bytes : Array U8 32#usize) : Nat :=
  ∑ i ∈ Finset.range 32, 2^(8 * i) * (bytes[i]!).val

/-- The cofactor of curve25519 -/
@[simp]
def h : Nat := 8

/-! ## Spec for `clamp_integer` -/

/-- **Spec and proof concerning `clamp_integer`**:
- No panic
- to do: 2^254 ≤ as_nat_32_u8 result
- to do: as_nat_32_u8 result < 2^255
- (as_nat_32_u8 result) is divisible by 8 (the cofactor of curve25519)
-/
theorem clamp_integer_spec (bytes : Array U8 32#usize) :
    ∃ result, clamp_integer bytes = ok (result) ∧
    h ∣ (ArrayU832.as_Nat result)  := by
  unfold clamp_integer
  progress*
  simp
  apply Finset.dvd_sum
  intro i hi
  by_cases hc : i = 0
  · -- case i = 0
    subst_vars
    simpa [i1_post_1] using dvd_and_248 _
  · -- Case when 0 < i
    have := List.mem_range.mp hi
    interval_cases i <;> omega
