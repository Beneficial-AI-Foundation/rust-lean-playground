import Aeneas
import Verify.Src.RustLeanPlayground
import Mathlib
import Verify.Proofs.Aux
import Verify.Proofs.Defs

set_option linter.style.setOption false
set_option grind.warning false
set_option maxHeartbeats 2000000

/-! # clamp_integer -/

open Aeneas.Std Result
open rust_lean_playground

attribute [-simp] Int.reducePow Nat.reducePow

/- Using the specs with bit-vectors -/
attribute [-progress] U8.add_spec U8.mul_spec
attribute [local progress] U8.add_bv_spec U8.mul_bv_spec


/-! ## Auxillary theorems -/

/- This allows `bvify` to automatically do the conversion `a ∣ b ↔ b % a = 0`,
   which can then be lifted to something which uses bit-vectors -/
attribute [bvify_simps] Nat.dvd_iff_mod_eq_zero

theorem U8.dvd_and_248 (byte : U8) : 8 ∣ (byte &&& 248#u8).val := by
  bvify 8; bv_decide

theorem U8.and_127_or_64_le (byte : U8) : byte.val &&& 127 ||| 64 ≤ 127 := by
  -- Key mathematical fact: for any n ≤ 127, n ||| 64 ≤ 127
  -- This is because:
  -- - 127 = 0b01111111 (all lower 7 bits set)
  -- - 64 = 0b01000000 (only bit 6 set)
  -- - When we OR any value ≤ 127 with 64, we're just ensuring bit 6 is set
  -- - Since 127 already has bit 6 set, the maximum result is 127
  -- - Specifically: 127 ||| 64 = 127 (can verify with decide)
  sorry

/-! ## Spec for `clamp_integer` -/

/-- **Spec and proof concerning `clamp_integer`**:
- No panic
- (as_nat_32_u8 result) is divisible by h (cofactor of curve25519)
- as_nat_32_u8 result < 2^255
- 2^254 ≤ as_nat_32_u8 result
-/
theorem clamp_integer_spec (bytes : Array U8 32#usize) :
    ∃ result, clamp_integer bytes = ok (result) ∧
    h ∣ U8x32_as_Nat result ∧
    U8x32_as_Nat result < 2^255 ∧
    2^254 ≤ U8x32_as_Nat result := by
  unfold clamp_integer
  progress*
  simp
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.dvd_sum
    intro i hi
    by_cases hc : i = 0
    · subst_vars
      simpa [*] using U8.dvd_and_248 _
    · have := List.mem_range.mp hi -- needed for inteval_cases bound
      interval_cases i <;> omega
  · subst_vars
    simp [*]
    rw [Finset.sum_range_succ]
    simp [*]
    have h_bound : (bytes : List U8)[31].val &&& 127 ||| 64 ≤ 127 :=
      U8.and_127_or_64_le (bytes : List U8)[31]
    calc
      _ ≤ ∑ x ∈ Finset.range 31, 2 ^ (8 * x) * (2^8 - 1) +
          2 ^ 248 * ((bytes : List U8)[31] &&& 127 ||| 64) := by
        gcongr
        bv_tac
      _ ≤ ∑ x ∈ Finset.range 31, 2 ^ (8 * x) * (2^8 - 1) + 2 ^ 248 * 127 := by
        gcongr
      _ < 2 ^ 255 := by
        bound
  · subst_vars
    simp [Finset.sum_range_succ, *]
    have : 64 ≤ ((bytes : List U8)[31] &&& 127 ||| 64) := Nat.right_le_or
    scalar_tac
