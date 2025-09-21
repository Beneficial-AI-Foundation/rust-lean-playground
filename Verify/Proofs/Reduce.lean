/- This file contains the spec theorem for `reduce` togeher with the proof.
Proof constructed by Clément Blaudeau -/

import Verify.Extraction.Reduce
import Mathlib

open Std.Do
open Std.Tactic

set_option mvcgen.warning false

/-- Automatically identify `(5:usize).toNat` and `5` in array sizes -/
instance {α : Type} : Coe (RustArray α (5:usize)) (RustArray α 5) where
  coe x := x.cast (by simp)

theorem UInt64.shiftRight_lt (n : Nat) (h : n ≤ 64) (x : UInt64) : x.toNat >>> n < 2^(64 - n) := by
  have := UInt64.toNat_lt x; interval_cases n <;> omega

/-- Auxiliary definition to convert a vector of u64 to a natural number -/
@[simp]
def ArrayU645_to_Nat (limbs : RustArray u64 5) : Nat :=
  ∑ i ∈ Finset.range 5, 2^(51 * i) * (limbs[i]!).toFin

/-- Curve25519 is the elliptic curve over the prime field with order p -/
def p : Nat := 2^255 - 19

/-- Postcondition -/
def post (limbs result : RustArray u64 5) :=
  (∀ i, (h:i < 5) → result[i] ≤ (2^51 + (2^13 - 1) * 19).toUInt64)
  ∧ ArrayU645_to_Nat limbs ≡ ArrayU645_to_Nat result [MOD p]

attribute [spec, simp] LOW_51_BIT_MASK

set_option maxHeartbeats 5000000 in
-- Simp is expensive here
/-- Spec theroem for `reduce` -/
theorem reduce.spec (limbs : (RustArray u64 (5 : usize))) :
    ⦃ ⌜ True ⌝ ⦄
    (reduce limbs)
    ⦃ ⇓ result => ⌜ post limbs result ⌝ ⦄ := by
  -- Step through the program using the [Spec.BV] set of triples
  open Spec.BV in
  mvcgen [reduce]
  -- Discard array access side conditions
  all_goals simp [Vector.size, -Int.reducePow, -Nat.reducePow] at *
  -- Discard arithmetic overflows
  all_goals try (subst_vars; simp at * ; bv_decide)
  -- Remains to show the post condition
  constructor
  · -- All the limbs of the result are bounded
    intro i _; interval_cases i
    all_goals subst_vars; simp; bv_decide
  · -- The result is equal [Mod p] the input
    subst_vars; simp [-Int.reducePow, -Nat.reducePow, Finset.range] at *
    rw [show 2251799813685247 = 2 ^ 51 - 1 by simp]
    -- Masking is remainder
    have h_mask : ∀ (x : u64) (y:Nat), x.toNat &&& (2^y - 1) = x.toNat % 2^y := by simp
    repeat rw [h_mask]
    -- Remove `% 2^64` on results of arithmetic operations
    have := UInt64.shiftRight_lt 51 (by simp)
    repeat rw [Nat.mod_eq_of_lt (b := 2^64) (by grind)]
    -- Unfold and finish
    unfold p Nat.ModEq
    omega
