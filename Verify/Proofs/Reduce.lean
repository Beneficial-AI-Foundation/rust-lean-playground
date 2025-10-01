/- This file contains the spec theorem for `reduce` togeher with the proof.
Proof constructed by Clément Blaudeau -/

import Verify.Extraction.Reduce
import Mathlib

open Std.Do
open Std.Tactic

attribute [-simp] Int.reducePow Nat.reducePow

set_option mvcgen.warning false
set_option linter.style.setOption false
set_option maxHeartbeats 5000000

/-- Automatically identify `(5:usize).toNat` and `5` in array sizes -/
instance {α : Type} : Coe (RustArray α (5 : usize)) (RustArray α 5) where
  coe x := x.cast (by simp)

-- Theorem to upstream
theorem UInt64.shiftRight_lt (n : Nat) (h : n ≤ 64) (x : UInt64) : x.toNat >>> n < 2^(64 - n) := by
  have := UInt64.toNat_lt x; interval_cases n <;> omega

-- Theorem to upstream
theorem u64.and_eq_mod (x : u64) (y : Nat) : x.toNat &&& (2^y - 1) = x.toNat % 2^y := by simp

attribute [spec, simp] LOW_51_BIT_MASK

/-- Auxiliary definition to convert a vector of u64 to a natural number -/
@[simp]
def ArrayU645_to_Nat (limbs : RustArray u64 5) : Nat :=
  ∑ i ∈ Finset.range 5, 2^(51 * i) * (limbs[i]!).toFin

/-- Curve25519 is the elliptic curve over the prime field with order p -/
def p : Nat := 2^255 - 19

/-- Postcondition -/
def post (limbs result : RustArray u64 5) :=
  (∀ i, (h : i < 5) → result[i] ≤ (2^51 + (2^13 - 1) * 19).toUInt64) ∧
  ArrayU645_to_Nat limbs ≡ ArrayU645_to_Nat result [MOD p]

open Spec.BV in
/-- Spec theroem for `reduce` -/
theorem reduce.spec (limbs : (RustArray u64 (5 : usize))) :
    ⦃ ⌜ True ⌝ ⦄
    (reduce limbs)
    ⦃ ⇓ result => ⌜ post limbs result ⌝ ⦄ := by
  mvcgen [reduce]
  all_goals try simp [Vector.size]
  all_goals try subst_vars; simp_all; bv_decide
  constructor
  · intro i _
    interval_cases i
    all_goals subst_vars; simp [Nat.reducePow]; bv_decide
  · subst_vars
    simp [Finset.range]
    rw [show 2251799813685247 = 2^51 - 1 by simp [Nat.reducePow]]
    repeat rw [u64.and_eq_mod]
    repeat rw [Nat.mod_eq_of_lt (b := 2^64) (by have := UInt64.shiftRight_lt; grind)]
    unfold p Nat.ModEq
    omega
