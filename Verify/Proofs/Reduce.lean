/- This file contains the spec theorem for `reduce` togeher with the proof. -/

import Verify.Extraction.Reduce
import Mathlib

open Std.Do
open Std.Tactic

set_option mvcgen.warning false

/- Three lemmas which were useful in the later proof -----------------------------------------/

/-- Fundamental property of bit operations: a number can be split into lower and upper bits -/
@[grind]
theorem UInt64.split_51 (a : UInt64) : a.toNat = (a.toNat &&& 2 ^ 51 - 1) +
    (a.toNat >>> 51) * 2^51 := by
  have := a.toNat.and_two_pow_sub_one_eq_mod 51; have := a.toNat.shiftRight_eq_div_pow 51
  grind

/-- Unexpectedly needed to be explicit with the following two estimates. -/
theorem mask_shift_lt (a b : u64) :
    ((UInt64.toNat a &&& 2 ^ 51 - 1 ) + UInt64.toNat b >>> 51) < 2 ^ 64 := by
  have : UInt64.toNat a &&& 2 ^ 51 - 1  ≤ 2 ^ 51 - 1 := Nat.and_le_right; have := b.toNat_lt
  grind
theorem mask_shift_lt' (a b : u64) :
    ((UInt64.toNat a &&& 2 ^ 51 - 1 ) + UInt64.toNat b >>> 51 * 19) < 2 ^ 64 := by
  have : UInt64.toNat a &&& 2 ^ 51 - 1  ≤ 2 ^ 51 - 1 := Nat.and_le_right; have := b.toNat_lt
  grind
/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Auxiliary definition to convert a vector of u64 to a natural number -/
@[simp]
def ArrayU645_to_Nat (limbs : RustArray u64 5) : Nat :=
  ∑ i ∈ Finset.range 5, 2^(51 * i) * (limbs[i]!).toFin

/-- Curve25519 is the elliptic curve over the prime field with order p -/
def p : Nat := 2^255 - 19

def post (limbs res : RustArray u64 (5 : usize)) :=
  let limbs : RustArray u64 5 := limbs.cast (by simp);
  let res : RustArray u64 5 := res.cast (by simp);

  (∀ i, (h : i < 5) → res[i] ≤ (2^51 + (2^13 - 1) * 19).toUInt64) -- all limbs are bounded
   ∧ ArrayU645_to_Nat limbs ≡ ArrayU645_to_Nat res [MOD p] --

attribute [spec, simp] Rust_lean_playground.LOW_51_BIT_MASK

set_option maxHeartbeats 5000000 in
-- likely that this could be done more efficiently
theorem reduce.spec (limbs : (RustArray u64 (5 : usize))) :
    ⦃ ⌜ True ⌝ ⦄
    (Rust_lean_playground.reduce limbs)
    ⦃ ⇓ res => ⌜ post limbs res ⌝ ⦄ := by
  open Spec.BV in mvcgen [Rust_lean_playground.reduce]
  -- No overflow because of the bit shift and bit mask prior to addition
  all_goals simp [Vector.size] at *
  all_goals try (subst_vars; (try simp at *); bv_decide)
  -- Remains to show the post condition
  constructor
  · -- All the limbs of the result are bounded
    intro i _; interval_cases i
    all_goals subst_vars; simp; bv_decide
  · -- The result is equal [Mod p] the input
    subst_vars
    simp [-Int.reducePow, -Nat.reducePow, Finset.range]
    rw [Nat.ModEq, show 2251799813685247 = 2 ^ 51 - 1 by simp]
    unfold p
    rw [Nat.mod_eq_of_lt (mask_shift_lt limbs[4] limbs[3]),
      Nat.mod_eq_of_lt (mask_shift_lt limbs[3] limbs[2]),
      Nat.mod_eq_of_lt (mask_shift_lt limbs[2] limbs[1]),
      Nat.mod_eq_of_lt (mask_shift_lt limbs[1] limbs[0]),
      Nat.mod_eq_of_lt (mask_shift_lt' limbs[0] limbs[4])]
    -- Here we need `limbs[0].split_51`, `limbs[1].split_51`, etc., but grind does it automatically
    -- since we tagged the theorem.
    grind
