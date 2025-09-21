-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Verify.Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import Mathlib

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

def Rust_lean_playground.LOW_51_BIT_MASK : u64 := 2251799813685247

@[spec]
def Rust_lean_playground.reduce
  (limbs : (RustArray u64 (5 : usize)))
  : Result (RustArray u64 (5 : usize))
  := do
  let c0 : u64 ← (pure (← (← limbs[(0 : usize)]_?) >>>? (51 : i32)));
  let c1 : u64 ← (pure (← (← limbs[(1 : usize)]_?) >>>? (51 : i32)));
  let c2 : u64 ← (pure (← (← limbs[(2 : usize)]_?) >>>? (51 : i32)));
  let c3 : u64 ← (pure (← (← limbs[(3 : usize)]_?) >>>? (51 : i32)));
  let c4 : u64 ← (pure (← (← limbs[(4 : usize)]_?) >>>? (51 : i32)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (0 : usize)
        (← (← limbs[(0 : usize)]_?)
          &&&? Rust_lean_playground.LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (1 : usize)
        (← (← limbs[(1 : usize)]_?)
          &&&? Rust_lean_playground.LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (2 : usize)
        (← (← limbs[(2 : usize)]_?)
          &&&? Rust_lean_playground.LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (3 : usize)
        (← (← limbs[(3 : usize)]_?)
          &&&? Rust_lean_playground.LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (4 : usize)
        (← (← limbs[(4 : usize)]_?)
          &&&? Rust_lean_playground.LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (0 : usize)
        (← (← limbs[(0 : usize)]_?) +? (← c4 *? (19 : u64)))));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (1 : usize)
        (← (← limbs[(1 : usize)]_?) +? c0)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (2 : usize)
        (← (← limbs[(2 : usize)]_?) +? c1)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (3 : usize)
        (← (← limbs[(3 : usize)]_?) +? c2)));
  let limbs : (RustArray u64 (5 : usize)) ← (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        limbs
        (4 : usize)
        (← (← limbs[(4 : usize)]_?) +? c3)));
  limbs

/-- Fundamental property of bit operations: a number can be split into lower and upper bits -/
@[grind]
theorem UInt64.split_51 (a : UInt64) : a.toNat = (a.toNat &&& 2 ^ 51 - 1) +
    (a.toNat >>> 51) * 2^51 := by
  have := a.toNat.and_two_pow_sub_one_eq_mod 51
  have := a.toNat.shiftRight_eq_div_pow 51
  grind

/-- Unexpectedly needed to be explicit with this estimate. -/
theorem mask_shift_lt (a b : u64) :
    ((UInt64.toNat a &&& 2 ^ 51 - 1 ) + UInt64.toNat b >>> 51) < 2 ^ 64 := by
  have : UInt64.toNat a &&& 2 ^ 51 - 1  ≤ 2 ^ 51 - 1 := Nat.and_le_right
  have := b.toNat_lt
  grind

/-- Unexpectedly needed to be explicit with this estimate. -/
theorem mask_shift_lt' (a b : u64) :
    ((UInt64.toNat a &&& 2 ^ 51 - 1 ) + UInt64.toNat b >>> 51 * 19) < 2 ^ 64 := by
  have : UInt64.toNat a &&& 2 ^ 51 - 1  ≤ 2 ^ 51 - 1 := Nat.and_le_right
  have := b.toNat_lt
  grind

/-- Auxiliary definition to interpret a vector of u64 as an natural number -/
@[simp]
def ArrayU645_to_Nat (limbs : RustArray u64 5) : Nat :=
  ∑ i ∈ Finset.range 5, 2^(51 * i) * (limbs[i]!).toFin

/-- Curve25519 is the elliptic curve over the prime field with order p -/
def p : Nat := 2^255 - 19

def post (limbs res : RustArray u64 (5 : usize)) :=
  let limbs : RustArray u64 5 := limbs.cast (by simp);
  let res : RustArray u64 5 := res.cast (by simp);

  (∀ i, (h : i < 5) → res[i] ≤ (2^51 + (2^13 - 1) * 19).toUInt64)
   ∧ ArrayU645_to_Nat limbs ≡ ArrayU645_to_Nat res [MOD p]

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
    grind
