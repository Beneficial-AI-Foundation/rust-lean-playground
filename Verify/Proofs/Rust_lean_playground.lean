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
set_option maxHeartbeats 5000000

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

/-- Auxiliary definition to interpret a vector of u32 as an integer -/
@[simp]
def ArrayU645_to_Nat (limbs : RustArray u64 5) : Nat :=
  ∑ i ∈ Finset.range 5, 2^(51 * i) * (limbs[i]!).toFin

/-- Curve25519 is the elliptic curve over the prime field with order p -/
def p : Nat := 2^255 - 19

def post (limbs res : RustArray u64 (5 : usize)) :=
  let limbs : RustArray u64 5 := limbs.cast (by simp);
  let res : RustArray u64 5 := res.cast (by simp);

  (∀ i, (h:i < 5) → res[i] ≤ (2^51 + (2^13 - 1) * 19).toUInt64)
   ∧ ArrayU645_to_Nat limbs ≡ ArrayU645_to_Nat res [MOD p] -- the one we want
--  ArrayU645_to_Nat r + p * (limbs[4].val >>> 51) = ArrayU645_to_Nat limbs -- fallback


attribute [spec, simp] Rust_lean_playground.LOW_51_BIT_MASK
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
    expose_names
    subst_vars
    simp [-Int.reducePow, -Nat.reducePow, Finset.range]

    have : ((UInt64.toNat limbs[1] &&& 2251799813685247) + UInt64.toNat limbs[0] >>> 51) <
        2 ^ 64 := by
      have : UInt64.toNat limbs[1] &&& 2251799813685247 ≤ 2251799813685247 := Nat.and_le_right
      have : UInt64.toNat limbs[0] >>> 51 ≤ 2^13 - 1 := by
        have := limbs[0].toNat_lt; omega
      grind
    rw [Nat.mod_eq_of_lt this]
    clear this

    have : ((UInt64.toNat limbs[2] &&& 2251799813685247) + UInt64.toNat limbs[1] >>> 51) <
        2 ^ 64 := by
      have : UInt64.toNat limbs[2] &&& 2251799813685247 ≤ 2251799813685247 := Nat.and_le_right
      have : UInt64.toNat limbs[1] >>> 51 ≤ 2^13 - 1 := by
        have := limbs[1].toNat_lt; omega
      grind
    rw [Nat.mod_eq_of_lt this]
    clear this

    have : ((UInt64.toNat limbs[3] &&& 2251799813685247) + UInt64.toNat limbs[2] >>> 51) <
        2 ^ 64 := by
      have : UInt64.toNat limbs[3] &&& 2251799813685247 ≤ 2251799813685247 := Nat.and_le_right
      have : UInt64.toNat limbs[2] >>> 51 ≤ 2^13 - 1 := by
        have := limbs[2].toNat_lt; omega
      grind
    rw [Nat.mod_eq_of_lt this]
    clear this

    have : ((UInt64.toNat limbs[4] &&& 2251799813685247) + UInt64.toNat limbs[3] >>> 51) <
        2 ^ 64 := by
      have : UInt64.toNat limbs[4] &&& 2251799813685247 ≤ 2251799813685247 := Nat.and_le_right
      have : UInt64.toNat limbs[3] >>> 51 ≤ 2^13 - 1 := by
        have := limbs[3].toNat_lt; omega
      grind
    rw [Nat.mod_eq_of_lt this]
    clear this

    have : ((UInt64.toNat limbs[0] &&& 2251799813685247) + UInt64.toNat limbs[4] >>> 51 * 19) <
        2 ^ 64 := by
      have : UInt64.toNat limbs[0] &&& 2251799813685247 ≤ 2251799813685247 := Nat.and_le_right
      have : UInt64.toNat limbs[4] >>> 51 * 19 ≤ (2^13 - 1) * 19 := by
        have := limbs[4].toNat_lt; omega
      grind
    rw [Nat.mod_eq_of_lt this]
    clear this

    rw [show 2251799813685247 = 2 ^ 51 - 1 by simp]

    rw [Nat.ModEq]
    unfold p

    have : 2^255 ≡ 19 [MOD p] := by
      unfold p
      rw [Nat.ModEq]
      grind


    -- Remaining goals is:
    -- ⊢ 2 ^ 204 * UInt64.toNat limbs[4] +
    --  (2 ^ 153 * UInt64.toNat limbs[3] +
    --  (2 ^ 102 * UInt64.toNat limbs[2] +
    --  (2 ^ 51 * UInt64.toNat limbs[1] +
    --  UInt64.toNat limbs[0]))) ≡
    --  2 ^ 204 * ((UInt64.toNat limbs[4] &&& 2 ^ 51 - 1) + UInt64.toNat limbs[3] >>> 51) +
    --  (2 ^ 153 * ((UInt64.toNat limbs[3] &&& 2 ^ 51 - 1) + UInt64.toNat limbs[2] >>> 51) +
    --  (2 ^ 102 * ((UInt64.toNat limbs[2] &&& 2 ^ 51 - 1) + UInt64.toNat limbs[1] >>> 51) +
    --  (2 ^ 51 * ((UInt64.toNat limbs[1] &&& 2 ^ 51 - 1) + UInt64.toNat limbs[0] >>> 51) +
    --  (UInt64.toNat limbs[0] &&& 2 ^ 51 - 1) + UInt64.toNat limbs[4] >>> 51 * 19))) [MOD p]

    sorry
