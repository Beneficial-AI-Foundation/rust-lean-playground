import Verify.Lib.Lib
import Verify.Extraction.Reduce
import Mathlib

open Std.Do
open Std.Tactic

/-! Spec functions and proofs -/

-- Auxiliary definition to interpret a vector of u32 as an integer
def U64x5_toNat (limbs : (RustArray u64 5)) : Nat :=
  ∑ i ∈ Finset.range 5, 2^(51 * i) * (limbs[i]!).toFin

-- Curve25519 is the elliptic curve over the prime field with order p
def p : Nat := 2^255 - 19

/-! ## Auxillary theorems -/

theorem LOW_51_BIT_MASK_val_eq : LOW_51_BIT_MASK.toFin = 2^51 - 1 := by
  unfold LOW_51_BIT_MASK; decide

theorem reduce_spec (limbs : (RustArray u64 5)) :
    ⦃ ⌜True⌝ ⦄
    reduce limbs
    ⦃ ⇓ result ↦
      (∀ (i : Fin 5), (result[i]!).toFin.toNat ≤ 2^51 + (2^13 - 1) * 19) ∧
      U64x5_toNat limbs ≡ U64x5_toNat result [MOD p] ⦄ := by


  sorry
