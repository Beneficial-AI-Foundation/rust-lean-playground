import Aeneas
import Verify.Src.RustLeanPlayground
import Mathlib

set_option linter.style.longLine false

/-! # Definitions

Common definitions used across proofs.
-/

open Aeneas.Std Result
open rust_lean_playground

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Auxiliary definitions for interpreting arrays as natural numbers -/

/-- Auxiliary definition to interpret a vector of u64 limbs as a natural number (51-bit limbs) -/
@[simp]
def ArrayU645_to_Nat (limbs : Array U64 5#usize) : Nat :=
  ∑ i ∈ Finset.range 5, 2^(51 * i) * (limbs[i]!).val

/-- Auxiliary definition to interpret a byte array as a natural number (little-endian) -/
@[simp]
def ArrayU832_to_Nat (bytes : Array U8 32#usize) : Nat :=
  ∑ i ∈ Finset.range 32, 2^(8 * i) * (bytes[i]!).val
