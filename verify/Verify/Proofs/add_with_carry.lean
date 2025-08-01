import Aeneas
import Verify.Src.RustLeanPlayground

/-! # add_with_carry

The main statement concerning `add_with_carry` is `add_with_carry_spec` (see the end of this file).

Lean code is from `https://github.com/AeneasVerif/aeneas`.
-/

open Aeneas.Std Result
open rust_lean_playground

set_option linter.hashCommand false
#setup_aeneas_simps


/-! ## Auxillary defs and theorems -/

attribute [-simp] Int.reducePow Nat.reducePow

-- Auxiliary definition to interpret a vector of u32 as a mathematical integer
@[simp]
def toInt (l : List U32) : Int :=
  match l with
  | [] => 0
  | x :: l =>
    x + 2 ^ 32 * toInt l

@[simp]
theorem toInt_drop (l : List U32) (i : Nat) (h0 : i < l.length) :
  toInt (l.drop i) = l[i]! + 2 ^ 32 * toInt (l.drop (i + 1)) := by
  cases l with
  | nil => simp at *
  | cons hd tl =>
    simp_all
    dcases i = 0 <;> simp_all
    have := toInt_drop tl (i - 1) (by scalar_tac)
    simp_all
    scalar_nf at *
    have : 1 + (i - 1) = i := by scalar_tac
    simp [*]

@[simp]
theorem toInt_update (l : List U32) (i : Nat) (x : U32) (h0 : i < l.length) :
  toInt (l.set i x) = toInt l + 2 ^ (32 * i) * (x - l[i]!) := by
  cases l with
  | nil => simp at *
  | cons hd tl =>
    simp_all
    dcases i = 0 <;> simp_all
    · scalar_eq_nf
    · have := toInt_update tl (i - 1) x (by scalar_tac)
      simp_all
      scalar_nf at *
      scalar_eq_nf
      have : 2 ^ (i * 32) = (2 ^ ((i - 1) * 32) * 4294967296 : Int) := by
        scalar_nf
        have : i = i - 1 + 1 := by scalar_tac
        conv => lhs; rw [this]
        scalar_nf
      simp [mul_assoc, *]
      scalar_eq_nf

/-! ## Proofs concerning `add_with_carry` -/

@[progress]
theorem add_with_carry_loop_spec
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (c0 : U8) (i : Usize)
  (hLength : x.length = y.length)
  (hi : i.val ≤ x.length)
  (hCarryLe : c0.val ≤ 1) :
  ∃ x' c1, add_with_carry_loop x y c0 i = ok (c1, x') ∧
  x'.length = x.length ∧
  c1.val ≤ 1 ∧
  toInt x' + c1.val * 2 ^ (32 * x'.length) =
    toInt x + 2 ^ (32 * i.val) * toInt (y.val.drop i.val) + c0.val * 2 ^ (32 * i.val) := by
  unfold add_with_carry_loop
  simp
  split
  · progress as ⟨ xi ⟩
    progress as ⟨ c0u ⟩
    have : c0u.val = c0.val := by scalar_tac
    progress as ⟨ s1, c1, hConv1 ⟩
    progress as ⟨ yi ⟩
    progress as ⟨ s2, c2, hConv2 ⟩
    progress as ⟨ c1u, hc1u ⟩
    progress as ⟨ c2u, hc2u ⟩
    progress as ⟨ c3, hc3 ⟩
    progress as ⟨ _ ⟩
    progress as ⟨ i1 ⟩
    have : c3.val ≤ 1 := by
      scalar_tac +split
    progress as ⟨ c4, x1, _, _, hc4 ⟩
    -- Proving the post-condition
    split_conjs
    · simp [*]
    · simp [*]
    · simp [hc4]
      have hxUpdate := toInt_update x.val i.val s2 (by scalar_tac)
      simp [hxUpdate]; clear hxUpdate
      have hyDrop := toInt_drop y.val i.val (by scalar_tac)
      simp [hyDrop]; clear hyDrop
      scalar_eq_nf
      -- The best way is to do a case disjunction and treat each sub-case separately
      split at hConv1 <;>
      split at hConv2
      · have hConv1' : (s1.val : Int) = xi.val + c0u.val - U32.size := by scalar_tac
        have hConv2' : (s2.val : Int) = s1.val + yi.val - U32.size := by scalar_tac
        simp [hConv2', hConv1']
        /- `U32.size_eq` is a lemma which allows to simplify `U32.size`.
           But you can also simply do `simp [U32.size]`, which simplifies
           `U32.size` to `2^U32.numBits`, then simplify `U32.numBits`. -/
        simp [*, U32.size_eq]
        scalar_eq_nf
      · have hConv1' : (s1.val : Int) = xi.val + c0u.val - U32.size := by scalar_tac
        simp [hConv2, hConv1']
        simp [*, U32.size_eq]
        scalar_eq_nf
      · have hConv2' : (s2.val : Int) = s1.val + yi.val - U32.size := by scalar_tac
        simp [hConv2', hConv1]
        simp [*, U32.size_eq]
        scalar_eq_nf
      · simp [*, U32.size_eq]
        scalar_eq_nf
  · simp_all
    scalar_tac
termination_by x.length - i.val
decreasing_by scalar_decr_tac

/-- **Spec and proof concerning `add_with_carry`**:
Assume that:
- `x` has the same length as `y`
Then:
- `add_with_carry x y` returns ok with result `(c, x')`
- `x'` has the same length as `x`
- `c.val ≤ 1`
- `toInt x' + c.val * 2 ^ (32 * x'.length) = toInt x + toInt y`. -/
@[progress]
theorem add_with_carry_spec
  (x : alloc.vec.Vec U32) (y : alloc.vec.Vec U32) (hLength : x.length = y.length) :
  ∃ x' c, add_with_carry x y = ok (c, x') ∧
  x'.length = x.length ∧
  c.val ≤ 1 ∧
  toInt x' + c.val * 2 ^ (32 * x'.length) = toInt x + toInt y := by
  unfold add_with_carry
  progress as ⟨ c, x' ⟩
  simp_all
