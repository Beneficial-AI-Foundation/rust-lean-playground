
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-- Partial right shift on u64 -/
instance UInt64.instHaxShiftRight : HaxShiftRight u64 u64 where
  shiftRight x y :=
    if (y ≤ 64) then pure (x >>> y)
    else .fail .integerOverflow

/-- Partial addition on usize -/
instance UInt64.instHaxAdd : HaxAdd u64 where
  add x y :=
    if (BitVec.uaddOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x + y)

-- Oliver
instance UInt64.instHaxMul : HaxMul u64 where
  mul x y :=
    if (BitVec.umulOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x * y)

-- Oliver
instance UInt64.instHaxSub : HaxSub u64 where
  sub x y :=
    if (BitVec.usubOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x - y)

infixl:60 " &&&? " => fun a b => pure (HAnd.hAnd a b)
@[simp, spec]
def Rust_primitives.Hax.Machine_int.bitand {α} [HAnd α α α] (a b: α) : Result α := a &&&? b

def Rust_primitives.Hax.Machine_int.shl (a : u64) (b : i32) : Result u64 := sorry

/-- Partial right shift on u64 (by i32) -/
instance UInt64.instHaxShiftRight' : HaxShiftRight u64 i32 where
  shiftRight x y := sorry

def Rust_lean_playground.reduce.LOW_51_BIT_MASK   : Result u64 := do
  (← (← Rust_primitives.Hax.Machine_int.shl (1 : u64) (51 : i32)) -? (1 : u64))

def Rust_lean_playground.reduce  (limbs : (RustArray u64 5))
  : Result (RustArray u64 5)
  := do
  let c0 : u64 ←
    (pure (← (← Core.Ops.Index.Index.index limbs (0 : usize)) >>>? (51 : i32)));
  let c1 : u64 ←
    (pure (← (← Core.Ops.Index.Index.index limbs (1 : usize)) >>>? (51 : i32)));
  let c2 : u64 ←
    (pure (← (← Core.Ops.Index.Index.index limbs (2 : usize)) >>>? (51 : i32)));
  let c3 : u64 ←
    (pure (← (← Core.Ops.Index.Index.index limbs (3 : usize)) >>>? (51 : i32)));
  let c4 : u64 ←
    (pure (← (← Core.Ops.Index.Index.index limbs (4 : usize)) >>>? (51 : i32)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (0 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Core.Ops.Index.Index.index limbs (0 : usize))
        Rust_lean_playground.reduce.LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (1 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Core.Ops.Index.Index.index limbs (1 : usize))
        Rust_lean_playground.reduce.LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (2 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Core.Ops.Index.Index.index limbs (2 : usize))
        Rust_lean_playground.reduce.LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (3 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Core.Ops.Index.Index.index limbs (3 : usize))
        Rust_lean_playground.reduce.LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (4 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Core.Ops.Index.Index.index limbs (4 : usize))
        Rust_lean_playground.reduce.LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (0 : usize)
      (← (← Core.Ops.Index.Index.index limbs (0 : usize)) +? (← c4 *? (19 :
      u64)))));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (1 : usize)
      (← (← Core.Ops.Index.Index.index limbs (1 : usize)) +? c0)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (2 : usize)
      (← (← Core.Ops.Index.Index.index limbs (2 : usize)) +? c1)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (3 : usize)
      (← (← Core.Ops.Index.Index.index limbs (3 : usize)) +? c2)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (4 : usize)
      (← (← Core.Ops.Index.Index.index limbs (4 : usize)) +? c3)));
  limbs
