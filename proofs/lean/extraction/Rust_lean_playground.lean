
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

def Rust_lean_playground.Field.add_assign  (lhs : (RustArray u64 5))
  (rhs : (RustArray u64 5))
  : Result (RustArray u64 5)
  := do
  let lhs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (5 : usize)
      (fun (lhs : (RustArray u64 5)) (_ : usize) =>(do true : Result Bool))
      lhs
      (fun (lhs : (RustArray u64 5)) (i : usize) =>(do
          (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            lhs
            i
            (← (← Core.Ops.Index.Index.index lhs i) +?
            (← Core.Ops.Index.Index.index rhs i))) : Result
          (RustArray u64 5)))));
  lhs

def Rust_lean_playground.Field.add  (lhs : (RustArray u64 5))
  (rhs : (RustArray u64 5))
  : Result (RustArray u64 5)
  := do
  let output : (RustArray u64 5) ← (pure lhs);
  let output : (RustArray u64 5) ←
    (pure (← Rust_lean_playground.Field.add_assign output rhs));
  output

def Rust_lean_playground.Field.mul.m  (x : u64) (y : u64)
  : Result TODO_LINE_700
  := do
  (← (← Rust_primitives.Hax.cast_op x) *? (← Rust_primitives.Hax.cast_op y))

def Rust_lean_playground.Field.mul.LOW_51_BIT_MASK   : Result u64 := do
  (← (← Rust_primitives.Hax.Machine_int.shl (1 : u64) (51 : i32)) -? (1 : u64))

def Rust_lean_playground.Field.mul  (lhs : (RustArray u64 5))
  (rhs : (RustArray u64 5))
  : Result (RustArray u64 5)
  := do
  let (a : (RustArray u64 5)) ← (pure lhs);
  let (b : (RustArray u64 5)) ← (pure rhs);
  let b1_19 : u64 ←
    (pure (← (← Core.Ops.Index.Index.index b (1 : usize)) *? (19 : u64)));
  let b2_19 : u64 ←
    (pure (← (← Core.Ops.Index.Index.index b (2 : usize)) *? (19 : u64)));
  let b3_19 : u64 ←
    (pure (← (← Core.Ops.Index.Index.index b (3 : usize)) *? (19 : u64)));
  let b4_19 : u64 ←
    (pure (← (← Core.Ops.Index.Index.index b (4 : usize)) *? (19 : u64)));
  let (c0 : TODO_LINE_700) ←
    (pure
    (← (← (← (← (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (0 : usize))
      (← Core.Ops.Index.Index.index b (0 : usize))) +?
    (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (4 : usize))
      b1_19)) +? (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (3 : usize))
      b2_19)) +? (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (2 : usize))
      b3_19)) +? (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (1 : usize))
      b4_19)));
  let (c1 : TODO_LINE_700) ←
    (pure
    (← (← (← (← (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (1 : usize))
      (← Core.Ops.Index.Index.index b (0 : usize))) +?
    (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (0 : usize))
      (← Core.Ops.Index.Index.index b (1 : usize)))) +?
    (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (4 : usize))
      b2_19)) +? (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (3 : usize))
      b3_19)) +? (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (2 : usize))
      b4_19)));
  let (c2 : TODO_LINE_700) ←
    (pure
    (← (← (← (← (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (2 : usize))
      (← Core.Ops.Index.Index.index b (0 : usize))) +?
    (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (1 : usize))
      (← Core.Ops.Index.Index.index b (1 : usize)))) +?
    (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (0 : usize))
      (← Core.Ops.Index.Index.index b (2 : usize)))) +?
    (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (4 : usize))
      b3_19)) +? (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (3 : usize))
      b4_19)));
  let (c3 : TODO_LINE_700) ←
    (pure
    (← (← (← (← (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (3 : usize))
      (← Core.Ops.Index.Index.index b (0 : usize))) +?
    (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (2 : usize))
      (← Core.Ops.Index.Index.index b (1 : usize)))) +?
    (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (1 : usize))
      (← Core.Ops.Index.Index.index b (2 : usize)))) +?
    (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (0 : usize))
      (← Core.Ops.Index.Index.index b (3 : usize)))) +?
    (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (4 : usize))
      b4_19)));
  let (c4 : TODO_LINE_700) ←
    (pure
    (← (← (← (← (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (4 : usize))
      (← Core.Ops.Index.Index.index b (0 : usize))) +?
    (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (3 : usize))
      (← Core.Ops.Index.Index.index b (1 : usize)))) +?
    (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (2 : usize))
      (← Core.Ops.Index.Index.index b (2 : usize)))) +?
    (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (1 : usize))
      (← Core.Ops.Index.Index.index b (3 : usize)))) +?
    (← Rust_lean_playground.Field.mul.m
      (← Core.Ops.Index.Index.index a (0 : usize))
      (← Core.Ops.Index.Index.index b (4 : usize)))));
  let (_ : Rust_primitives.Hax.Tuple0) ←
    (pure
    if true then
      do
      let (_ : Rust_primitives.Hax.Tuple0) ←
        (pure
        (← Hax_lib.assert
          (← Rust_primitives.Hax.Machine_int.lt
            (← Core.Ops.Index.Index.index a (0 : usize))
            (← Rust_primitives.Hax.Machine_int.shl (1 : u64) (54 : i32)))));
      Rust_primitives.Hax.Tuple0.mk
    else
      do
      Rust_primitives.Hax.Tuple0.mk);
  let (_ : Rust_primitives.Hax.Tuple0) ←
    (pure
    if true then
      do
      let (_ : Rust_primitives.Hax.Tuple0) ←
        (pure
        (← Hax_lib.assert
          (← Rust_primitives.Hax.Machine_int.lt
            (← Core.Ops.Index.Index.index b (0 : usize))
            (← Rust_primitives.Hax.Machine_int.shl (1 : u64) (54 : i32)))));
      Rust_primitives.Hax.Tuple0.mk
    else
      do
      Rust_primitives.Hax.Tuple0.mk);
  let (_ : Rust_primitives.Hax.Tuple0) ←
    (pure
    if true then
      do
      let (_ : Rust_primitives.Hax.Tuple0) ←
        (pure
        (← Hax_lib.assert
          (← Rust_primitives.Hax.Machine_int.lt
            (← Core.Ops.Index.Index.index a (1 : usize))
            (← Rust_primitives.Hax.Machine_int.shl (1 : u64) (54 : i32)))));
      Rust_primitives.Hax.Tuple0.mk
    else
      do
      Rust_primitives.Hax.Tuple0.mk);
  let (_ : Rust_primitives.Hax.Tuple0) ←
    (pure
    if true then
      do
      let (_ : Rust_primitives.Hax.Tuple0) ←
        (pure
        (← Hax_lib.assert
          (← Rust_primitives.Hax.Machine_int.lt
            (← Core.Ops.Index.Index.index b (1 : usize))
            (← Rust_primitives.Hax.Machine_int.shl (1 : u64) (54 : i32)))));
      Rust_primitives.Hax.Tuple0.mk
    else
      do
      Rust_primitives.Hax.Tuple0.mk);
  let (_ : Rust_primitives.Hax.Tuple0) ←
    (pure
    if true then
      do
      let (_ : Rust_primitives.Hax.Tuple0) ←
        (pure
        (← Hax_lib.assert
          (← Rust_primitives.Hax.Machine_int.lt
            (← Core.Ops.Index.Index.index a (2 : usize))
            (← Rust_primitives.Hax.Machine_int.shl (1 : u64) (54 : i32)))));
      Rust_primitives.Hax.Tuple0.mk
    else
      do
      Rust_primitives.Hax.Tuple0.mk);
  let (_ : Rust_primitives.Hax.Tuple0) ←
    (pure
    if true then
      do
      let (_ : Rust_primitives.Hax.Tuple0) ←
        (pure
        (← Hax_lib.assert
          (← Rust_primitives.Hax.Machine_int.lt
            (← Core.Ops.Index.Index.index b (2 : usize))
            (← Rust_primitives.Hax.Machine_int.shl (1 : u64) (54 : i32)))));
      Rust_primitives.Hax.Tuple0.mk
    else
      do
      Rust_primitives.Hax.Tuple0.mk);
  let (_ : Rust_primitives.Hax.Tuple0) ←
    (pure
    if true then
      do
      let (_ : Rust_primitives.Hax.Tuple0) ←
        (pure
        (← Hax_lib.assert
          (← Rust_primitives.Hax.Machine_int.lt
            (← Core.Ops.Index.Index.index a (3 : usize))
            (← Rust_primitives.Hax.Machine_int.shl (1 : u64) (54 : i32)))));
      Rust_primitives.Hax.Tuple0.mk
    else
      do
      Rust_primitives.Hax.Tuple0.mk);
  let (_ : Rust_primitives.Hax.Tuple0) ←
    (pure
    if true then
      do
      let (_ : Rust_primitives.Hax.Tuple0) ←
        (pure
        (← Hax_lib.assert
          (← Rust_primitives.Hax.Machine_int.lt
            (← Core.Ops.Index.Index.index b (3 : usize))
            (← Rust_primitives.Hax.Machine_int.shl (1 : u64) (54 : i32)))));
      Rust_primitives.Hax.Tuple0.mk
    else
      do
      Rust_primitives.Hax.Tuple0.mk);
  let (_ : Rust_primitives.Hax.Tuple0) ←
    (pure
    if true then
      do
      let (_ : Rust_primitives.Hax.Tuple0) ←
        (pure
        (← Hax_lib.assert
          (← Rust_primitives.Hax.Machine_int.lt
            (← Core.Ops.Index.Index.index a (4 : usize))
            (← Rust_primitives.Hax.Machine_int.shl (1 : u64) (54 : i32)))));
      Rust_primitives.Hax.Tuple0.mk
    else
      do
      Rust_primitives.Hax.Tuple0.mk);
  let (_ : Rust_primitives.Hax.Tuple0) ←
    (pure
    if true then
      do
      let (_ : Rust_primitives.Hax.Tuple0) ←
        (pure
        (← Hax_lib.assert
          (← Rust_primitives.Hax.Machine_int.lt
            (← Core.Ops.Index.Index.index b (4 : usize))
            (← Rust_primitives.Hax.Machine_int.shl (1 : u64) (54 : i32)))));
      Rust_primitives.Hax.Tuple0.mk
    else
      do
      Rust_primitives.Hax.Tuple0.mk);
  let out : (RustArray u64 5) ←
    (pure (← Rust_primitives.Hax.repeat (0 : u64) (5 : usize)));
  let c1 : TODO_LINE_700 ←
    (pure
    (← c1 +? (← Rust_primitives.Hax.cast_op
      (← Rust_primitives.Hax.cast_op (← c0 >>>? (51 : i32))))));
  let out : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (0 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Rust_primitives.Hax.cast_op c0)
        Rust_lean_playground.Field.mul.LOW_51_BIT_MASK)));
  let c2 : TODO_LINE_700 ←
    (pure
    (← c2 +? (← Rust_primitives.Hax.cast_op
      (← Rust_primitives.Hax.cast_op (← c1 >>>? (51 : i32))))));
  let out : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (1 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Rust_primitives.Hax.cast_op c1)
        Rust_lean_playground.Field.mul.LOW_51_BIT_MASK)));
  let c3 : TODO_LINE_700 ←
    (pure
    (← c3 +? (← Rust_primitives.Hax.cast_op
      (← Rust_primitives.Hax.cast_op (← c2 >>>? (51 : i32))))));
  let out : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (2 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Rust_primitives.Hax.cast_op c2)
        Rust_lean_playground.Field.mul.LOW_51_BIT_MASK)));
  let c4 : TODO_LINE_700 ←
    (pure
    (← c4 +? (← Rust_primitives.Hax.cast_op
      (← Rust_primitives.Hax.cast_op (← c3 >>>? (51 : i32))))));
  let out : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (3 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Rust_primitives.Hax.cast_op c3)
        Rust_lean_playground.Field.mul.LOW_51_BIT_MASK)));
  let (carry : u64) ←
    (pure (← Rust_primitives.Hax.cast_op (← c4 >>>? (51 : i32))));
  let out : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (4 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Rust_primitives.Hax.cast_op c4)
        Rust_lean_playground.Field.mul.LOW_51_BIT_MASK)));
  let out : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (0 : usize)
      (← (← Core.Ops.Index.Index.index out (0 : usize)) +? (← carry *? (19 :
      u64)))));
  let out : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (1 : usize)
      (← (← Core.Ops.Index.Index.index out (1 : usize)) +?
      (← (← Core.Ops.Index.Index.index out (0 : usize)) >>>? (51 : i32)))));
  let out : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (0 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Core.Ops.Index.Index.index out (0 : usize))
        Rust_lean_playground.Field.mul.LOW_51_BIT_MASK)));
  out

def Rust_lean_playground.Field.mul_assign  (lhs : (RustArray u64 5))
  (rhs : (RustArray u64 5))
  : Result (RustArray u64 5)
  := do
  let result : (RustArray u64 5) ←
    (pure (← Rust_lean_playground.Field.mul lhs rhs));
  let lhs : (RustArray u64 5) ← (pure result);
  lhs

def Rust_lean_playground.Field.from_limbs  (limbs : (RustArray u64 5))
  : Result (RustArray u64 5)
  := do
  limbs

def Rust_lean_playground.Field.ZERO   : Result (RustArray u64 5) := do
  #v[(0 : u64), (0 : u64), (0 : u64), (0 : u64), (0 : u64)]

def Rust_lean_playground.Field.ONE   : Result (RustArray u64 5) := do
  (← Rust_lean_playground.Field.from_limbs
    #v[(1 : u64), (0 : u64), (0 : u64), (0 : u64), (0 : u64)])

def Rust_lean_playground.Field.MINUS_ONE   : Result (RustArray u64 5) := do
  (← Rust_lean_playground.Field.from_limbs
    #v[(2251799813685228 : u64),
      (2251799813685247 : u64),
      (2251799813685247 : u64),
      (2251799813685247 : u64),
      (2251799813685247 : u64)])

def Rust_lean_playground.Field.reduce.LOW_51_BIT_MASK   : Result u64 := do
  (← (← Rust_primitives.Hax.Machine_int.shl (1 : u64) (51 : i32)) -? (1 : u64))

def Rust_lean_playground.Field.reduce  (limbs : (RustArray u64 5))
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
        Rust_lean_playground.Field.reduce.LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (1 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Core.Ops.Index.Index.index limbs (1 : usize))
        Rust_lean_playground.Field.reduce.LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (2 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Core.Ops.Index.Index.index limbs (2 : usize))
        Rust_lean_playground.Field.reduce.LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (3 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Core.Ops.Index.Index.index limbs (3 : usize))
        Rust_lean_playground.Field.reduce.LOW_51_BIT_MASK)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (4 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Core.Ops.Index.Index.index limbs (4 : usize))
        Rust_lean_playground.Field.reduce.LOW_51_BIT_MASK)));
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

def Rust_lean_playground.Field.sub  (lhs : (RustArray u64 5))
  (rhs : (RustArray u64 5))
  : Result (RustArray u64 5)
  := do
  (← Rust_lean_playground.Field.reduce
    #v[(← (← (← Core.Ops.Index.Index.index lhs (0 : usize)) +?
      (36028797018963664 : u64)) -? (← Core.Ops.Index.Index.index
        rhs
        (0 : usize))),
      (← (← (← Core.Ops.Index.Index.index lhs (1 : usize)) +? (36028797018963952
      : u64)) -? (← Core.Ops.Index.Index.index rhs (1 : usize))),
      (← (← (← Core.Ops.Index.Index.index lhs (2 : usize)) +? (36028797018963952
      : u64)) -? (← Core.Ops.Index.Index.index rhs (2 : usize))),
      (← (← (← Core.Ops.Index.Index.index lhs (3 : usize)) +? (36028797018963952
      : u64)) -? (← Core.Ops.Index.Index.index rhs (3 : usize))),
      (← (← (← Core.Ops.Index.Index.index lhs (4 : usize)) +? (36028797018963952
      : u64)) -? (← Core.Ops.Index.Index.index rhs (4 : usize)))])

def Rust_lean_playground.Field.sub_assign  (lhs : (RustArray u64 5))
  (rhs : (RustArray u64 5))
  : Result (RustArray u64 5)
  := do
  let result : (RustArray u64 5) ←
    (pure (← Rust_lean_playground.Field.sub lhs rhs));
  let lhs : (RustArray u64 5) ← (pure result);
  lhs

def Rust_lean_playground.Field.negate  (input : (RustArray u64 5))
  : Result (RustArray u64 5)
  := do
  let neg : (RustArray u64 5) ←
    (pure
    (← Rust_lean_playground.Field.reduce
      #v[(← (36028797018963664 : u64) -? (← Core.Ops.Index.Index.index
          input
          (0 : usize))),
        (← (36028797018963952 : u64) -? (← Core.Ops.Index.Index.index
          input
          (1 : usize))),
        (← (36028797018963952 : u64) -? (← Core.Ops.Index.Index.index
          input
          (2 : usize))),
        (← (36028797018963952 : u64) -? (← Core.Ops.Index.Index.index
          input
          (3 : usize))),
        (← (36028797018963952 : u64) -? (← Core.Ops.Index.Index.index
          input
          (4 : usize)))]));
  let input : (RustArray u64 5) ← (pure neg);
  input

def Rust_lean_playground.Field.neg  (input : (RustArray u64 5))
  : Result (RustArray u64 5)
  := do
  let output : (RustArray u64 5) ← (pure input);
  let output : (RustArray u64 5) ←
    (pure (← Rust_lean_playground.Field.negate output));
  output

def Rust_lean_playground.Field.from_bytes.load8_at  (input : (RustSlice u8))
  (i : usize)
  : Result u64
  := do
  (← Rust_primitives.Hax.Machine_int.bitor
    (← Rust_primitives.Hax.Machine_int.bitor
      (← Rust_primitives.Hax.Machine_int.bitor
        (← Rust_primitives.Hax.Machine_int.bitor
          (← Rust_primitives.Hax.Machine_int.bitor
            (← Rust_primitives.Hax.Machine_int.bitor
              (← Rust_primitives.Hax.Machine_int.bitor
                (← Rust_primitives.Hax.cast_op
                  (← Core.Ops.Index.Index.index input i))
                (← Rust_primitives.Hax.Machine_int.shl
                  (← Rust_primitives.Hax.cast_op
                    (← Core.Ops.Index.Index.index input (← i +? (1 : usize))))
                  (8 : i32)))
              (← Rust_primitives.Hax.Machine_int.shl
                (← Rust_primitives.Hax.cast_op
                  (← Core.Ops.Index.Index.index input (← i +? (2 : usize))))
                (16 : i32)))
            (← Rust_primitives.Hax.Machine_int.shl
              (← Rust_primitives.Hax.cast_op
                (← Core.Ops.Index.Index.index input (← i +? (3 : usize))))
              (24 : i32)))
          (← Rust_primitives.Hax.Machine_int.shl
            (← Rust_primitives.Hax.cast_op
              (← Core.Ops.Index.Index.index input (← i +? (4 : usize))))
            (32 : i32)))
        (← Rust_primitives.Hax.Machine_int.shl
          (← Rust_primitives.Hax.cast_op
            (← Core.Ops.Index.Index.index input (← i +? (5 : usize))))
          (40 : i32)))
      (← Rust_primitives.Hax.Machine_int.shl
        (← Rust_primitives.Hax.cast_op
          (← Core.Ops.Index.Index.index input (← i +? (6 : usize))))
        (48 : i32)))
    (← Rust_primitives.Hax.Machine_int.shl
      (← Rust_primitives.Hax.cast_op
        (← Core.Ops.Index.Index.index input (← i +? (7 : usize))))
      (56 : i32)))

def Rust_lean_playground.Field.from_bytes  (bytes : (RustArray u8 32))
  : Result (RustArray u64 5)
  := do
  let low_51_bit_mask : u64 ←
    (pure
    (← (← Rust_primitives.Hax.Machine_int.shl (1 : u64) (51 : i32)) -? (1 :
    u64)));
  #v[(← Rust_primitives.Hax.Machine_int.bitand
      (← Rust_lean_playground.Field.from_bytes.load8_at
        (← Rust_primitives.unsize bytes)
        (0 : usize))
      low_51_bit_mask),
    (← Rust_primitives.Hax.Machine_int.bitand
      (← (← Rust_lean_playground.Field.from_bytes.load8_at
        (← Rust_primitives.unsize bytes)
        (6 : usize)) >>>? (3 : i32))
      low_51_bit_mask),
    (← Rust_primitives.Hax.Machine_int.bitand
      (← (← Rust_lean_playground.Field.from_bytes.load8_at
        (← Rust_primitives.unsize bytes)
        (12 : usize)) >>>? (6 : i32))
      low_51_bit_mask),
    (← Rust_primitives.Hax.Machine_int.bitand
      (← (← Rust_lean_playground.Field.from_bytes.load8_at
        (← Rust_primitives.unsize bytes)
        (19 : usize)) >>>? (1 : i32))
      low_51_bit_mask),
    (← Rust_primitives.Hax.Machine_int.bitand
      (← (← Rust_lean_playground.Field.from_bytes.load8_at
        (← Rust_primitives.unsize bytes)
        (24 : usize)) >>>? (12 : i32))
      low_51_bit_mask)]

def Rust_lean_playground.Field.to_bytes  (input : (RustArray u64 5))
  : Result (RustArray u8 32)
  := do
  let limbs : (RustArray u64 5) ←
    (pure (← Rust_lean_playground.Field.reduce input));
  let q : u64 ←
    (pure
    (← (← (← Core.Ops.Index.Index.index limbs (0 : usize)) +? (19 : u64)) >>>?
    (51 : i32)));
  let q : u64 ←
    (pure
    (← (← (← Core.Ops.Index.Index.index limbs (1 : usize)) +? q) >>>? (51 :
    i32)));
  let q : u64 ←
    (pure
    (← (← (← Core.Ops.Index.Index.index limbs (2 : usize)) +? q) >>>? (51 :
    i32)));
  let q : u64 ←
    (pure
    (← (← (← Core.Ops.Index.Index.index limbs (3 : usize)) +? q) >>>? (51 :
    i32)));
  let q : u64 ←
    (pure
    (← (← (← Core.Ops.Index.Index.index limbs (4 : usize)) +? q) >>>? (51 :
    i32)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (0 : usize)
      (← (← Core.Ops.Index.Index.index limbs (0 : usize)) +? (← (19 : u64) *?
      q))));
  let low_51_bit_mask : u64 ←
    (pure
    (← (← Rust_primitives.Hax.Machine_int.shl (1 : u64) (51 : i32)) -? (1 :
    u64)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (1 : usize)
      (← (← Core.Ops.Index.Index.index limbs (1 : usize)) +?
      (← (← Core.Ops.Index.Index.index limbs (0 : usize)) >>>? (51 : i32)))));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (0 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Core.Ops.Index.Index.index limbs (0 : usize))
        low_51_bit_mask)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (2 : usize)
      (← (← Core.Ops.Index.Index.index limbs (2 : usize)) +?
      (← (← Core.Ops.Index.Index.index limbs (1 : usize)) >>>? (51 : i32)))));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (1 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Core.Ops.Index.Index.index limbs (1 : usize))
        low_51_bit_mask)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (3 : usize)
      (← (← Core.Ops.Index.Index.index limbs (3 : usize)) +?
      (← (← Core.Ops.Index.Index.index limbs (2 : usize)) >>>? (51 : i32)))));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (2 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Core.Ops.Index.Index.index limbs (2 : usize))
        low_51_bit_mask)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (4 : usize)
      (← (← Core.Ops.Index.Index.index limbs (4 : usize)) +?
      (← (← Core.Ops.Index.Index.index limbs (3 : usize)) >>>? (51 : i32)))));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (3 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Core.Ops.Index.Index.index limbs (3 : usize))
        low_51_bit_mask)));
  let limbs : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      limbs
      (4 : usize)
      (← Rust_primitives.Hax.Machine_int.bitand
        (← Core.Ops.Index.Index.index limbs (4 : usize))
        low_51_bit_mask)));
  let s : (RustArray u8 32) ←
    (pure (← Rust_primitives.Hax.repeat (0 : u8) (32 : usize)));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (0 : usize)
      (← Rust_primitives.Hax.cast_op
        (← Core.Ops.Index.Index.index limbs (0 : usize)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (1 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (0 : usize)) >>>? (8 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (2 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (0 : usize)) >>>? (16 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (3 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (0 : usize)) >>>? (24 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (4 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (0 : usize)) >>>? (32 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (5 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (0 : usize)) >>>? (40 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (6 : usize)
      (← Rust_primitives.Hax.cast_op
        (← Rust_primitives.Hax.Machine_int.bitor
          (← (← Core.Ops.Index.Index.index limbs (0 : usize)) >>>? (48 : i32))
          (← Rust_primitives.Hax.Machine_int.shl
            (← Core.Ops.Index.Index.index limbs (1 : usize))
            (3 : i32))))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (7 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (1 : usize)) >>>? (5 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (8 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (1 : usize)) >>>? (13 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (9 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (1 : usize)) >>>? (21 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (10 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (1 : usize)) >>>? (29 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (11 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (1 : usize)) >>>? (37 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (12 : usize)
      (← Rust_primitives.Hax.cast_op
        (← Rust_primitives.Hax.Machine_int.bitor
          (← (← Core.Ops.Index.Index.index limbs (1 : usize)) >>>? (45 : i32))
          (← Rust_primitives.Hax.Machine_int.shl
            (← Core.Ops.Index.Index.index limbs (2 : usize))
            (6 : i32))))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (13 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (2 : usize)) >>>? (2 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (14 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (2 : usize)) >>>? (10 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (15 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (2 : usize)) >>>? (18 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (16 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (2 : usize)) >>>? (26 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (17 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (2 : usize)) >>>? (34 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (18 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (2 : usize)) >>>? (42 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (19 : usize)
      (← Rust_primitives.Hax.cast_op
        (← Rust_primitives.Hax.Machine_int.bitor
          (← (← Core.Ops.Index.Index.index limbs (2 : usize)) >>>? (50 : i32))
          (← Rust_primitives.Hax.Machine_int.shl
            (← Core.Ops.Index.Index.index limbs (3 : usize))
            (1 : i32))))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (20 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (3 : usize)) >>>? (7 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (21 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (3 : usize)) >>>? (15 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (22 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (3 : usize)) >>>? (23 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (23 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (3 : usize)) >>>? (31 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (24 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (3 : usize)) >>>? (39 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (25 : usize)
      (← Rust_primitives.Hax.cast_op
        (← Rust_primitives.Hax.Machine_int.bitor
          (← (← Core.Ops.Index.Index.index limbs (3 : usize)) >>>? (47 : i32))
          (← Rust_primitives.Hax.Machine_int.shl
            (← Core.Ops.Index.Index.index limbs (4 : usize))
            (4 : i32))))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (26 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (4 : usize)) >>>? (4 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (27 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (4 : usize)) >>>? (12 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (28 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (4 : usize)) >>>? (20 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (29 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (4 : usize)) >>>? (28 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (30 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (4 : usize)) >>>? (36 : i32)))));
  let s : (RustArray u8 32) ←
    (pure
    (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (31 : usize)
      (← Rust_primitives.Hax.cast_op
        (← (← Core.Ops.Index.Index.index limbs (4 : usize)) >>>? (44 : i32)))));
  let (_ : Rust_primitives.Hax.Tuple0) ←
    (pure
    if true then
      do
      let (_ : Rust_primitives.Hax.Tuple0) ←
        (pure
        (← Hax_lib.assert
          (← Rust_primitives.Hax.Machine_int.eq
            (← Rust_primitives.Hax.Machine_int.bitand
              (← Core.Ops.Index.Index.index s (31 : usize))
              (128 : u8))
            (0 : u8))));
      Rust_primitives.Hax.Tuple0.mk
    else
      do
      Rust_primitives.Hax.Tuple0.mk);
  s

def Rust_lean_playground.Field.pow2k  (input : (RustArray u64 5)) (k : u32)
  : Result (RustArray u64 5)
  := do
  let (_ : Rust_primitives.Hax.Tuple0) ←
    (pure
    if true then
      do
      let (_ : Rust_primitives.Hax.Tuple0) ←
        (pure
        (← Hax_lib.assert (← Rust_primitives.Hax.Machine_int.gt k (0 : u32))));
      Rust_primitives.Hax.Tuple0.mk
    else
      do
      Rust_primitives.Hax.Tuple0.mk);
  let (a : (RustArray u64 5)) ← (pure input);
  let
    (⟨(a : (RustArray u64 5)), (k : u32)⟩ : (Rust_primitives.Hax.Tuple2
    (RustArray u64 5) u32)) ←
    (pure
    (← Rust_primitives.Hax.failure
      "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/933.
Please upvote or comment this issue if you see this error message.
Unhandled loop kind"
      "{
 (loop {
 |Tuple2(a, k)| {
 {
 let a3_19: int = {
 rust_primitives::hax::machine_int::mul(
 19,
 core::ops::index::f_index(a, 3),
 )
 };
 {
 let a4_19: int = {
 rust_primitives::hax::machine_int::mu..."));
  a

def Rust_lean_playground.Field.pow2k.m  (x : u64) (y : u64)
  : Result TODO_LINE_700
  := do
  (← (← Rust_primitives.Hax.cast_op x) *? (← Rust_primitives.Hax.cast_op y))

def Rust_lean_playground.Field.pow2k.LOW_51_BIT_MASK   : Result u64 := do
  (← (← Rust_primitives.Hax.Machine_int.shl (1 : u64) (51 : i32)) -? (1 : u64))

def Rust_lean_playground.Field.square  (input : (RustArray u64 5))
  : Result (RustArray u64 5)
  := do
  (← Rust_lean_playground.Field.pow2k input (1 : u32))

def Rust_lean_playground.Field.square2  (input : (RustArray u64 5))
  : Result (RustArray u64 5)
  := do
  let square : (RustArray u64 5) ←
    (pure (← Rust_lean_playground.Field.pow2k input (1 : u32)));
  let square : (RustArray u64 5) ←
    (pure
    (← Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (5 : usize)
      (fun (square : (RustArray u64 5)) (_ : usize) =>(do true : Result Bool))
      square
      (fun (square : (RustArray u64 5)) (i : usize) =>(do
          (← Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            square
            i
            (← (← Core.Ops.Index.Index.index square i) *? (2 : u64))) : Result
          (RustArray u64 5)))));
  square

def Rust_lean_playground.ZERO   : Result (RustArray u64 5) := do
  #v[(0 : u64), (0 : u64), (0 : u64), (0 : u64), (0 : u64)]