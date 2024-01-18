/-
Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Seq
import LeanColls.Data.Array

namespace LeanColls

/-! # Bit Vectors

Implemented as a byte array.
-/
structure BitVec (size : Nat) where
  data : ByteArray
  hsize : data.size*8 ≥ size

namespace BitVec

def get (bv : BitVec n) (i : Fin n) : Bool :=
  let div := i.val / 8
  let mod := (i.val % 8).toUInt8
  have : div < bv.data.size := by sorry
  let byte := Seq.get bv.data ⟨i.val / 8, this⟩
  (byte.land (UInt8.shiftLeft 1 mod)) != 0

def set (bv : BitVec n) (i : Fin n) (x : Bool) : BitVec n :=
  match bv, i with
  | ⟨data, h_data⟩, ⟨i, h_i⟩ =>
    if x then
      -- Set bit i to 1
      ⟨data ||| (1 <<< i), sorry⟩
    else
      -- Set bit i to 0
      ⟨data &&& ((1 <<< n) - 1 - (1 <<< i)), sorry⟩

def flip (bv : BitVec n) (i : Fin n) : BitVec n :=
  bv.set i (not <| bv.get i)

def empty (n : Nat) : BitVec n := ⟨0, Nat.pos_pow_of_pos _ (by decide)⟩

instance : OfNat (BitVec n) 0 := ⟨empty n⟩

@[simp]
theorem shiftLeft_bitwiseOr (a b i : Nat)
  : (a ||| b) >>> i = (a >>> i) ||| (b >>> i)
  := by sorry

@[simp]
theorem shiftRight_shiftLeft (i j)
  : 2^i >>> j = if j > i then 0 else 2^(i-j)
  := by sorry


theorem get_set (bv : BitVec n) (i x) (j : Fin n)
  : get (set bv i x) j = if i = j then x else get bv j
  := by
  simp [get, set]
  split <;> split <;> (subst_vars; simp)
  repeat sorry

theorem shiftRight_zero (n i : Nat)
  : n >>> (i+1) = n >>> i / 2
  := by simp [HShiftRight.hShiftRight, ShiftRight.shiftRight, Nat.shiftRight]

theorem shiftRight_succ (n i : Nat)
  : n >>> (i+1) = n >>> i / 2
  := by simp [HShiftRight.hShiftRight, ShiftRight.shiftRight, Nat.shiftRight]

theorem zero_shiftRight (i : Nat) : 0 >>> i = 0
  := by
  induction i <;> simp [shiftRight_zero, shiftRight_succ]

theorem get_empty (n i)
  : get (empty n) i = false
  := by
  match i with
  | ⟨i,h_i⟩ =>
  simp [empty,get]

def toString (bv : BitVec n) :=
  String.leftpad n '0' (String.mk (Nat.toDigits 2 bv.val))

instance : ToString (BitVec n) := ⟨toString⟩

instance : DecidableEq (BitVec n) :=
  cast (by simp [BitVec]) (inferInstance : DecidableEq (Fin (2^n)))

instance : Inhabited (BitVec n) := ⟨empty n⟩
