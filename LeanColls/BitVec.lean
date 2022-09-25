/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.AuxLemmas

namespace LeanColls

/-! # Bit vectors

Bit 0 is the least significant bit.
-/
def BitVec (size) :=  Fin (2^size)

namespace BitVec

def get (bv : BitVec n) (i : Fin n) : Bool :=
  (bv.val >>> i.val) % 2 == 1

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
  rw [(by assumption : _ >>> _ = 0)]
  simp

theorem get_empty (n i)
  : get (empty n) i = false
  := by
  match i with
  | ⟨i,h_i⟩ =>
  simp [empty,get]
  simp [zero_shiftRight]

def toString (bv : BitVec n) :=
  String.leftpad n '0' (String.mk (Nat.toDigits 2 bv.val))

instance : ToString (BitVec n) := ⟨toString⟩

instance : DecidableEq (BitVec n) :=
  cast (by simp [BitVec]) (inferInstance : DecidableEq (Fin (2^n)))

instance : Inhabited (BitVec n) := ⟨empty n⟩

end BitVec
