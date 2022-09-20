/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Array.Basic
import LeanColls.Array.VarArray

namespace LeanColls

structure ArrayBuffer (α) where
  cap : Nat
  h_cap : cap > 0
  size : Nat
  h_size : size ≤ cap
  backing : ArrayUninit α cap size h_size

namespace ArrayBuffer

def empty (_ : Unit) (initCap : Nat := 16) (h_cap : 1 ≤ initCap := by decide) : ArrayBuffer α := ⟨
  initCap,
  h_cap,
  0,
  Nat.zero_le _,
  ArrayUninit.new initCap
  ⟩

@[inline] def full (A : ArrayBuffer α) : Bool := A.size = A.cap

def grow : ArrayBuffer α → ArrayBuffer α :=
λ ⟨cap, h_cap, size, h_size, backing⟩ =>
  let newCap := 2 * cap
  have : cap < newCap := by
    have := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self 1) h_cap
    simp at this ⊢
    assumption
  ⟨newCap, Nat.le_trans h_cap <| Nat.le_of_lt this,
    size,
    Nat.le_trans h_size <| Nat.le_of_lt this,
    backing.resize newCap (Nat.le_trans h_size <| Nat.le_of_lt this)⟩

theorem grow_notfull (A : ArrayBuffer α)
  : ¬A.grow.full
  := by
    simp [full,grow]
    apply (decide_eq_false_iff_not _).mpr
    suffices A.size < 2 * A.cap from
      Nat.ne_of_lt this
    have := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self 1) A.h_cap
    simp at this ⊢
    apply Nat.lt_of_le_of_lt A.h_size
    assumption

@[inline] def push_notfull (A : ArrayBuffer α) (h : ¬A.full) (a : α) : ArrayBuffer α
  :=
    match A with
    | ⟨cap, h_cap, size, h_size, backing⟩ =>
    have h_size : size < cap :=
      Nat.lt_of_le_of_ne h_size <| by simp [full] at h; exact h
    ⟨ cap, h_cap,
      size + 1, h_size,
      backing.push a h_size⟩

def push (A : ArrayBuffer α) (a : α) : ArrayBuffer α :=
  if h:A.size = A.cap then
    A.grow.push_notfull (A.grow_notfull) a
  else
    A.push_notfull (by simp [full,h]) a

def toArray (A : ArrayBuffer α) : Array α A.size :=
  match A with
  | ⟨_, _, size, h_size, backing⟩ =>
  if ArrayUninit.isExclusive A
  then ⟨backing.resize size (Nat.le_refl _)⟩
  else Array.init (n := size) (fun ⟨i,h⟩ =>
    backing.get i (Nat.lt_of_lt_of_le h h_size) h)

instance : Enumerable (VarArray α) α where
  ρ := ArrayBuffer α
  insert A :=
    match A with
    | some ⟨a,A⟩ => A.push a
    | none => ArrayBuffer.empty ()
  fromEnumerator A := ⟨A.size, ⟨A.toArray⟩⟩

def foldl (f : _ → _ → _) (acc : β) (A : ArrayBuffer α) :=
  (Range.mk A.size).foldl' (fun acc i h =>
    f acc (A.backing.get i (Nat.lt_of_lt_of_le h A.h_size) h)
  ) acc

instance : Foldable (ArrayBuffer α) α where
  fold A f acc := A.foldl f acc
