/-
Copyright (c) 2021 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes
import LeanColls.Range
import LeanColls.IndexedOps
import LeanColls.Uninit
import LeanColls.AuxLemmas

namespace LeanColls

@[extern "leancolls_array_initialize"] private constant arrayInit : IO Unit

builtin_initialize arrayInit

structure Array (α : Type u) (n : Nat) : Type u where
  data : (i : Fin n) → α

namespace Array

@[extern "leancolls_array_new"]
def new (x : @&α) (n : @& Nat) : Array α n
  := ⟨λ _ => x⟩

@[extern "leancolls_array_get"]
def get {α} {n : @& Nat}
        (A : @& Array α n) (i : @& Fin n) : α
  := A.data i

@[inline, extern "leancolls_array_set"]
def set {α} {n : @& Nat}
        (A : Array α n) (i : @& Fin n) (x : α)
  : Array α n
  := ⟨λ a => if a = i then x  else A.data a⟩

@[inline, extern "leancolls_array_resize"]
def resize {α} {n : @& Nat} (A : Array α n)
          (x : @&α) (m : @& Nat)
  : Array α m
  := ⟨λ i => if h:i < n
    then A.data ⟨i,h⟩
    else x⟩

unsafe def allInitUnsafe (A : Array (Uninit α) n)
  (h : ∀ i, (A.get i).isInit) : Array α n
  := unsafeCast A
@[implementedBy allInitUnsafe]
def allInit (A : Array (Uninit α) n)
  (h : ∀ i, (A.get i).isInit) : Array α n
  := ⟨λ i => Uninit.getValue (A.get i) (h i)⟩

theorem get_of_set_eq (f : Array α n) (i : Fin n) (x : α) {i' : Fin n} (h_i : i = i')
  : (f.set i x).get i' = x
  := by unfold get; unfold set; simp [h_i, Function.update, cast]

theorem get_of_set_ne (f : Array α n) (i : Fin n) (x : α) (j : Fin n) (h : i ≠ j)
  : (f.set i x).get j = f.get j
  := by
    unfold get; unfold set
    simp [Function.update]
    split
    exact False.elim $ h (by apply Eq.symm; assumption)
    rfl

instance : Indexed (Array α n) α where
  size _ := n
  nth := Array.get

instance : IndexedOps (Array α n) α := default

end Array


structure ArrayBuffer (α) where
  cap : Nat
  h_cap : 1 ≤ cap
  size : Fin cap.succ
  backing : Array (Uninit α) cap
  h_filled : ∀ i, (h : i < size.val) →
    backing.get ⟨i, Nat.lt_of_lt_le h <| Nat.le_of_succ_le_succ size.isLt⟩
    |>.isInit

namespace ArrayBuffer

def empty (_ : Unit) : ArrayBuffer α := ⟨
  16,
  by decide,
  0,
  Array.new (Uninit.uninit) 16,
  by intro i h; contradiction
  ⟩

@[inline] def full (A : ArrayBuffer α) : Bool := A.size = A.cap

def grow : ArrayBuffer α → ArrayBuffer α :=
λ ⟨cap, h_cap, size, backing, h_backing⟩ =>
  let newCap := 2 * cap
  have : cap < newCap := by
    have := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self 1) h_cap
    simp at this ⊢
    assumption
  ⟨newCap, Nat.le_trans h_cap <| Nat.le_of_lt this,
    ⟨size, Nat.lt_trans size.isLt $ Nat.succ_lt_succ this⟩,
    backing.resize (Uninit.uninit) newCap,
    by
      intro i h
      simp at h
      have : i < cap := Nat.lt_of_lt_le h (Nat.le_of_succ_le_succ size.isLt)
      simp [Array.get, Array.resize, this]
      apply h_backing
      assumption
      ⟩

theorem grow_notfull (A : ArrayBuffer α)
  : ¬A.grow.full
  := by
    simp [full,grow]
    suffices A.size.val < 2 * A.cap by
      simp [Nat.ne_of_lt this]
    have := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self 1) A.h_cap
    simp at this ⊢
    apply Nat.lt_of_le_of_lt (Nat.le_of_succ_le_succ A.size.isLt)
    assumption

set_option pp.coercions true

@[inline] def push_notfull (A : ArrayBuffer α) (h : ¬A.full) (a : α) : ArrayBuffer α
  :=
    match A with
    | ⟨cap, h_cap, size, backing, h_backing⟩ =>
    have h_size :=
      Nat.le_of_lt_succ $
      Nat.lt_of_le_and_ne size.isLt (by
      simp [full] at h; intro h'; apply h; injection h'; assumption)
    ⟨ cap, h_cap, ⟨size.val + 1, Nat.succ_le_succ h_size⟩,
      backing.set ⟨size,h_size⟩ (Uninit.init a),
      by
        intro i h_i
        cases size; case mk size _ =>
        by_cases h : i = size
        cases h
        rw [backing.get_of_set_eq]
        exact Uninit.isInit_init
        simp [Fin.eq_of_val_eq]
        rw [backing.get_of_set_ne _ _ _ (by simp; exact h ∘ Eq.symm)]
        have h_i : i < size := Nat.lt_of_le_and_ne (Nat.le_of_succ_le_succ h_i) h
        exact h_backing i h_i⟩

def push (A : ArrayBuffer α) (a : α) : ArrayBuffer α :=
  if h:A.size = A.cap then
    A.grow.push_notfull (A.grow_notfull) a
  else
    A.push_notfull (by simp [full,h]) a


def toArray (A : ArrayBuffer α) : Array α A.size :=
  A.backing.resize (unreachable!) A.size
  |>.allInit <| by
    intro ⟨i,h_i⟩
    have : i < A.cap := Nat.lt_of_lt_le h_i <| Nat.le_of_succ_le_succ A.size.isLt
    simp [Array.resize, Array.get, this]
    exact A.h_filled _ h_i

end ArrayBuffer

instance : Enumerable (Σ n, Array α n) α where
  ρ := ArrayBuffer α
  insert A :=
    match A with
    | some ⟨a,A⟩ => A.push a
    | none => ArrayBuffer.empty ()
  fromEnumerator A := ⟨A.size, A.toArray⟩

instance : Indexed (Array α n) α where
  size _ := n
  nth a i := a.get i

end LeanColls