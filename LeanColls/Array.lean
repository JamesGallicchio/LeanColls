/-
Copyright (c) 2021 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes
import LeanColls.Range
import LeanColls.IndexedOps

namespace LeanColls

@[extern "leancolls_array_initialize"] private constant arrayInit : IO Unit

builtin_initialize arrayInit

structure Array (α : Type u) (n : Nat) : Type u where
  data : List α
  h_len : data.length = n

attribute [extern "leancolls_array_to_list"] Array.data
attribute [extern "leancolls_array_of_list"] Array.mk

namespace Array

@[extern "leancolls_array_new"]
private unsafe def newExternal (a : α) (n : USize) : Array α n.toNat
  := ⟨List.replicate n.toNat a, List.length_replicate _ _⟩
private unsafe def newImpl (a : α) (n : @& Nat) : Array α n
  := unsafeCast (newExternal a n.toUSize!)
@[implementedBy newImpl]
def new (a : α) (n : @& Nat) : Array α n
  := ⟨List.replicate n a, List.length_replicate _ _⟩

@[extern "leancolls_array_get"]
private unsafe def getExternal {n : @& Nat} (A : @& Array α n) (i : USize) : α
  := A.data.get (unsafeCast i.toNat)
private unsafe def getImpl {n : @& Nat} (A : @& Array α n) (i : @& Fin n) : α
  := getExternal A i.val.toUSize!
@[implementedBy getImpl]
def get {n : @& Nat} (A : @& Array α n) (i : @& Fin n) : α
  := A.data.get ⟨i, by rw [A.h_len]; exact i.isLt⟩

@[extern "leancolls_array_set"]
private unsafe def setExternal (n : USize) (A : Array α n.toNat) (i : USize) (x : α) : Array α n.toNat
  := ⟨A.data.set i.toNat x, sorry⟩
private unsafe def setImpl {n : @& Nat} (A : Array α n) (i : @& Fin n) (x : α) : Array α n
  := unsafeCast (setExternal n.toUSize! (unsafeCast A) i.val.toUSize! x)
@[implementedBy setImpl]
def set {n : @& Nat} (A : Array α n) (i : @& Fin n) (x : α) : Array α n
  := ⟨A.data.set i.val x, by rw [List.length_set]; exact A.h_len⟩

@[extern "leancolls_array_extend"]
def extend (A : Array α n) (m : @& Nat) (a : α) : Array α (n+m)
  := ⟨A.data ++ List.replicate m a, by simp [List.length_append, A.h_len]⟩

@[extern "leancolls_array_shrink"]
def shrink (A : Array α n) (n' : @& Nat) (h : n' ≤ n) : Array α n'
  := ⟨A.data.take n', by
    simp [List.length_take, A.h_len, min]
    split
    apply Nat.le_antisymm
    assumption
    exact h
    rfl
    ⟩

@[extern "leancolls_array_unwrap_somes"]
def unwrapSomes (A : Array (Option α) n) (h : ∀ i, Option.isSome (A.get i))
  : Array α n
  := ⟨A.data.subtypeByMem.map (λ ⟨x,h'⟩ => x.get (by
      cases A; case mk data h_len _ =>
      unfold get at h
      simp at h_len h' h
      cases h_len
      simp at h_len h'
      cases List.index_of_mem _ _ h'
      case intro i h'' =>
      simp at h''
      rw [←h'']
      exact h i
    )), by
      simp [A.h_len]
    ⟩

theorem get_of_set_eq (f : Array α n) (i : Fin n) (x : α)
  : (f.set i x).get i = x
  := by
    unfold get; unfold set; simp
    exact List.get_of_set_eq _ ⟨i, by rw [f.h_len]; exact i.isLt⟩ x

theorem get_of_set_ne (f : Array α n) (i : Fin n) (x : α) (j : Fin n)
  : i ≠ j → (f.set i x).get j = f.get j
  := by
    unfold get; unfold set
    intro h
    exact List.get_of_set_ne _ i.val x
      ⟨j, by rw [f.h_len]; exact j.isLt⟩
      (by
        simp
        intro h'
        cases i; cases j
        simp at h'
        exact h (by simp [h']))

instance : Indexed (Array α n) α where
  size _ := n
  nth := get

instance : IndexedOps (Array α n) α := default

end Array



structure ArrayBuffer (α) where
  cap : { c : Nat // 1 ≤ c }
  backing : Array (Option α) cap
  size : Nat
  h_size : size ≤ cap
  h_full : ∀ i, (h:i.val < size) → (backing.get i).isSome

namespace ArrayBuffer

def empty : ArrayBuffer α := ⟨
  ⟨1,by decide⟩,
  Array.new none 1,
  0,
  by decide,
  by intro i h; have := Nat.not_lt_zero _ h; contradiction⟩

@[inline] def full (A : ArrayBuffer α) : Bool := A.size = A.cap

def grow : ArrayBuffer α → ArrayBuffer α :=
λ ⟨cap, backing, size, h_size, h_full⟩ =>
  ⟨⟨cap + cap, Nat.le_trans cap.property (Nat.le_add_right _ _)⟩, backing.extend cap none, size,
    Nat.le_trans h_size (Nat.le_add_left _ _),
    by
      intro i h
      have h_icap : i.val < cap := Nat.lt_of_lt_le h h_size
      have := h_full ⟨i.val, h_icap⟩ h
      simp [Array.extend, Array.get] at this ⊢
      simp [List.get_append_left _ _ (by rw [backing.h_len]; exact h_icap)]
      exact this⟩

theorem grow_notfull (A : ArrayBuffer α)
  : ¬A.grow.full
  := by
    simp [full,grow]
    suffices A.1.val < A.1.val + A.1.val by
      simp [Nat.ne_of_lt (Nat.lt_of_le_of_lt A.h_size this)]
    generalize A.cap = x
    cases x; case mk v h_p =>
    simp
    exact Nat.add_le_add_left h_p v

set_option pp.coercions true

@[inline] def push_notfull (A : ArrayBuffer α) (h : ¬A.full) (a : α) : ArrayBuffer α
  :=
    match A with
    | ⟨cap, backing, size, h_size, h_full⟩ =>
    have h_size := Nat.lt_of_le_and_ne h_size (by simp [full] at h; exact h)
    ⟨cap, backing.set ⟨size,h_size⟩ a, size + 1,
    h_size,
    by
      intro i h_i
      cases h_i
      case refl =>
        simp [Array.get_of_set_eq, Option.isSome]
      case step h_i =>
        have : ⟨size,h_size⟩ ≠ i := by
          intro h_contra
          cases h_contra
          simp at h_i
          exact Nat.not_le_of_gt h_i (Nat.le_refl _)
        rw [Array.get_of_set_ne _ _ _ _ this]
        simp at h_i
        exact h_full ⟨i, _⟩ h_i⟩

def push (A : ArrayBuffer α) (a : α) : ArrayBuffer α :=
  if h:A.size = A.cap then
    A.grow.push_notfull (A.grow_notfull) a
  else
    A.push_notfull (by simp [full,h]) a


def toArray (A : ArrayBuffer α) : Array α A.size :=
  (A.backing.shrink A.size A.h_size).unwrapSomes (by
    cases A; case mk cap backing size h_size h_full =>
    intro i
    have := h_full ⟨i.val, Nat.le_trans i.isLt h_size⟩ i.isLt
    unfold Array.shrink.proof_1
    simp [Array.shrink, Array.get]
    sorry
  )

end ArrayBuffer

instance : Enumerable (Σ n, Array α n) α where
  ρ := ArrayBuffer α
  insert A :=
    match A with
    | some ⟨a,A⟩ => A.push a
    | none => ArrayBuffer.empty
  fromEnumerator A := ⟨A.size, A.toArray⟩

instance : Indexed (Array α n) α where
  size _ := n
  nth a i := a.get i

end LeanColls