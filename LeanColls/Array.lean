/-
Copyright (c) 2021 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes
import LeanColls.Range
import LeanColls.IndexedOps
import LeanColls.AuxLemmas

namespace LeanColls

@[extern "leancolls_array_initialize"] private constant arrayInit : IO Unit

builtin_initialize arrayInit

structure Array (n : Nat) (α : Fin n → Type u) : Type u where
  data : (i : Fin n) → α i

namespace Array

@[extern "leancolls_array_new"]
def new.{u} (n : @& Nat) : Array n (λ _ => PUnit.{u+1})
  := ⟨λ _ => PUnit.unit⟩

@[extern "leancolls_array_get"]
def get {n : @& Nat} {α : Fin n → Type u}
        (A : @& Array n α) (i : @& Fin n) : α i
  := A.data i

@[extern "leancolls_array_set"]
def set {n : @& Nat} {α : Fin n → Type u}
        (A : Array n α) (i : @& Fin n) (x : α')
  : Array n (Function.update α i α')
  := ⟨λ a => if h:a = i
      then cast (by simp [h]) x
      else cast (by simp [h]) (A.data a)⟩

@[extern "leancolls_array_resize"]
def resize {n : @& Nat} {α : Fin n → Type u}
          (A : Array n α) (m : @& Nat)
  : Array m (λ i : Fin m => if h:i < n then α ⟨i,h⟩ else PUnit)
  := ⟨λ i =>
    if h:i < n
    then cast (by simp [h]) (A.data ⟨i,h⟩)
    else cast (by simp [h]) PUnit.unit⟩

theorem get_of_set_eq (f : Array n α) (i : Fin n) (x : α')
  : (f.set i x).get i = cast (by simp) x
  := by unfold get; unfold set; simp [Function.update, cast]

theorem get_of_set_ne (f : Array n α) (i : Fin n) (x : α') (j : Fin n) (h : i ≠ j)
  : (f.set i x).get j = cast (by simp [h.symm]) (f.get j)
  := by
    unfold get; unfold set
    simp [Function.update]
    split
    exact False.elim $ h (by apply Eq.symm; assumption)
    rfl

end Array

def Array' (α n) := Array n (λ _ => α)

namespace Array'

instance : Indexed (Array' α n) α where
  size _ := n
  nth := Array.get

instance : IndexedOps (Array' α n) α := default

end Array'


structure ArrayBuffer (α) where
  cap : Nat
  h_cap : 1 ≤ cap
  size : Fin cap.succ
  backing : Array cap (λ i => if i < size.val then α else PUnit)

namespace ArrayBuffer

def empty (_ : Unit) : ArrayBuffer α := ⟨
  16,
  by decide,
  0,
  cast (by
    simp; apply congrArg; apply funext; intro; split
    apply False.elim; apply Nat.not_lt_zero; assumption
    rfl)
    (Array.new 16)
  ⟩

@[inline] def full (A : ArrayBuffer α) : Bool := A.size = A.cap

def grow : ArrayBuffer α → ArrayBuffer α :=
λ ⟨cap, h_cap, size, backing⟩ =>
  let newCap := 2 * cap
  have : cap < newCap := by
    have := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self 1) h_cap
    simp at this ⊢
    assumption
  ⟨newCap, Nat.le_trans h_cap $ Nat.le_of_lt this,
    ⟨size, Nat.lt_trans size.isLt $ Nat.succ_lt_succ this⟩,
    cast (by
      apply congrArg; apply funext; intro; simp
      split <;> split
      rfl; rfl
      case h.h.inr.inl x h h' =>
        apply False.elim; apply h
        apply Nat.lt_of_lt_le h'
        apply Nat.le_of_succ_le_succ
        exact size.isLt
      rfl
      ) $ backing.resize newCap⟩

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
    | ⟨cap, h_cap, size, backing⟩ =>
    have h_size :=
      Nat.le_of_lt_succ $
      Nat.lt_of_le_and_ne size.isLt (by
      simp [full] at h; intro h'; apply h; injection h'; assumption)
    ⟨cap, h_cap, ⟨size.val + 1, Nat.succ_le_succ h_size⟩, cast (by
      apply congrArg; simp; apply funext; intro x; split
      case _ h =>
        simp [h, Nat.lt_succ_self size.val]
      case _ h =>
      split
      case _ h' =>
        simp [Nat.lt_succ_of_le $ Nat.le_of_lt h']
      case _ h' =>
      simp [h']
      split
      case inl h'' =>
        apply False.elim
        apply h'
        apply Nat.lt_of_le_and_ne
        exact Nat.le_of_succ_le_succ h''
        intro h_contra
        apply h
        apply Fin.eq_of_val_eq
        assumption
      rfl
      ) $ backing.set ⟨size,h_size⟩ a⟩

def push (A : ArrayBuffer α) (a : α) : ArrayBuffer α :=
  if h:A.size = A.cap then
    A.grow.push_notfull (A.grow_notfull) a
  else
    A.push_notfull (by simp [full,h]) a


def toArray (A : ArrayBuffer α) : Array' α A.size :=
  cast (by
    cases A; case mk cap h_cap size backing =>
    simp
    apply congrArg; apply funext
    intro i
    have h_isize : i.val < size.val := i.isLt
    have h_icap : i.val < cap := Nat.lt_of_lt_le h_isize (Nat.le_of_succ_le_succ size.isLt)
    simp [h_isize, h_icap]
  ) (A.backing.resize A.size)

end ArrayBuffer

instance : Enumerable (Σ n, Array' α n) α where
  ρ := ArrayBuffer α
  insert A :=
    match A with
    | some ⟨a,A⟩ => A.push a
    | none => ArrayBuffer.empty ()
  fromEnumerator A := ⟨A.size, A.toArray⟩

instance : Indexed (Array' α n) α where
  size _ := n
  nth a i := a.get i

end LeanColls