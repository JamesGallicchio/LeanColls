/-
Copyright (c) 2022 James Gallicchio.

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

@[extern "leancolls_array_set"]
def set {α} {n : @& Nat}
        (A : Array α n) (i : @& Fin n) (x : α)
  : Array α n
  := ⟨λ a => if a = i then x  else A.data a⟩

@[extern "leancolls_array_resize"]
def resize {α} {n : @& Nat} (A : Array α n)
          (x : @&α) (m : @& Nat)
  : Array α m
  := ⟨λ i => if h:i < n
    then A.data ⟨i,h⟩
    else x⟩

@[extern "leancolls_array_copy"]
def copy {α} {n : @& Nat} (A : Array α n) : Array α n
  := ⟨λ i => A.data i⟩

unsafe def allInitUnsafe (A : Array (Uninit α) n)
  (h : ∀ i, (A.get i).isInit) : Array α n
  := unsafeCast A
@[implementedBy allInitUnsafe]
def allInit (A : Array (Uninit α) n)
  (h : ∀ i, (A.get i).isInit) : Array α n
  := ⟨λ i => Uninit.getValue (A.get i) (h i)⟩

@[simp]
theorem get_of_set_eq (f : Array α n) (i : Fin n) (x : α) {i' : Fin n} (h_i : i = i')
  : (f.set i x).get i' = x
  := by unfold get; unfold set; simp [h_i, Function.update, cast]

@[simp]
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

instance : Indexed (Array α n) α where
  size _ := n
  nth a i := a.get i

structure COWArray (α n) where
  backing : Array α n

namespace COWArray
variable (A : COWArray α n)

def new (x : α) (n : Nat) := Array.new x n |> COWArray.mk
@[inline] def get : Fin n → α := A.backing.get
@[inline] def set (i : Fin n) (x : α) : COWArray α n :=
  A.backing.copy |>.set i x |> COWArray.mk

@[inline] def update (i : Fin n) (f : α → α) : COWArray α n :=
  A.set i (f <| A.get i)

instance : Foldable (COWArray α n) α where
  fold f acc A := Foldable.fold f acc A.backing

end COWArray