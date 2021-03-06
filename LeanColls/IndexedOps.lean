/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes
import LeanColls.Range
import LeanColls.View

namespace LeanColls

namespace IndexedOps

instance [Indexed C τ] : Foldable C τ where
  fold f init c :=
    Range.fold' ⟨Size.size c⟩ (λ acc i h =>
      f acc (Indexed.nth c ⟨i,h⟩)
    ) init

structure Slice (C) (τ : outParam (Type u)) [Indexed C τ] where
  c : C
  off : Nat
  len : Nat
  h_range : off + len ≤ Size.size c

instance [Indexed C τ] : Indexed (Slice C τ) τ where
  size S := S.len
  nth S (i : Fin S.len) := Indexed.nth S.c ⟨S.off + i, Nat.le_trans (Nat.add_lt_add_left i.isLt _) (Slice.h_range S)⟩

def IndexedEq [DecidableEq τ] [Indexed C₁ τ] [Indexed C₂ τ] (c₁ : C₁) (c₂ : C₂)
  {h : Size.size c₁ = Size.size c₂} : Prop :=
  ∀ i, Indexed.nth c₁ i = Indexed.nth c₂ ⟨i.val, by rw [←h]; exact i.isLt⟩

end IndexedOps

class IndexedOps (C τ) [Indexed C τ] where
  slice (off len : Nat) (c : C)
    {h : off + len ≤ Size.size c} : IndexedOps.Slice C τ

namespace IndexedOps

instance [Indexed C τ] : Inhabited (IndexedOps C τ) where
  default := {
    slice := λ off len c h => ⟨c,off,len,h⟩
  }

instance [Indexed C τ] : MapLike C Nat τ where
  fold f acc c :=
    Range.fold' ⟨Size.size c⟩ (λ acc i h_i =>
      f acc (i, Indexed.nth c ⟨i,h_i⟩)
    ) acc
  get? c i :=
    if h : i < Size.size c then
      some (Indexed.nth c ⟨i, h⟩)
    else none

end IndexedOps

end LeanColls
