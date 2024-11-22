/- Copyright (c) 2024 James Gallicchio

Authors: James Gallicchio
-/

import LeanColls.Classes.Ops
import LeanColls.Classes.Ops.Fold

namespace LeanColls.Insert

instance [_root_.Insert τ C] [EmptyCollection C] : Insert C τ where
  empty := EmptyCollection.emptyCollection
  insert c x := _root_.Insert.insert x c

variable  (C : Type u) (τ : outParam (Type v)) [Insert C τ]

class Mem [Membership τ C] : Prop where
  mem_empty : ∀ x, ¬ x ∈ empty (C := C)
  mem_insert : ∀ x (cont : C) y, x ∈ insert cont y ↔ x = y ∨ x ∈ cont
  mem_singleton : ∀ x y, x ∈ singleton (C := C) y ↔ x = y

class ToMultiset [ToMultiset C τ] : Prop where
  toMultiset_empty : ToMultiset.toMultiset (empty (C := C)) = {}
  toMultiset_insert : ∀ (cont : C) x,
    ToMultiset.toMultiset (insert cont x) = Multiset.cons x (ToMultiset.toMultiset cont)
  toMultiset_singleton : ∀ x,
    ToMultiset.toMultiset (singleton (C := C) x) = {x}

instance [Membership τ C] [LeanColls.ToMultiset C τ] [ToMultiset C τ] [Mem.ToMultiset C τ] : Mem C τ where
  mem_empty := by
    intro x
    simp [Mem.ToMultiset.mem_iff_mem_toMultiset, ToMultiset.toMultiset_empty]
  mem_insert := by
    intro x c y
    simp [Mem.ToMultiset.mem_iff_mem_toMultiset, ToMultiset.toMultiset_insert]
  mem_singleton := by
    intro x
    simp [Mem.ToMultiset.mem_iff_mem_toMultiset, ToMultiset.toMultiset_singleton]

@[simp] theorem toList_empty [Membership τ C] [Mem C τ] [ToList C τ] [Mem.ToList C τ]
  : toList (empty (C := C)) = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro x
  rw [← Mem.ToList.mem_iff_mem_toList]
  apply Mem.mem_empty

@[simp] theorem toList_singleton [ToList C τ] [LeanColls.ToMultiset C τ] [LawfulToList C τ] [ToMultiset C τ]
  : toList (singleton (C := C) x) = [x] := by
  apply Multiset.coe_eq_singleton.mp
  rw [LawfulToList.toMultiset_toList]
  rw [ToMultiset.toMultiset_singleton]

def into (C' : Type u) {τ} [Insert C' τ] {C} [Fold C τ] (c : C) : C' :=
  fold c insert empty

end Insert

export Insert (into)

namespace Insert

@[simp]
theorem mem_into_iff [Insert C' τ] [Membership τ C'] [Mem C' τ]
    [Fold C τ] [Membership τ C] [ToList C τ] [Fold.ToList C τ] [Mem.ToList C τ]
    (c : C)
  : x ∈ into C' c ↔ x ∈ c := by
  unfold into
  have ⟨L, perm, h⟩ := Fold.ToList.fold_eq_fold_toList (τ := τ) c
  conv at h => ext; ext; ext; rw [← List.foldr_reverse]
  replace perm := (List.reverse_perm ..).trans perm
  generalize L.reverse = L' at perm h; clear L
  conv => lhs; rw [h]
  clear h
  conv => rhs; rw [Mem.ToList.mem_iff_mem_toList, ← perm.mem_iff]
  clear perm
  induction L' with
  | nil =>
    simp [Mem.mem_empty]
  | cons hd tl ih =>
    simp [Mem.mem_insert, ih]
