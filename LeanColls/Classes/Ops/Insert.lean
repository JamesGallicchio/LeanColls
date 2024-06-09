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

class AgreesWithToSet [ToSet C τ] : Prop where
  toSet_empty : toSet (empty (C := C)) = ∅
  toSet_insert : ∀ (cont : C) x, toSet (insert cont x) = {x} ∪ toSet cont
  toSet_singleton : ∀ x, toSet (singleton (C := C) x) = {x}

export AgreesWithToSet (
  toSet_empty
  toSet_insert
  toSet_singleton)

attribute [simp] toSet_empty toSet_insert toSet_singleton

class AgreesWithToMultiset [ToMultiset C τ] : Prop where
  toMultiset_empty : toMultiset (empty (C := C)) = 0
  toMultiset_insert : ∀ (cont : C) x,
    toMultiset (insert cont x) = x ::ₘ toMultiset cont
  toMultiset_singleton : ∀ x,
    toMultiset (singleton (C := C) x) = {x}

export AgreesWithToMultiset (
  toMultiset_empty
  toMultiset_insert
  toMultiset_singleton)

attribute [simp] toMultiset_empty toMultiset_insert toMultiset_singleton

instance [ToMultiset C τ] [AgreesWithToMultiset C τ] : AgreesWithToSet C τ where
  toSet_empty := by
    simp [toSet, toMultiset_empty]; rfl
  toSet_insert := by
    intro c x
    simp [toSet, toMultiset_insert]; rfl
  toSet_singleton := by
    intro x
    simp [toSet, toMultiset_singleton]; rfl

@[simp] theorem toList_empty [ToList C τ] [AgreesWithToMultiset C τ]
  : toList (empty (C := C)) = [] := by
  rw [← List.isEmpty_iff_eq_nil
    , ← Multiset.coe_eq_zero_iff_isEmpty]
  simp [toMultiset_empty]

@[simp] theorem toList_singleton [ToList C τ] [AgreesWithToMultiset C τ]
  : toList (singleton (C := C) x) = [x] := by
  apply Multiset.coe_eq_singleton.mp
  simp [toMultiset_singleton]

def into (C' : Type u) {τ} [Insert C' τ] {C} [Fold C τ] (c : C) : C' :=
  fold c insert empty

end Insert

export Insert (into)

namespace Insert

@[simp]
theorem toMultiset_into_eq [ToMultiset C τ] [ToMultiset C' τ]
    [Fold C τ] [Fold.AgreesWithToMultiset C τ]
    [Insert C' τ] [AgreesWithToMultiset C' τ]
    (c : C)
  : toMultiset (into C' c) = toMultiset c := by
  unfold into
  apply Fold.multisetInduction c (motive := fun m acc => toMultiset acc = m)
  · simp [toMultiset_empty]
  · rintro _ _ _ _ _ rfl
    simp [toMultiset_insert]

@[simp]
theorem mem_into_iff
    [Fold C τ] [ToMultiset C τ] [Fold.AgreesWithToMultiset C τ]
    [Insert C' τ] [ToSet C' τ] [AgreesWithToSet C' τ]
    [Membership τ C'] [Membership.AgreesWithToSet C' τ]
    [Membership τ C] [Membership.AgreesWithToSet C τ]
    (c : C)
  : x ∈ into C' c ↔ x ∈ c := by
  unfold into
  conv => rhs; rw [←Membership.mem_toMultiset_iff_mem]
  apply Fold.multisetInduction c (motive := fun m acc => x ∈ acc ↔ x ∈ m)
  · rw [Membership.AgreesWithToSet.mem_iff_mem_toSet, toSet_empty]
    simp
  · rintro _ _ _ _ _ h
    rw [Membership.AgreesWithToSet.mem_iff_mem_toSet, toSet_insert]
    simp [toMultiset_insert]
    rw [h]
