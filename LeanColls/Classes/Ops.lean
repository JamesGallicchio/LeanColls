/- Copyright (c) 2023 James Gallicchio

Authors: James Gallicchio
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

/-! ## Collection operations

This file defines various classes of operations over collections.
- [Fold]: internal iteration
- [Iterate]: external iteration
- [Insert]: empty, insert
- [Size]: some notion of collection size
- [ToFinset]: modeled by finset
- [ToMultiset]: modeled by multiset

TODO: consider adding these?
- [Contains]: decidable membership
- [FilterMap]: conditional map

Related classes which are defined elsewhere but used here:
- [Membership]: Prop-level membership
- [Append]: Disjoint union
- [Functor]: map function
- [Bind]: bind and flatten
- (TODO) whatever the do notation guard class is called

-/

namespace LeanColls

-- TODO: docstrings

/-! ### Models -/

/-- `C` can be modeled as a finset of `τ`s -/
class ToFinset (C : Type u) (τ : outParam (Type v)) where
  toFinset : C → Finset τ

/-- `C` can be modeled as a multiset of `τ`s -/
class ToMultiset (C : Type u) (τ : outParam (Type v)) where
  toMultiset : C → Multiset τ

class LawfulToMultiset (C : Type u) (τ : outParam (Type v))
        [DecidableEq τ] [ToFinset C τ] [ToMultiset C τ] where
  toFinset_toMultiset : ∀ (c : C), (ToMultiset.toMultiset c).toFinset = ToFinset.toFinset c

attribute [simp] LawfulToMultiset.toFinset_toMultiset

instance [DecidableEq τ] [ToMultiset C τ] : ToFinset C τ where
  toFinset c := (ToMultiset.toMultiset c).toFinset

instance [DecidableEq τ] [ToMultiset C τ] : LawfulToMultiset C τ where
  toFinset_toMultiset _ := rfl

class ToList (C : Type u) (τ : outParam (Type v)) where
  toList : C → List τ
export ToList (toList)

class LawfulToList (C : Type u) (τ : outParam (Type v))
        [ToMultiset C τ] [ToList C τ] where
  toMultiset_toList : ∀ (c : C), (toList c) = ToMultiset.toMultiset c

attribute [simp] LawfulToMultiset.toFinset_toMultiset

instance [ToList C τ] : ToMultiset C τ where
  toMultiset c := (toList c)

instance [ToList C τ] : LawfulToList C τ where
  toMultiset_toList _ := rfl



/-! ### Operations Defined Elsewhere -/

namespace Mem
variable (C : Type u) (τ : outParam (Type v)) [Membership τ C]

class ToFinset [ToFinset C τ] : Prop where
  mem_iff_mem_toFinset : ∀ x (c : C),
    x ∈ c ↔ x ∈ ToFinset.toFinset c

class ToMultiset [ToMultiset C τ] : Prop where
  mem_iff_mem_toMultiset : ∀ x (c : C),
    x ∈ c ↔ x ∈ ToMultiset.toMultiset c

class ToList [ToList C τ] : Prop where
  mem_iff_mem_toList : ∀ x (c : C),
    x ∈ c ↔ x ∈ ToList.toList c

end Mem

namespace Append
variable (C : Type u) (τ : outParam (Type v)) [Append C]

class ToList [ToList C τ] : Prop where
  toList_append : ∀ (c1 c2 : C),
    toList (c1 ++ c2) = toList c1 ++ toList c2

end Append



/-! ### Iteration -/

/-- `C` can be folded over, with element type `τ` -/
class Fold (C : Type u) (τ : outParam (Type v)) where
  /-- full (not early-terminating) fold over the elements of `C` -/
  fold : {β : Type w} → C → (β → τ → β) → β → β
  /-- monadic fold over the elements of `C` -/
  foldM : {β : Type w} → {m : Type w → Type w} → [Monad m] →
      C → (β → τ → m β) → β → m β
    := fun c f i => fold c (fun macc x => macc >>= fun acc => f acc x) (pure i)
export Fold (fold foldM)

/-- `C` with element type `τ` can be iterated using type `ρ`

**Note:** This is essentially a combination of Lean core's
[ToStream] and [Stream] classes.
By combining them we can avoid relying on distinct `ρ` types
to associate the `next?` and `iterate` functions.
-/
class Iterate (C : Type u) (τ : outParam (Type v)) (ρ : outParam (Type w)) where
  iterate : C → ρ
  next? : ρ → Option (τ × ρ)
export Iterate (iterate next?)


/-! ### New Operations -/

/-- `C` has an empty collection, and a way to insert `τ`s -/
class Insert (C : Type u) (τ : outParam (Type v)) where
  empty : C
  insert : C → τ → C
  singleton : τ → C := insert empty
export Insert (empty insert singleton)

namespace Insert
variable  (C : Type u) (τ : outParam (Type v)) [Insert C τ]

class Mem [Membership τ C] : Prop where
  mem_empty : ∀ x, ¬ x ∈ empty (C := C)
  mem_insert : ∀ x (c : C) y, x ∈ insert c y ↔ x = y ∨ x ∈ c
  mem_singleton : ∀ x y, x ∈ singleton (C := C) y ↔ x = y

class ToMultiset [ToMultiset C τ] : Prop where
  toMultiset_empty : ToMultiset.toMultiset (empty (C := C)) = {}
  toMultiset_insert : ∀ (c : C) x,
    ToMultiset.toMultiset (insert c x) = Multiset.cons x (ToMultiset.toMultiset c)
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

end Insert


class Size (C : Type u) where
  /-- Number of elements in the collection. -/
  size : C → Nat
export Size (size)

instance (priority := low) Size.ofFold [Fold C τ] : Size C where
  size c := Fold.fold c (fun acc _x => acc+1) 0
