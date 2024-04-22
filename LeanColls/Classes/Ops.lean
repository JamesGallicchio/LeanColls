/- Copyright (c) 2023 James Gallicchio

Authors: James Gallicchio
-/

import LeanColls.MathlibUpstream
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum

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

/-- `C` can be modeled as a set of `τ`s -/
class ToSet (C : Type u) (τ : outParam (Type v)) where
  toSet : (cont : C) → Set τ
export ToSet (toSet)

/-- `C` can be modeled as a finset of `τ`s -/
class ToFinset (C : Type u) (τ : outParam (Type v)) where
  toFinset : (cont : C) → Finset τ
export ToFinset (toFinset)

/-- `C` can be modeled as a multiset of `τ`s -/
class ToMultiset (C : Type u) (τ : outParam (Type v)) where
  toMultiset : (cont : C) → Multiset τ
export ToMultiset (toMultiset)

/-- `C` can be modeled as a list of `τ`s -/
class ToList (C : Type u) (τ : outParam (Type v)) where
  toList : (cont : C) → List τ
export ToList (toList)

/-! #### Hierarchical Instances

More specific models give a trivial default instance
of the less specific model.
-/

instance [ToFinset C τ] : ToSet C τ where
  toSet c := toFinset c

instance [DecidableEq τ] [ToMultiset C τ] : ToFinset C τ where
  toFinset c := (toMultiset c).toFinset

instance (priority := default + 1) [ToMultiset C τ] : ToSet C τ where
  toSet c := (· ∈ toMultiset c)

instance [ToList C τ] : ToMultiset C τ where
  toMultiset c := (toList c)

/-! #### Lemmas -/

namespace ToSet

@[inline]
def instProd [ToSet C₁ τ₁] [ToSet C₂ τ₂] : ToSet (C₁ × C₂) (τ₁ × τ₂) where
  toSet := fun (c1,c2) => toSet c1 ×ˢ toSet c2

@[inline]
def instSum [ToSet C₁ τ₁] [ToSet C₂ τ₂] : ToSet (C₁ × C₂) (τ₁ ⊕ τ₂) where
  toSet := fun (c1,c2) =>
    ((toSet c1).image Sum.inl) ∪ ((toSet c2).image Sum.inr)

@[inline]
def instMap [ToSet C₁ τ₁] (fC : C₂ → C₁) (ft : τ₁ → τ₂) : ToSet C₂ τ₂ where
  toSet c2 := toSet (fC c2) |>.image ft

end ToSet

namespace ToFinset

@[simp]
theorem toSet_toFinset [ToFinset C τ] (c : C) : (toFinset c).toSet = toSet c := rfl

@[inline]
def instProd [ToFinset C₁ τ₁] [ToFinset C₂ τ₂] : ToFinset (C₁ × C₂) (τ₁ × τ₂) where
  toFinset := fun (c1,c2) => toFinset c1 ×ˢ toFinset c2

@[inline]
def instSum [ToFinset C₁ τ₁] [ToFinset C₂ τ₂] : ToFinset (C₁ × C₂) (τ₁ ⊕ τ₂) where
  toFinset := fun (c1,c2) =>
    Finset.disjSum (toFinset c1) (toFinset c2)

@[inline]
def instMap [ToFinset C₁ τ₁] (fC : C₂ → C₁) (ft : τ₁ ↪ τ₂) : ToFinset C₂ τ₂ where
  toFinset c2 := toFinset (fC c2) |>.map ft

end ToFinset

namespace ToMultiset

@[simp]
theorem toFinset_toMultiset [DecidableEq τ] [ToMultiset C τ] (c : C)
  : (toMultiset c).toFinset = toFinset c := rfl

@[inline]
def instProd [ToMultiset C₁ τ₁] [ToMultiset C₂ τ₂] : ToMultiset (C₁ × C₂) (τ₁ × τ₂) where
  toMultiset := fun (c1,c2) => toMultiset c1 ×ˢ toMultiset c2

@[inline]
def instSum [ToMultiset C₁ τ₁] [ToMultiset C₂ τ₂] : ToMultiset (C₁ × C₂) (τ₁ ⊕ τ₂) where
  toMultiset := fun (c1,c2) =>
    (toMultiset c1).map Sum.inl + (toMultiset c2).map Sum.inr

@[inline]
def instMap [ToMultiset C₁ τ₁] (fC : C₂ → C₁) (ft : τ₁ → τ₂) : ToMultiset C₂ τ₂ where
  toMultiset c2 := toMultiset (fC c2) |>.map ft

end ToMultiset

namespace ToList

@[simp]
theorem toMultiset_toList [ToList C τ] (c : C)
  : Multiset.ofList (toList c) = toMultiset c := rfl

@[simp]
theorem toFinset_toList [ToList C τ] [DecidableEq τ] (c : C)
  : (toList c).toFinset = toFinset c := rfl

@[inline]
def instProd [ToList C₁ τ₁] [ToList C₂ τ₂] : ToList (C₁ × C₂) (τ₁ × τ₂) where
  toList := fun (c1,c2) => toList c1 ×ˢ toList c2

@[simp]
theorem instProd.toToMultiset_eq_toMultiset_prod [ToList C₁ τ₁] [ToList C₂ τ₂] (c1 : C₁) (c2 : C₂)
  : ↑(toList c1 ×ˢ toList c2) = toMultiset c1 ×ˢ toMultiset c2 := by
  simp only [instToMultiset]
  rw [Multiset.coe_product]

@[inline]
def instSum [ToList C₁ τ₁] [ToList C₂ τ₂] : ToList (C₁ × C₂) (τ₁ ⊕ τ₂) where
  toList := fun (c1,c2) =>
    (toList c1).map Sum.inl ++ (toList c2).map Sum.inr

@[inline]
def instMap [ToList C₁ τ₁] (fC : C₂ → C₁) (ft : τ₁ → τ₂) : ToList C₂ τ₂ where
  toList c2 := toList (fC c2) |>.map ft

end ToList


/-! ### Operations Defined Elsewhere -/

namespace Membership

/-- Correctness of `Membership` against the `ToSet` model. -/
class AgreesWithToSet (C : Type u) (τ : outParam (Type v)) [Membership τ C] [ToSet C τ] : Prop where
  mem_iff_mem_toSet : ∀ x (cont : C), x ∈ cont ↔ x ∈ toSet cont
export AgreesWithToSet (mem_iff_mem_toSet)

variable {C τ} [Membership τ C]

/-!
Simp normal form for membership is `x ∈ c` with the smallest expression `c`.
-/

@[simp] theorem mem_toSet_iff_mem (c : C) [ToSet C τ] [AgreesWithToSet C τ]
  : x ∈ toSet c ↔ x ∈ c := by
  simp [mem_iff_mem_toSet]

@[simp] theorem mem_toFinset_iff_mem (c : C) [ToFinset C τ] [AgreesWithToSet C τ]
  : x ∈ toFinset c ↔ x ∈ c := by
  simp [← Finset.mem_coe]

@[simp] theorem mem_toMultiset_iff_mem (c : C) [ToMultiset C τ] [AgreesWithToSet C τ]
  : x ∈ toMultiset c ↔ x ∈ c := by
  simp [mem_iff_mem_toSet, instToSet_1]
  rfl

@[simp] theorem mem_toList_iff_mem (c : C) [ToList C τ] [AgreesWithToSet C τ]
  : x ∈ toList c ↔ x ∈ c := by
  conv => rhs; rw [mem_iff_mem_toSet]

/-! Different simp normal form would be to reduce membership to membership
in the base model for the collection.

TODO: how to handle this?
-/

theorem mem_toSet_iff_mem_toFinset [ToFinset C τ] (x : τ) (c : C) :
    x ∈ toSet c ↔ x ∈ toFinset c := by rfl

theorem mem_toSet_iff_mem_toMultiset [ToMultiset C τ] (x : τ) (c : C) :
    x ∈ toSet c ↔ x ∈ toMultiset c := by rfl

theorem mem_toFinset_iff_mem_toMultiset [ToMultiset C τ] [DecidableEq τ] (x : τ) (c : C) :
    x ∈ toFinset c ↔ x ∈ toMultiset c := by
  simp only [instToFinset, Multiset.mem_toFinset]

theorem mem_toMultiset_iff_mem_toList [ToList C τ] (x : τ) (c : C) :
    x ∈ toMultiset c ↔ x ∈ toList c := by
  simp only [instToMultiset]; rw [Multiset.mem_coe]

end Membership

namespace Append
variable (C : Type u) (τ : outParam (Type v)) [Append C]

class AgreesWithToList [ToList C τ] : Prop where
  toList_append : ∀ (c1 c2 : C),
    toList (c1 ++ c2) = toList c1 ++ toList c2
export AgreesWithToList (toList_append)

attribute [simp] toList_append

end Append

namespace Functor
variable (C : Type u → Type v) [Functor C] (τ τ')

class ToList [ToList (C τ) τ] [ToList (C τ') τ'] : Prop where
  toList_map : ∀ (c : C τ) (f : τ → τ'),
    toList (Functor.map f c) = Functor.map f (toList c)

attribute [simp] ToList.toList_map

end Functor


/-! ### Iteration -/

/-- `C` can be folded over, with element type `τ` -/
class Fold (C : Type u) (τ : outParam (Type v)) where
  /-- full (not early-terminating) fold over the elements of `C` -/
  fold : {β : Type w} → (cont : C) → (β → τ → β) → β → β
  /-- monadic fold over the elements of `C` -/
  foldM : {β : Type w} → {m : Type w → Type w} → [Monad m] →
      (cont : C) → (β → τ → m β) → β → m β
    := fun c f i => fold c (fun macc x => macc >>= fun acc => f acc x) (pure i)
export Fold (fold foldM)

/-- `C` with element type `τ` can be iterated using type `ρ`

**Note:** This is essentially a combination of Lean core's
[ToStream] and [Stream] classes.
By combining them we can avoid relying on distinct `ρ` types
to associate the `next?` and `iterate` functions.
-/
class Iterate (C : Type u) (τ : outParam (Type v)) (ρ : outParam (Type w)) where
  iterate : (cont : C) → ρ
  next? : ρ → Option (τ × ρ)
export Iterate (iterate next?)


/-! ### New Operations -/

/-- `C` has an empty collection, and a way to insert `τ`s -/
class Insert (C : Type u) (τ : outParam (Type v)) where
  empty : C
  insert : (cont : C) → τ → C
  singleton : τ → C := insert empty
export Insert (empty insert singleton)

class Size (C : Type u) where
  /-- Number of elements in the collection. -/
  size : (cont : C) → Nat
export Size (size)

instance (priority := low) Size.ofFold [Fold C τ] : Size C where
  size c := Fold.fold c (fun acc _x => acc+1) 0
