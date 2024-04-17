/- Copyright (c) 2023 James Gallicchio

Authors: James Gallicchio
-/

import LeanColls.MathlibUpstream

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
  toFinset : (cont : C) → Finset τ

/-- `C` can be modeled as a multiset of `τ`s -/
class ToMultiset (C : Type u) (τ : outParam (Type v)) where
  toMultiset : (cont : C) → Multiset τ

class LawfulToMultiset (C : Type u) (τ : outParam (Type v))
        [DecidableEq τ] [ToFinset C τ] [ToMultiset C τ] where
  toFinset_toMultiset : ∀ (cont : C),
    (ToMultiset.toMultiset cont).toFinset = ToFinset.toFinset cont

attribute [simp] LawfulToMultiset.toFinset_toMultiset

instance [DecidableEq τ] [ToMultiset C τ] : ToFinset C τ where
  toFinset c := (ToMultiset.toMultiset c).toFinset

instance [DecidableEq τ] [ToMultiset C τ] : LawfulToMultiset C τ where
  toFinset_toMultiset _ := rfl

class ToList (C : Type u) (τ : outParam (Type v)) where
  toList : (cont : C) → List τ
export ToList (toList)

class LawfulToList (C : Type u) (τ : outParam (Type v))
        [ToMultiset C τ] [ToList C τ] where
  toMultiset_toList : ∀ (cont : C), (toList cont) = ToMultiset.toMultiset cont

attribute [simp] LawfulToMultiset.toFinset_toMultiset

namespace ToList

instance [ToList C τ] : ToMultiset C τ where
  toMultiset c := (toList c)

instance [ToList C τ] : LawfulToList C τ where
  toMultiset_toList _ := rfl

def prod [ToList C₁ τ₁] [ToList C₂ τ₂] : ToList (C₁ × C₂) (τ₁ × τ₂) where
  toList := fun (c1,c2) => toList c1 ×ˢ toList c2

def sum [ToList C₁ τ₁] [ToList C₂ τ₂] : ToList (C₁ × C₂) (τ₁ ⊕ τ₂) where
  toList := fun (c1,c2) =>
    (toList c1).map Sum.inl ++ (toList c2).map Sum.inr

end ToList


/-! ### Operations Defined Elsewhere -/

namespace Mem
variable (C : Type u) (τ : outParam (Type v)) [Membership τ C]

class ToFinset [ToFinset C τ] : Prop where
  mem_iff_mem_toFinset : ∀ x (cont : C),
    x ∈ cont ↔ x ∈ ToFinset.toFinset cont

class ToMultiset [ToMultiset C τ] : Prop where
  mem_iff_mem_toMultiset : ∀ x (cont : C),
    x ∈ cont ↔ x ∈ ToMultiset.toMultiset cont

class ToList [ToList C τ] : Prop where
  mem_iff_mem_toList : ∀ x (cont : C),
    x ∈ cont ↔ x ∈ ToList.toList cont

end Mem

namespace Append
variable (C : Type u) (τ : outParam (Type v)) [Append C]

class ToList [ToList C τ] : Prop where
  toList_append : ∀ (c1 c2 : C),
    toList (c1 ++ c2) = toList c1 ++ toList c2

attribute [simp] ToList.toList_append

end Append

export Functor (map)

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
