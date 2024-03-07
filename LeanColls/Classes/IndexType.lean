/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import Mathlib.Tactic.FinCases

import LeanColls.Classes.Ops
import LeanColls.MathlibUpstream

/-! ## Index Types

Index types are types which can serve as the index into a sequence.
Every index type is in bijection with `Fin n`.

N.B. this is equivalent to [Fintype] in mathlib, but [Fintype] has many
instances with very bad computational complexity.
-/

namespace LeanColls

structure IndexType.Univ (ι : Type u)

def IndexType.univ (ι : Type u) : IndexType.Univ ι := .mk

class IndexType (ι : Type u)
  extends
    ToList (IndexType.Univ ι) ι,
    Fold (IndexType.Univ ι) ι
  where
  card : Nat
  toFin : ι → Fin card
  fromFin : Fin card → ι
  toList _ := Fin.foldr card (fromFin · :: ·) []
  fold := fun _ f acc => Fin.foldl card (fun acc x => f acc (fromFin x)) acc
  foldM := fun _ f acc => Fin.foldlM card acc (fun x acc => f acc (fromFin x))

class LawfulIndexType (ι : Type u) [I : IndexType ι] where
  toFin_leftInv : I.toFin.LeftInverse I.fromFin
  toFin_rightInv : I.toFin.RightInverse I.fromFin

namespace IndexType

variable [IndexType ι] [LawfulIndexType ι]

@[simp] theorem toFin_fromFin
  : ∀ i, toFin (ι := ι) (fromFin i) = i
  := LawfulIndexType.toFin_leftInv

@[simp] theorem fromFin_toFin
  : ∀ x, fromFin (ι := ι) (toFin x) = x
  := LawfulIndexType.toFin_rightInv

@[simp] theorem toFin_inj (i j : ι) : toFin i = toFin j ↔ i = j := by
  constructor
  · apply LawfulIndexType.toFin_rightInv.injective
  · rintro rfl; rfl

@[simp] theorem fromFin_inj (i j : Fin (IndexType.card ι)) : fromFin i = fromFin j ↔ i = j := by
  constructor
  · apply LawfulIndexType.toFin_leftInv.injective
  · rintro rfl; rfl

/-! #### Fin n -/

instance : IndexType (Fin n) where
  card := n
  toFin := id
  fromFin := id

instance : LawfulIndexType (Fin n) where
  toFin_leftInv  := by intro _; rfl
  toFin_rightInv := by intro _; rfl


/-! #### Product -/

variable {α : Type u} {β : Type v}

instance [IndexType.{u,w} α] [IndexType.{v,w} β] : IndexType.{max u v, w} (α × β) where
  card := card α * card β
  toFin := fun x =>
    match x with
    | (a,b) =>
      let ⟨a,ha⟩ := toFin a
      let ⟨b,hb⟩ := toFin b
      ⟨ a * (IndexType.card β) + b, by
        calc
          _ < a * card β + card β := by simp [*]
          _ ≤ card α * card β := by
            rw [← Nat.succ_mul]
            apply Nat.mul_le_mul_right
            exact ha ⟩
  fromFin := fun ⟨i,hi⟩ =>
    let q := i / card β
    let r := i % card β
    ( fromFin ⟨q, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; assumption)⟩
    , fromFin ⟨r, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by simp_all)⟩)

instance [IndexType.{u,w} α] [LawfulIndexType.{u,w} α] [IndexType.{v,w} β] [LawfulIndexType.{v,w} β]
  : LawfulIndexType.{max u v, w} (α × β) where
  toFin_leftInv := by
    rintro ⟨i,hi⟩; simp [toFin, fromFin]
    exact Nat.div_add_mod' i (card β)
  toFin_rightInv := by
    rintro ⟨a,b⟩; simp [toFin, fromFin]
    constructor
    · convert fromFin_toFin a
      rw [Nat.mul_comm, Nat.mul_add_div]
      simp
      apply Nat.div_eq_of_lt
      simp; apply Fin.pos; apply IndexType.toFin b
    · convert fromFin_toFin b
      apply Nat.mul_add_mod_of_lt
      exact Fin.prop (toFin b)

/-! #### Sum -/

instance [IndexType.{u,w} α] [IndexType.{v,w} β] : IndexType.{max u v, w} (α ⊕ β) where
  card := card α + card β
  toFin := fun x =>
    match x with
    | .inl a =>
      let ⟨a,ha⟩ := toFin a
      ⟨ a, Nat.lt_add_right (card β) ha ⟩
    | .inr b =>
      let ⟨b,hb⟩ := toFin b
      ⟨ card α + b, Nat.add_lt_add_left hb _ ⟩
  fromFin := fun ⟨i,hi⟩ =>
    if h : i < card α then
      .inl (fromFin ⟨i,h⟩)
    else
      .inr (fromFin ⟨i-card α, by simp at h; exact Nat.sub_lt_left_of_lt_add h hi⟩)

instance [IndexType.{u,w} α] [LawfulIndexType.{u,w} α] [IndexType.{v,w} β] [LawfulIndexType.{v,w} β]
  : LawfulIndexType (α ⊕ β) where
  toFin_leftInv := by
    rintro ⟨i,hi⟩
    simp [toFin, fromFin]
    if i < card α then
      simp_all
    else
      simp [*]; simp_all
  toFin_rightInv := by
    rintro (a|b)
      <;> simp [toFin, fromFin]

-- TODO: deriving handler for nonrecursive inductives
