/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.ProxyType

import LeanColls.Classes.Ops
import LeanColls.Data.Transformer.View
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

instance IndexType.instFoldUnivFin : Fold (Univ (Fin n)) (Fin n) where
  fold := fun ⟨⟩ => Fin.foldl _
  foldM := fun ⟨⟩ f init => Fin.foldlM _ init (Function.swap f)

class IndexType.{u,w} (ι : Type u)
  extends
    ToList (IndexType.Univ ι) ι,
    Fold.{0,u,w} (IndexType.Univ ι) ι
  where
  card : Nat
  toFin : ι → Fin card
  fromFin : Fin card → ι
  toList _ := List.ofFn fromFin

class LawfulIndexType (ι : Type u) [I : IndexType ι]
  extends
    Fold.ToList (IndexType.Univ ι) ι
  where
  leftInv  : Function.LeftInverse  I.fromFin I.toFin
  rightInv : Function.RightInverse I.fromFin I.toFin
  toList_eq_ofFn : toList (IndexType.univ ι) = List.ofFn IndexType.fromFin := by rfl

namespace IndexType

variable [IndexType ι] [LawfulIndexType ι]

@[simp] theorem toFin_fromFin
  : ∀ i, toFin (ι := ι) (fromFin i) = i
  := LawfulIndexType.rightInv

@[simp] theorem fromFin_toFin
  : ∀ x, fromFin (ι := ι) (toFin x) = x
  := LawfulIndexType.leftInv

@[simp] theorem toFin_inj (i j : ι) : toFin i = toFin j ↔ i = j := by
  constructor
  · apply LawfulIndexType.leftInv.injective
  · rintro rfl; rfl

@[simp] theorem fromFin_inj (i j : Fin (IndexType.card ι)) : fromFin i = fromFin j ↔ i = j := by
  constructor
  · apply LawfulIndexType.rightInv.injective
  · rintro rfl; rfl

def toEquiv : ι ≃ Fin (IndexType.card ι) where
  toFun := IndexType.toFin
  invFun := IndexType.fromFin
  left_inv := LawfulIndexType.leftInv
  right_inv := LawfulIndexType.rightInv

theorem toFin_eq_iff (x y : ι) : toFin x = toFin y ↔ x = y := by
  constructor
  · apply toEquiv.injective
  · rintro rfl; rfl

theorem fromFin_eq_iff (x y : Fin _) : (fromFin x : ι) = fromFin y ↔ x = y := by
  constructor
  · apply toEquiv.symm.injective
  · rintro rfl; rfl

instance (priority := default) : DecidableEq ι := by
  intro x y; rw [← toFin_eq_iff]; infer_instance


/-! #### Transport over equivalence -/

def ofEquiv {ι} [IndexType.{_,w} ι'] (f : ι' ≃ ι) : IndexType.{_,w} ι where
  card := IndexType.card ι'
  toFin   := IndexType.toFin ∘ f.symm
  fromFin := f ∘ IndexType.fromFin
  toFold := Fold.map (fun ⟨⟩ => IndexType.univ (ι')) f

def ofEquivLawful {ι} [I' : IndexType ι'] [LI' : LawfulIndexType ι'] (f : ι' ≃ ι)
    : @LawfulIndexType ι (ofEquiv f) :=
  @LawfulIndexType.mk
    (ι := ι)
    (I := ofEquiv f)
    (leftInv  := by simp [ofEquiv]; intro; simp)
    (rightInv := by simp [ofEquiv]; intro; simp)
    (toList_eq_ofFn := by simp [ofEquiv]; rfl)
    (toToList := by
      letI := ofEquiv f; apply Fold.map.ToList
      intro c'; simp [toList, ofEquiv, LawfulIndexType.toList_eq_ofFn]; rfl)

/-! #### Unit -/

instance : IndexType Unit where
  card := 1
  toFin := fun () => 0
  fromFin := fun 0 => ()
  fold := fun ⟨⟩ f init => f init ()
  foldM := fun ⟨⟩ f init => f init ()

instance : LawfulIndexType Unit where
  leftInv := by intro; rfl
  rightInv := by rintro ⟨i,h⟩; simp [card] at h; subst h; simp [fromFin, toFin]
  fold_eq_fold_toList := by rintro β ⟨⟩ f init; simp [toList, fold]
  foldM_eq_foldM_toList := by rintro β _ _ _ ⟨⟩ f init; simp [toList, foldM]

/-! #### Fin n -/

instance : IndexType (Fin n) where
  card := n
  toFin := id
  fromFin := id

instance : LawfulIndexType (Fin n) where
  leftInv  := by intro _; rfl
  rightInv := by intro _; rfl
  fold_eq_fold_toList := by
    rintro β ⟨⟩ f init; use List.ofFn id; simp [toList, fold, Fin.foldl_eq_foldl_ofFn]
  foldM_eq_foldM_toList := by
    rintro β _ _ _ ⟨⟩ f init
    use List.ofFn id
    simp [toList, foldM, Fin.foldlM_eq_foldl, Fin.foldl_eq_foldl_ofFn, List.foldlM_eq_foldl]


section
variable {α : Type u} [IndexType.{u,w} α] [LawfulIndexType.{u,w} α]
         {β : Type v} [IndexType.{v,w} β] [LawfulIndexType.{v,w} β]

/-! #### Product -/

instance : IndexType.{max u v, w} (α × β) where
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
  fold := fun ⟨⟩ f acc =>
    fold (IndexType.univ α) (fun acc a =>
      fold (IndexType.univ β) (fun acc b =>
          f acc (a,b)
        )
        acc
      )
      acc
  foldM := fun ⟨⟩ f acc =>
    foldM (IndexType.univ α) (fun acc a =>
      foldM (IndexType.univ β) (fun acc b =>
          f acc (a,b)
        )
        acc
      )
      acc

instance : LawfulIndexType.{max u v, w} (α × β) where
  rightInv := by
    rintro ⟨i,hi⟩; simp [toFin, fromFin]
    exact Nat.div_add_mod' i (card β)
  leftInv := by
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
  fold_eq_fold_toList := by
    rintro γ ⟨⟩ f init
    refine ⟨_, List.Perm.refl _, ?_⟩
    simp [fold, toList]
    sorry


/-! #### Sigma -/

instance : IndexType.{max u v, w} ((_ : α) × β) where
  card := card α * card β
  toFin := fun x =>
    match x with
    | ⟨a,b⟩ =>
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
    ⟨ fromFin ⟨q, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; assumption)⟩
    , fromFin ⟨r, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by simp_all)⟩ ⟩

instance : LawfulIndexType.{max u v, w} ((_ : α) × β) where
  rightInv := by
    rintro ⟨i,hi⟩; simp [toFin, fromFin]
    exact Nat.div_add_mod' i (card β)
  leftInv := by
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

instance : IndexType.{max u v, w} (α ⊕ β) where
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

instance : LawfulIndexType (α ⊕ β) where
  rightInv := by
    rintro ⟨i,hi⟩
    simp [toFin, fromFin]
    if i < card α then
      simp_all
    else
      simp [*]; simp_all
  leftInv := by
    rintro (a|b)
      <;> simp [toFin, fromFin]


end


/-! #### Generic inductives -/

section
open Lean Elab Command

macro "derive_indextype% " t:term : term => `(term| IndexType.ofEquiv (proxy_equiv% $t))
macro "derive_lawfulindextype% " t:term : term => `(term| IndexType.ofEquivLawful (proxy_equiv% $t) rfl)

def mkIndexType (declName : Name) : CommandElabM Bool := do
  let indVal ← getConstInfoInduct declName
  let cmds ← liftTermElabM do
    let header ← Deriving.mkHeader `IndexType 0 indVal
    let binders' ← Deriving.mkInstImplicitBinders `Decidable indVal header.argNames
    let indexType ← `(command|
      instance $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* :
          IndexType $header.targetType := derive_indextype% _)
    let lawful ← `(command|
      instance $header.binders:bracketedBinder* $(binders'.map TSyntax.mk):bracketedBinder* :
          LawfulIndexType $header.targetType := derive_lawfulindextype% _)
    return #[indexType, lawful]
  trace[Elab.Deriving.indextype] "instance commands:\n{cmds}"
  for cmd in cmds do
    elabCommand cmd
  return true

def mkIndexTypeInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false -- mutually inductive types are not supported
  let declName := declNames[0]!
  mkIndexType declName

initialize
  registerDerivingHandler ``IndexType mkIndexTypeInstanceHandler
  registerTraceClass `Elab.Deriving.indextype

end
