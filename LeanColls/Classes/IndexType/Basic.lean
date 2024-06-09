/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.ProxyType

import LeanColls.Classes.Ops
import LeanColls.Classes.Ops.Fold
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
    Fold.LawfulFold (IndexType.Univ ι) ι,
    Fold.AgreesWithToMultiset (IndexType.Univ ι) ι
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

@[simp]
theorem length_toList_univ [IndexType α] [LawfulIndexType α]
  : List.length (toList <| IndexType.univ α) = IndexType.card α := by
  rw [LawfulIndexType.toList_eq_ofFn]; simp

@[simp]
theorem get_toList_univ [IndexType α] [LawfulIndexType α] (i)
  : List.get (toList <| univ α) i = IndexType.fromFin (i.cast (by simp)) := by
  suffices ∀ L i (hL : L = toList (univ α)), List.get L i = fromFin (i.cast (by simp [hL]))
    from this _ _ rfl
  intro L i hL
  rw [LawfulIndexType.toList_eq_ofFn] at hL
  subst hL
  simp

@[simp]
theorem mem_toList_univ [IndexType α] [LawfulIndexType α] (x) : x ∈ (toList <| univ α) := by
  simp [LawfulIndexType.toList_eq_ofFn, List.mem_ofFn]
  use toFin x
  simp

instance (priority := default) : DecidableEq ι := by
  intro x y; rw [← toFin_eq_iff]; infer_instance


/-! #### Transport over equivalence -/


def ofEquiv {ι} [IndexType.{_,w} ι'] (f : ι' ≃ ι) : IndexType.{_,w} ι where
  card := IndexType.card ι'
  toFin   := IndexType.toFin ∘ f.symm
  fromFin := f ∘ IndexType.fromFin
  toFold := Fold.instMap (fun ⟨⟩ => IndexType.univ (ι')) f

def ofEquivLawful {ι} [I' : IndexType ι'] [LI' : LawfulIndexType ι'] (f : ι' ≃ ι)
    : @LawfulIndexType ι (ofEquiv f) :=
  @LawfulIndexType.mk
    (ι := ι)
    (I := ofEquiv f)
    (leftInv  := by simp [ofEquiv]; intro; simp)
    (rightInv := by simp [ofEquiv]; intro; simp)
    (toList_eq_ofFn := by simp [ofEquiv]; rfl)
    (toLawfulFold := Fold.LawfulFold.instMap ..)
    (toAgreesWithToMultiset := by
      convert @Fold.AgreesWithToMultiset.instMap _ _ _ _ _
        inferInstance _ (fun (_ : Univ ι) => Univ.mk) f
      simp [ofEquiv, inferInstance, ToMultiset.instMap]
      unfold instToMultiset toMultiset
      congr; ext _
      have := LI'.toList_eq_ofFn
      simp only [Multiset.map_coe, this]
      congr; simp
      rfl)

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
  exists_eq_list_foldl := by
    rintro ⟨⟩
    refine ⟨_, rfl, ?_⟩
    intro β f init; simp [toList, fold]
  foldM_eq_fold := by
    rintro m β _ _ ⟨⟩ f init; simp [foldM, fold]

/-! #### Fin n -/

instance : IndexType (Fin n) where
  card := n
  toFin := id
  fromFin := id

instance : LawfulIndexType (Fin n) where
  leftInv  := by intro _; rfl
  rightInv := by intro _; rfl
  exists_eq_list_foldl := by
    rintro ⟨⟩
    refine ⟨_, rfl, ?_⟩
    simp [toList, fold, Fin.foldl_eq_foldl_ofFn]
  foldM_eq_fold := by
    rintro β _ _ _ ⟨⟩ f init
    simp [foldM, fold, Fin.foldlM_eq_foldl]


section
variable {α : Type u} [IndexType.{u,w} α] [LawfulIndexType.{u,w} α]
         {β : Type v} [IndexType.{v,w} β] [LawfulIndexType.{v,w} β]

/-! #### Product -/

instance : IndexType.{max u v, w} (α × β) where
  card := card α * card β
  toFin := fun (a,b) => Fin.pair (toFin a) (toFin b)
  fromFin := fun p => (fromFin (Fin.pair_left p), fromFin (Fin.pair_right p))
  toToList :=
    let _ := ToList.instProd (C₁ := Univ α) (C₂ := Univ β)
    ToList.instMap (C₁ := Univ α × Univ β) (C₂ := Univ (α × β)) (fun ⟨⟩ => (⟨⟩,⟨⟩)) id
  toFold :=
    let _ := Fold.instProd (C₁ := Univ α) (C₂ := Univ β)
    Fold.instMap (C := Univ α × Univ β) (C' := Univ (α × β)) (fun ⟨⟩ => (⟨⟩,⟨⟩)) id

@[simp]
theorem toList_univ_prod {c : Univ (α × β)}: toList c = toList (univ α) ×ˢ toList (univ β) := by
  simp [instIndexTypeProd, ToList.instMap, ToList.instProd]

@[simp]
theorem toMultiset_univ_prod : toMultiset (univ (α × β)) = toMultiset (univ α) ×ˢ toMultiset (univ β) := by
  simp only [instIndexTypeProd, ToList.instMap, ToList.instProd, instToMultiset]; simp

instance : LawfulIndexType.{max u v, w} (α × β) where
  rightInv := by
    rintro ⟨i,hi⟩; simp [toFin, fromFin]
  leftInv := by
    rintro ⟨a,b⟩; simp [toFin, fromFin]
  toList_eq_ofFn := by
    simp [toList, fromFin]
    apply List.ext_get
    · simp [card, List.length_product]
    intro i h1 h2
    simp [List.get_product_eq_get_pair]
    constructor <;>
      simp [← Fin.val_inj, Fin.pair_left, Fin.pair_right]
  exists_eq_list_foldl :=
    -- these proof goals are really annoying, and I'm not sure how to automate the
    -- "just keep unfolding until we actually find the difference" step
    let _a := Fold.instProd (C₁ := Univ α) (C₂ := Univ β)
    let _b := Fold.instMap (C' := Univ (α × β)) (C := Univ α × Univ β)
              (fun ⟨⟩ => (⟨⟩,⟨⟩)) id
    let _c := ToMultiset.instProd (C₁ := Univ α) (C₂ := Univ β)
    let _d := ToMultiset.instMap (C₂ := Univ (α × β)) (C₁ := Univ α × Univ β)
              (fun ⟨⟩ => (⟨⟩,⟨⟩)) id
    let _e := Fold.AgreesWithToMultiset.instProd (C₁ := Univ α) (C₂ := Univ β)
    let f := Fold.AgreesWithToMultiset.instMap (C' := Univ (α × β)) (C := Univ α × Univ β)
      (fun ⟨⟩ => (⟨⟩,⟨⟩)) id
    by
    have := f.exists_eq_list_foldl
    intro c
    specialize this c
    rcases this with ⟨L,h1,h2⟩
    refine ⟨L,?_,h2⟩
    rw [h1]
    simp (config := {zetaDelta := true})
    simp only [ToMultiset.instMap, ToMultiset.instProd, toMultiset]
    simp
  toLawfulFold :=
    @Fold.LawfulFold.instMap (Univ α × Univ β) _ (Univ (α × β)) _
      Fold.instProd
      Fold.LawfulFold.instProd
      (fun ⟨⟩ => (⟨⟩,⟨⟩)) id


/-! #### Sigma -/

instance : IndexType.{max u v, w} ((_ : α) × β) :=
  IndexType.ofEquiv (Equiv.sigmaEquivProd α β).symm

instance : LawfulIndexType.{max u v, w} ((_ : α) × β) :=
  IndexType.ofEquivLawful _


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
  toToList :=
    let _ := ToList.instSum (C₁ := Univ α) (C₂ := Univ β)
    ToList.instMap (C₁ := Univ α × Univ β) (C₂ := Univ (α ⊕ β)) (fun ⟨⟩ => (⟨⟩,⟨⟩)) id
  toFold :=
    let _ := Fold.instSum (C₁ := Univ α) (C₂ := Univ β)
    Fold.instMap (C := Univ α × Univ β) (C' := Univ (α ⊕ β)) (fun ⟨⟩ => (⟨⟩,⟨⟩)) id

theorem toList_univ_sum {c : Univ (α ⊕ β)} :
    toList c = (toList (univ α) |>.map Sum.inl) ++ (toList (univ β) |>.map Sum.inr) := by
  simp [instIndexTypeSum, ToList.instMap, ToList.instSum]

theorem toMultiset_univ_sum :
    toMultiset (univ (α ⊕ β)) = (toMultiset (univ α)).map Sum.inl + (toMultiset (univ β)).map Sum.inr := by
  simp only [instIndexTypeSum, ToList.instMap, ToList.instSum, instToMultiset]
  simp only [
    List.map_append,
    List.map_map,
    Function.id_comp,
    ToList.toMultiset_toList]
  rfl

instance : LawfulIndexType (α ⊕ β) where
  leftInv := by
    rintro (a|b)
      <;> simp [toFin, fromFin]
  rightInv := by
    rintro ⟨i,hi⟩
    simp [toFin, fromFin]
    if i < card α then
      simp_all
    else
      simp [*]; simp_all
  toList_eq_ofFn := by
    simp [toList_univ_sum, toList]
    apply List.ext_get
    · simp [card]
    intro i h1 h2
    simp [fromFin]
    split
    next h =>
      rw [List.get_append_left]
      · simp
      · simpa using h
    next h =>
      rw [List.get_append_right]
      · simp
      · simpa using h
      · simp at h1 ⊢
        omega
  exists_eq_list_foldl :=
    -- these proof goals are really annoying, and I'm not sure how to automate the
    -- "just keep unfolding until we actually find the difference" step
    let _a := Fold.instSum (C₁ := Univ α) (C₂ := Univ β)
    let _b := Fold.instMap (C' := Univ (α ⊕ β)) (C := Univ α × Univ β)
              (fun ⟨⟩ => (⟨⟩,⟨⟩)) id
    let _c := ToMultiset.instSum (C₁ := Univ α) (C₂ := Univ β)
    let _d := ToMultiset.instMap (C₂ := Univ (α ⊕ β)) (C₁ := Univ α × Univ β)
              (fun ⟨⟩ => (⟨⟩,⟨⟩)) id
    let _e := Fold.AgreesWithToMultiset.instSum (C₁ := Univ α) (C₂ := Univ β)
    let f := Fold.AgreesWithToMultiset.instMap (C' := Univ (α ⊕ β)) (C := Univ α × Univ β)
      (fun ⟨⟩ => (⟨⟩,⟨⟩)) id
    by
    have := f.exists_eq_list_foldl
    intro c
    specialize this c
    rcases this with ⟨L,h1,h2⟩
    refine ⟨L,?_,h2⟩
    rw [h1]
  toLawfulFold :=
    @Fold.LawfulFold.instMap (Univ α × Univ β) _ (Univ (α ⊕ β)) _
      Fold.instSum
      Fold.LawfulFold.instSum
      (fun ⟨⟩ => (⟨⟩,⟨⟩)) id


end


/-! #### Generic inductives -/

section
open Lean Elab Command

macro "derive_indextype% " t:term : term => `(term| IndexType.ofEquiv (proxy_equiv% $t))
macro "derive_lawfulindextype% " t:term : term => `(term| IndexType.ofEquivLawful (proxy_equiv% $t))

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
