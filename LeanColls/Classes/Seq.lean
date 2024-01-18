/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Ops
import LeanColls.Data.List

import Mathlib.Data.List.OfFn

namespace LeanColls

/-! ## Sequences

Sequences are an ordered collection of elements.

All sequences are isomorphic to [List],
which is also the model used for sequence operations.
-/

/-- A collection which is ordered (i.e. isomorphic to [List]). -/
class Seq.{u,v} (C : Type u) (τ : outParam (Type v))
  extends
  Fold.{u,v,max u v} C τ,
  Insert C τ,
  ToList C τ,
  Membership τ C,
  Size C,
  Append C
  where
  ofFn : {sz : Nat} → (Fin sz → τ) → C
  get : (cont : C) → Fin (size cont) → τ
  set : (cont : C) → Fin (size cont) → τ → C
  update : (cont : C) → Fin (size cont) → (τ → τ) → C :=
    fun cont i f => set cont i (f (get cont i))
  -- TODO: should `cons` and `snoc` label their container argument?
  -- The argument order/position is intentional, for readability,
  -- so I don't know that anyone *should* use named application here.
  cons : τ → C → C := (singleton · ++ ·)
  getCons? : C → Option (τ × C) := fun cont =>
    match h : size cont with
    | 0 => none
    | _+1 =>
      some (
        get cont (Fin.cast h.symm 0)
      , ofFn (fun i => get cont (i.succ.cast h.symm)))
  snoc : C → τ → C := (· ++ singleton ·)
  getSnoc? : C → Option (C × τ) := fun cont =>
    match h : size cont with
    | 0 => none
    | _+1 =>
      some (
        ofFn (fun i => get cont (i.castSucc.cast h.symm))
      , get cont (Fin.last _ |>.cast h.symm))

end LeanColls

namespace List

open LeanColls

@[simp] instance : Seq (List τ) τ where
  toList := id
  empty := []
  insert L x := x::L
  size := List.length
  fold L f init := List.foldl f init L
  ofFn := List.ofFn
  get := List.get
  set L i x := List.set L i x
  cons := List.cons
  getCons? := getCons?
  snoc := snoc
  getSnoc? := getSnoc?

@[simp] theorem toList_eq (L : List α) : toList L = L := rfl
@[simp] theorem size_cons (x : α) (xs) : size (x :: xs) = size xs + 1 := length_cons _ _
@[simp] theorem size_nil : size ([] : List α) = 0 := rfl
@[simp] theorem toMultiset_eq (L : List α) : ToMultiset.toMultiset L = L := rfl

end List

namespace LeanColls

class LawfulSeq (C : Type u) (τ : outParam (Type v)) [Seq C τ]
  extends
    Mem.ToList C τ,
    Append.ToList C τ,
    Insert.ToMultiset C τ
  : Prop
  where
  size_def : ∀ (cont : C),
    size cont = (toList cont).length
  toList_ofFn : ∀ (f : Fin n → τ),
    toList (Seq.ofFn (C := C) f) = Seq.ofFn f
  get_def : ∀ (cont : C) i,
    Seq.get cont i = Seq.get (toList cont) (i.cast (size_def _))
  toList_set : ∀ (cont : C) i x,
    toList (Seq.set cont i x) = Seq.set (toList cont) (i.cast (size_def _)) x
  toList_update : ∀ (cont : C) i f,
    toList (Seq.update cont i f) = Seq.update (toList cont) (i.cast (size_def _)) f
  toList_cons : ∀ x (cont : C),
    toList (Seq.cons x cont) = Seq.cons x (toList cont)
  getCons?_eq_none : ∀ (cont : C),
    Seq.getCons? cont = none ↔ toList cont = []
  getCons?_eq_some : ∀ (cont : C) x c',
    Seq.getCons? cont = some (x,c') ↔ toList cont = x :: toList c'
  toList_snoc : ∀ (cont : C) x,
    toList (Seq.snoc cont x) = Seq.snoc (toList cont) x
  getSnoc?_eq_none : ∀ (cont : C),
    Seq.getSnoc? cont = none ↔ toList cont = []
  getSnoc?_eq_some : ∀ (cont : C) x c',
    Seq.getSnoc? cont = some (c',x) ↔ toList cont = (toList c').snoc x

end LeanColls

namespace List

instance : LeanColls.LawfulSeq (List τ) τ where
  mem_iff_mem_toList   := by simp
  toList_append        := by simp
  toList_ofFn          := by simp
  toList_set           := by simp
  get_def              := by simp
  getCons?_eq_some        := by simp
  getSnoc?_eq_some        := by simp
  toMultiset_empty     := by simp
  toMultiset_insert    := by simp
  toMultiset_singleton := by simp
  size_def             := by simp
  getCons?_eq_none        := by simp
  getSnoc?_eq_none        := by simp
  toList_update := by intros; rfl
  toList_cons := by intros; rfl
  toList_snoc := by intros; rfl

end List

namespace LeanColls

namespace Seq

export Mem.ToList (
  mem_iff_mem_toList
)

export Append.ToList (
  toList_append
)
attribute [simp] toList_append

export Insert.ToMultiset (
  toMultiset_empty
)
attribute [simp] toMultiset_empty

export LawfulSeq (
size_def
toList_ofFn
get_def
toList_set
toList_update
toList_cons
getCons?_eq_none
getCons?_eq_some
toList_snoc
getSnoc?_eq_none
getSnoc?_eq_some
)
attribute [simp] toList_ofFn toList_set toList_update toList_cons toList_snoc

variable [Seq C τ] [LawfulSeq C τ]

@[simp] theorem size_set (cont : C) (i : Fin (size cont)) (x : τ)
  : size (set cont i x) = size cont := by
  simp [size_def]

@[simp] theorem size_update (cont : C) (i f)
  : size (Seq.update cont i f) = size cont := by
  simp [size_def]

@[simp] theorem size_cons (cont : C) (x)
  : size (Seq.cons x cont) = size cont + 1 := by
  simp [size_def]

@[simp] theorem size_snoc (cont : C) (x)
  : size (Seq.snoc cont x) = size cont + 1 := by
  simp [size_def]

@[simp] theorem size_append (c1 c2 : C)
  : size (c1 ++ c2) = size c1 + size c2 := by
  simp [size_def]

@[simp] theorem size_singleton (x : τ)
  : size (singleton (C := C) x) = 1 := by
  simp [size_def]

@[simp] theorem size_ofFn (f : Fin n → τ)
  : size (ofFn (C := C) f) = n := by
  simp [size_def, toList_ofFn]

@[simp] theorem get_ofFn (f : Fin n → τ) (i : Fin (size (ofFn f)))
  : get (ofFn (C := C) f) i = f (i.cast <| size_ofFn f) := by
  rcases i with ⟨i,hi⟩
  rw [get_def]
  suffices ∀ L (_h : L = ofFn f) (hi' : i < L.length),
    get L ⟨i,hi'⟩ = f ⟨i, size_ofFn (C := C) f ▸ hi⟩
    from this _ (toList_ofFn _) (by simp at hi; simp [*])
  intro L hL hi'
  cases hL; simp

set_option pp.proofs.withType false

theorem get_set (cont : C) (i : Fin (size cont)) (x : τ) (j)
  : get (set cont i x) j =
    if i.val = j.val then x else get cont (j.cast (size_set ..)) := by
  rcases i with ⟨i,hi⟩; rcases j with ⟨j,hj⟩
  rw [get_def (C := C), get_def (C := C)]; simp
  suffices ∀ L (_hL : L = toList cont) L' (_hL' : L' = List.set L i x)
            (hj' : j < L.length) (hj'' : j < L'.length),
    List.get L' ⟨j,hj''⟩ = if i = j then x else get L ⟨j,hj'⟩
    from this (toList cont) rfl (toList (set cont ⟨i,hi⟩ x))
          (toList_set ..) (by simp_all [size_def]) (by simp_all [size_def])
  intro L _hL L' hL' hj' hj''
  cases hL'; rw [List.get_set]; rfl

theorem get_update (cont : C) (i : Fin (size cont)) (f : τ → τ) (j)
  : get (update cont i f) j =
    if i.val = j.val then f (get cont (j.cast (size_update ..)))
    else get cont (j.cast (size_update ..)) := by
  rcases i with ⟨i,hi⟩; rcases j with ⟨j,hj⟩
  rw [get_def (C := C), get_def (C := C)]; simp
  suffices ∀ L (_hL : L = toList cont) L' (hi : i < size L) (_hL' : L' = update L ⟨i,hi⟩ f)
            (hj' : j < L.length) (hj'' : j < L'.length),
    List.get L' ⟨j,hj''⟩ = if i = j then f (get L ⟨j,hj'⟩) else get L ⟨j,hj'⟩
    from this (toList cont) rfl (toList (update cont ⟨i,hi⟩ f)) (by rw [size_def] at hi; simp_all)
          (toList_update ..) (by simp_all [size_def]) (by simp_all [size_def])
  intro L _hL L' hi' hL' hj' hj''
  cases hL'; simp [update]; rw [List.get_set]
  split <;> simp_all
