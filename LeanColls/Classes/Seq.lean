/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Ops
import LeanColls.Classes.Indexed

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
  get : (c : C) → Fin (size c) → τ
  set : (c : C) → Fin (size c) → τ → C
  update : (c : C) → Fin (size c) → (τ → τ) → C :=
    fun c i f => set c i (f (get c i))
  cons : τ → C → C := (singleton · ++ ·)
  cons? : C → Option (τ × C) := fun c =>
    match h : size c with
    | 0 => none
    | _+1 =>
      some (
        get c (Fin.cast h.symm 0)
      , ofFn (fun i => get c (i.succ.cast h.symm)))
  snoc : C → τ → C := (· ++ singleton ·)
  snoc? : C → Option (C × τ) := fun c =>
    match h : size c with
    | 0 => none
    | _+1 =>
      some (
        ofFn (fun i => get c (i.castSucc.cast h.symm))
      , get c (Fin.last _ |>.cast h.symm))

class LawfulSeq (C : Type u) (τ : outParam (Type v)) [Seq C τ]
  extends
    Mem.ToList C τ,
    Append.ToList C τ,
    Insert.ToMultiset C τ
  where
  size_def : ∀ (c : C),
    size c = (toList c).length
  toList_ofFn : ∀ (f : Fin n → τ),
    toList (Seq.ofFn (C := C) f) = List.ofFn f
  get_def : ∀ (c : C) i,
    Seq.get c i = List.get (toList c) (i.cast (size_def _))
  toList_set : ∀ (c : C) i x,
    toList (Seq.set c i x) = List.set (toList c) i x
  toList_update : ∀ (c : C) i f,
    toList (Seq.update c i f) = toList (Seq.set c i (f (Seq.get c i)))
    := by intros; rfl
  toList_cons : ∀ x (c : C),
    toList (Seq.cons x c) = toList (singleton x ++ c)
    := by intros; rfl
  cons?_eq_none : ∀ (c : C),
    Seq.cons? c = none ↔ toList c = []
  cons?_eq_some : ∀ (c : C) x c',
    Seq.cons? c = some (x,c') → toList c = x :: toList c'
  cons?_eq_some_of_toList : ∀ (c : C) x c',
    toList c = x :: c' → ∃ c'', Seq.cons? c = some (x,c'')
  toList_snoc : ∀ (c : C) x,
    toList (Seq.snoc c x) = toList (c ++ singleton x)
    := by intros; rfl
  snoc?_eq_none : ∀ (c : C),
    Seq.snoc? c = none ↔ toList c = []
  snoc?_eq_some : ∀ (c : C) x c',
    Seq.snoc? c = some (c',x) → toList c = toList c' ++ [x]
  snoc?_eq_some_of_toList : ∀ (c : C) x c',
    toList c = c' ++ [x] → ∃ c'', Seq.snoc? c = some (c'',x)


namespace Seq

export Mem.ToList (
  mem_iff_mem_toList
)

export Append.ToList (
  toList_append
)

export Insert.ToMultiset (
  toMultiset_empty
)

export LawfulSeq (
size_def
toList_ofFn
get_def
toList_set
toList_update
toList_cons
cons?_eq_none
cons?_eq_some
cons?_eq_some_of_toList
toList_snoc
snoc?_eq_none
snoc?_eq_some
snoc?_eq_some_of_toList
)

variable [Seq C τ] [LawfulSeq C τ]

@[simp] theorem size_update (c : C) (i f)
  : size (Seq.update c i f) = size c :=
  by rw [size_def, size_def, toList_update, toList_set]; simp

@[simp] theorem size_cons (c : C) (x)
  : size (Seq.cons x c) = size c + 1 := by
  rw [size_def, size_def, toList_cons, toList_append]
  simp

@[simp] theorem size_snoc (c : C) (x)
  : size (Seq.snoc c x) = size c + 1 := by
  rw [size_def, size_def, toList_snoc, toList_append]
  simp


/-! ### Relationship with [Indexed] -/

structure FixSize (C) [Size C] (n : Nat) where
  data : C
  hsize : size data = n

def FixSize.cast [Size C] (h : n = n') (c : FixSize C n) : FixSize C n' :=
  ⟨c.data, Trans.trans c.hsize h⟩

def fixSize (c : C) : FixSize C (size c) := {
  data := c
  hsize := rfl
}

instance [Seq C τ] : Indexed (FixSize C n) (Fin n) τ := sorry -- TODO
instance [Seq C τ] : LawfulIndexed (FixSize C n) (Fin n) τ := sorry -- TODO
