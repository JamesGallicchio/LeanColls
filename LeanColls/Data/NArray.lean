/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Data.Array


namespace LeanColls.Data

/-- Array with fixed size `sz`. -/
structure NArray (α : Type u) (sz : Nat) : Type u where
  data : Array α
  hsize : data.size = sz

namespace NArray

def ofFn (f : Fin sz → α) : NArray α sz :=
  ⟨Array.ofFn f, by simp⟩

def get (A : NArray α sz) (i : Fin sz) : α :=
  A.data.get ⟨i, by rw [A.hsize]; exact i.isLt⟩

def set (A : NArray α sz) (i : Fin sz) (a : α) : NArray α sz :=
  ⟨ A.data.set ⟨i, by rw [A.hsize]; exact i.isLt⟩ a
  , by simp [A.hsize]⟩

def update (A : NArray α sz) (i : Fin sz) (f : α → α)
  : NArray α sz :=
  A.set i (f <| A.get i)

instance : Indexed (NArray α sz) (Fin sz) (α) where
  ofFn := ofFn
  get := get
  set := set
  update := update

instance : LawfulIndexed (NArray α sz) (Fin sz) α where
  get_ofFn := by
    intro f
    ext i
    simp [Indexed.get, Indexed.ofFn, get, ofFn]
  get_set := by
    intro c i a j
    simp [Indexed.get,Set.set,get,set]
    split
    · simp [*]
    next h =>
      rw [Array.get_set_ne]
      simp
      exact Fin.val_ne_iff.mpr h
  get_update := by
    intro c i f j
    simp [Indexed.get,Indexed.update,get,update,set]
    split
    · simp [*]
    next h =>
      rw [Array.get_set_ne]
      simp
      exact Fin.val_ne_iff.mpr h

def cast (h : sz = sz') : NArray α sz → NArray α sz' :=
  h ▸ id

def ofArray (A : Array α) : NArray α A.size :=
  ⟨A, rfl⟩

def ofList (L : List α) : NArray α L.length :=
  cast (by simp) <| ofArray L.toArray

def empty : NArray α 0 := ofArray #[]
def singleton (a : α) : NArray α 1 := ofArray #[a]

def cons (a : α) : NArray α n → NArray α (n+1)
| ⟨A,h⟩ => ⟨A.cons a, by simp [h]⟩

def snoc (a : α) : NArray α n → NArray α (n+1)
| ⟨A,h⟩ => ⟨A.snoc a, by simp [h]⟩

def front : NArray α (n+1) → α × NArray α n
| ⟨A,h⟩ => (A.get (h ▸ 0), ofFn (fun i => A.get (h ▸ i.succ)))

def back : NArray α (n+1) → NArray α n × α
| ⟨A,h⟩ => (⟨A.pop, by simp [h]⟩, A.get (h ▸ Fin.last n))
