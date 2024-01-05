/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Indexed

namespace LeanColls

/-- An indexed collection can be restricted to some "smaller" domain -/
structure Slice (C ι τ) [Indexed C ι τ] (ι') (f : ι' ↪ ι) where
  data : C

namespace Slice

def get [Indexed C ι τ] (slice : Slice C ι τ ι' f) (i) :=
  Indexed.get slice.data (f i)

def update [Indexed C ι τ] (slice : Slice C ι τ ι' f) (i' : ι') (g : τ → τ) : Slice C ι τ ι' f :=
  ⟨Indexed.update slice.data (f i') g⟩

def set [Indexed C ι τ] (slice : Slice C ι τ ι' f) (i' : ι') (x : τ) : Slice C ι τ ι' f :=
  ⟨Indexed.set slice.data (f i') x⟩

instance [Indexed C ι τ] [IndexType ι'] [DecidableEq τ] [Inhabited τ]
    : Indexed (Slice C ι τ ι' f) ι' τ where
  get := Slice.get
  update := Slice.update
  mem x slice :=
    match
      foldM (m := Except Unit) (IndexType.univ ι')
        (fun _ i' =>
          if Slice.get slice i' = x then
            throw ()
          else return ()
        ) ()
    with
    | .error () => true
    | .ok () => false
  toMultiset slice :=
    toList (IndexType.univ ι') |> Multiset.ofList |>.map (Slice.get slice)
  fold slice f init :=
    fold (IndexType.univ ι') (fun acc i => f acc (i,Slice.get slice i)) init
  ofFn g := ⟨
      (Indexed.ofFn fun _ => default)
      |> fold (IndexType.univ ι') (fun c i' => Indexed.set c (f i') (g i'))
    ⟩
