/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Seq
import LeanColls.Classes.Indexed.Basic

namespace LeanColls

/-! ## FixSize

Every [Seq] instance can be adapted to an [Indexed] instance
by restricting the type to a fixed size.
This file implements such a transformation.
 -/

@[ext]
structure FixSize.{u,v,w} (C : Type u) [Size C] (ι : Type v) [IndexType.{v,w} ι] where
  data : C
  hsize : size data = IndexType.card ι
deriving DecidableEq

def Seq.fixSize [Size C] (c : C) : FixSize C (Fin (size c)) := {
  data := c
  hsize := rfl
}

namespace FixSize

variable [Seq C τ] [LawfulSeq C τ] [IndexType ι]

instance : Indexed (FixSize C ι) ι τ := {
  Indexed.instOfIndexType
    (get := fun ⟨c,hsize⟩ i => Seq.get c (Fin.cast hsize.symm <| IndexType.toFin i))
    (ofFn := fun f => ⟨ Seq.ofFn (f <| IndexType.fromFin ·), by simp ⟩)
    (update := fun ⟨c,hsize⟩ i f =>
        ⟨ Seq.update c (Fin.cast hsize.symm <| IndexType.toFin i) f
        , by simp; exact hsize ⟩) with
  mem := fun x c => x ∈ c.data
  set := fun c i x =>
    ⟨ Seq.set c.data (Fin.cast c.hsize.symm <| IndexType.toFin i) x
    , by simp; exact c.hsize ⟩
}

instance [LawfulIndexType ι] : LawfulIndexed (FixSize C ι) ι τ where
  get_ofFn f := by simp [Indexed.ofFn, Indexed.get]
  get_set_eq := by
    intros;
    simp [Indexed.set, Indexed.get]
    intros; simp [Seq.get_set, Fin.val_eq_val]
    intros; contradiction
  get_set_ne := by
    intros;
    simp [Indexed.set, Indexed.get]
    intros; simp [Seq.get_set, Fin.val_eq_val]
    intros; contradiction
  get_update_eq := by
    intros
    simp [Indexed.get, Indexed.update, Indexed.set, Seq.get_update, *]
  get_update_ne := by
    intros
    simp [Indexed.get, Indexed.update, Indexed.set]
    rw [Seq.get_update_ne]
    · simp
    · simp [Fin.ext_iff] at *
      simp [Fin.val_inj]; assumption

instance [Inhabited τ] : Inhabited (FixSize C ι) where
  default := Indexed.ofFn fun _ => default
