/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Seq
import LeanColls.Classes.Indexed

namespace LeanColls

/-! ## FixSize

Every [Seq] instance can be adapted to an [Indexed] instance
by restricting the type to a fixed size.
This file implements such a transformation.
 -/

structure FixSize.{u,v,w} (C : Type u) [Size C] (ι : Type v) [IndexType.{v,w} ι] where
  data : C
  hsize : size data = IndexType.card ι

def Seq.fixSize [Size C] (c : C) : FixSize C (Fin (size c)) := {
  data := c
  hsize := rfl
}

namespace FixSize

instance [Seq C τ] [LawfulSeq C τ] [IndexType ι] : Indexed (FixSize C ι) ι τ := {
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

instance [Seq C τ] [LawfulSeq C τ] [IndexType ι] [LawfulIndexType ι]
    : LawfulIndexed (FixSize C ι) ι τ where
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
    · simp [Fin.val_inj]
      assumption
