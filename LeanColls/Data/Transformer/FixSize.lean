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

structure FixSize (C) [Size C] (n : Nat) where
  data : C
  hsize : size data = n

def FixSize.cast [Size C] (h : n = n') (c : FixSize C n) : FixSize C n' :=
  ⟨c.data, Trans.trans c.hsize h⟩

def Seq.fixSize [Size C] (c : C) : FixSize C (size c) := {
  data := c
  hsize := rfl
}

namespace FixSize

-- TODO: finish impl
instance [Seq C τ] [LawfulSeq C τ] : Indexed (FixSize C n) (Fin n) τ := {
  Indexed.instOfIndexType
    (get := fun ⟨c,hsize⟩ i => Seq.get c (i.cast hsize.symm))
    (ofFn := fun f => ⟨ Seq.ofFn f, by simp ⟩)
    (update := fun ⟨c,hsize⟩ i f =>
        ⟨ Seq.update c (i.cast hsize.symm) f
        , by simp; exact hsize ⟩) with
  mem := fun x c => x ∈ c.data
  set := fun c i x =>
    ⟨ Seq.set c.data (i.cast c.hsize.symm) x
    , by simp; exact c.hsize ⟩
}

instance [Seq C τ] [LawfulSeq C τ]: LawfulIndexed (FixSize C n) (Fin n) τ where
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
    · simp [Fin.eq_iff_veq] at *
      simp [*]
