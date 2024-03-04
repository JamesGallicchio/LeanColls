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
instance [Seq C τ] [LawfulSeq C τ] : Indexed (FixSize C n) (Fin n) τ where
  toMultiBagWithIdx := sorry
  mem x c := x ∈ c.data
  get c i := Seq.get c.data (i.cast c.hsize.symm)
  set c i x :=
    ⟨ Seq.set c.data (i.cast c.hsize.symm) x
    , by simp; exact c.hsize ⟩
  update c i f :=
    ⟨ Seq.update c.data (i.cast c.hsize.symm) f
    , by simp; exact c.hsize ⟩
  ofFn f := ⟨ Seq.ofFn f, by simp ⟩
  toMultiset c := toList c.data
  fold' := sorry

instance [Seq C τ] [LawfulSeq C τ]: LawfulIndexed (FixSize C n) (Fin n) τ where
  get_ofFn f := by simp [Indexed.ofFn, Indexed.get]
  get_set := by
    simp [Indexed.set, Indexed.get]
    intros; simp [Seq.get_set, Fin.val_eq_val]
  get_update := by
    simp [Indexed.get, Indexed.update]
    intros; simp [Seq.get_update, Fin.val_eq_val]
