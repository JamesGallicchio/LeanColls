/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Data.Array

namespace LeanColls

structure ArrayI (ι : Type u) [IndexType ι] (α : Type v) where
  data : ArrayN α (IndexType.card ι)

namespace ArrayI

instance [IndexType ι] : Indexed (ArrayI ι α) ι α := {
  Indexed.instOfIndexType
    (get := fun ⟨a⟩ i =>
      Indexed.get a (IndexType.toFin i))
    (ofFn := fun f =>
      ⟨ Indexed.ofFn fun x => f (IndexType.fromFin x) ⟩)
    (update := fun ⟨a⟩ i f =>
      ⟨ Indexed.update a (IndexType.toFin i) f ⟩)
  with
  set := fun ⟨a⟩ i x => ⟨Indexed.set a (IndexType.toFin i) x⟩
}

instance [IndexType ι] [LawfulIndexType ι] : LawfulIndexed (ArrayI ι α) ι α where
  get_ofFn := by
    intro f
    simp [instIndexedArrayI, Indexed.get, Indexed.ofFn]
  get_set_eq := by
    intro c i j a h
    simp only [Indexed.instOfIndexType, instIndexedArrayI, Indexed.get, Indexed.set]
    rw [Seq.get_set_eq]
    simp only [h, Fin.coe_cast]
  get_set_ne := by
    intro c i j a h
    simp only [Indexed.instOfIndexType, instIndexedArrayI, Indexed.get, Indexed.set]
    rw [Seq.get_set_ne _ _ _ _ ?ne]
    case ne =>
      intro contra
      simp only [Fin.coe_cast, Fin.val_inj, IndexType.toFin_inj] at contra
      contradiction
    simp only [Fin.cast_trans]
  get_update_eq := by
    intro c i j f h
    simp only [Indexed.instOfIndexType, instIndexedArrayI, Indexed.get, Indexed.update]
    rw [Seq.get_update_eq]
    simp only [h, Fin.coe_cast]
  get_update_ne := by
    intro c i j a h
    simp only [Indexed.instOfIndexType, instIndexedArrayI, Indexed.get, Indexed.update]
    rw [Seq.get_update_ne _ _ _ _ ?ne]
    case ne =>
      intro contra
      simp only [Fin.coe_cast, Fin.val_inj, IndexType.toFin_inj] at contra
      contradiction
    simp only [Fin.cast_trans]
