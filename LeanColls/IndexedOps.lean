/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes
import LeanColls.Range
import LeanColls.View

namespace LeanColls

namespace IndexedOps

instance [Indexed C τ] : Membership τ C where
  mem x c := ∃ i, x = Indexed.nth c i

instance [Indexed C τ] : Foldable'.Correct C τ inferInstance where
  fold c f init :=
    Foldable'.Correct.fold' (Range.mk <| Size.size c) (λ acc i h =>
      f acc (Indexed.nth c ⟨i,h⟩)
    ) init
  fold' c f init :=
    Foldable'.Correct.fold' (Range.mk <| Size.size c) (λ acc i h =>
      f acc (Indexed.nth c ⟨i,h⟩) ⟨⟨i,h⟩, rfl⟩
    ) init
  foldCorrect := sorry
  fold'Correct := sorry
  memCorrect x c := by
    simp [Membership.mem, Foldable.fold, canonicalToList]
    constructor
    case mp =>
      intro h; simp [Membership.mem] at h; cases h; case intro i h =>
      
      sorry
    case mpr =>
      intro h
      sorry

structure Slice (C) (τ : outParam (Type u)) [Indexed C τ] where
  c : C
  off : Nat
  len : Nat
  h_range : off + len ≤ Size.size c

instance [Indexed C τ] : Indexed (Slice C τ) τ where
  size S := S.len
  nth S (i : Fin S.len) := Indexed.nth S.c ⟨S.off + i, Nat.le_trans (Nat.add_lt_add_left i.isLt _) (Slice.h_range S)⟩

def IndexedEq [DecidableEq τ] [Indexed C₁ τ] [Indexed C₂ τ] (c₁ : C₁) (c₂ : C₂)
  {h : Size.size c₁ = Size.size c₂} : Prop :=
  ∀ i, Indexed.nth c₁ i = Indexed.nth c₂ ⟨i.val, by rw [←h]; exact i.isLt⟩

end IndexedOps

class IndexedOps (C τ) [Indexed C τ] where
  slice (off len : Nat) (c : C)
    {h : off + len ≤ Size.size c} : IndexedOps.Slice C τ

namespace IndexedOps

instance [Indexed C τ] : Inhabited (IndexedOps C τ) where
  default := {
    slice := λ off len c h => ⟨c,off,len,h⟩
  }

instance [Indexed C τ] [Foldable C τ] : FoldableOps C τ
  := { (default : FoldableOps C τ) with
  toList := λ c =>
    let n := Size.size c
    Foldable'.Correct.fold' (Range.mk n) (λ acc i h =>
      Indexed.nth c ⟨n-i-1, by
        simp
        simp [Membership.mem] at h
        rw [Nat.sub_sub]
        apply Nat.sub_lt_of_pos_le
        simp [Nat.add_one, Nat.zero_lt_succ]
        exact h
      ⟩ :: acc
      ) []
  }

theorem toList_eq_range_toList_map [Indexed C τ] (c : C)
  (hL : ∀ {x}, x ∈ canonicalToList (Foldable.fold (Range.mk (Size.size c))) → x < Size.size c)
  : FoldableOps.toList c = (
      canonicalToList (Range.fold ⟨Size.size c⟩)
      |>.map' (fun x h => Indexed.nth c ⟨x, hL h⟩))
  := by
  simp [FoldableOps.toList]
  rw [Foldable'.Correct.fold'Correct]
  -- Rewrite right canonicalToList
  suffices ∀ L (h : L = canonicalToList (Range.fold ⟨Size.size c⟩)) f'
    (h_f' : ∃ (h' : ∀ {x}, x ∈ L → _), ∀ x (h : x ∈ L), f' x h = Indexed.nth c ⟨x, h' h⟩),
    _ = List.map' L f'
    from this _ rfl _ (by
      sorry)
  intro L h f' h_f'
  rw [Range.canonicalToList_eq_toList] at h
  cases h
  -- Rewrite left canonicalToList
  stop
  suffices ∀ L (h : L = canonicalToList fun {β} => Foldable.fold (⟨Size.size c⟩ : Range)),
    List.fold' L _ []
    = _
    from this _ rfl
  sorry

theorem toList_eq_default_toList [Indexed C τ] (c : C)
  : FoldableOps.toList c = (FoldableOps.defaultImpl C τ).toList c
  := by
  conv =>
    rhs
    rw [FoldableOps.default_toList_eq_canonicalToList]
    simp [canonicalToList]
    unfold Foldable.fold
    simp [Foldable.Correct.toFoldable, Foldable'.Correct.toCorrect,
      instCorrectInferInstanceMembershipInstMembership]
    rw [Foldable'.fold'_append_singleton_eq_map]
  rw [toList_eq_range_toList_map]
  case hL =>
    intro i h
    rw [←Foldable'.Correct.memCorrect] at h
    simp [Membership.mem] at h
    assumption
  rfl

@[simp]
theorem length_toList_eq_size {C τ : Type} [Indexed C τ] (c : C)
  : List.length (FoldableOps.toList c) = Size.size c
  := by
  simp [FoldableOps.toList, FoldableOps.defaultImpl,
        Foldable'.fold', Foldable'.Correct.fold']
  apply Range.fold'_ind (motive := λ i _ acc => List.length acc = i)
  simp
  simp

theorem get_toList_eq_get [Indexed C τ] (c : C) (i : Nat) (h : i < _)
  : List.get (FoldableOps.toList c) ⟨i, h⟩ = Indexed.nth c ⟨i, by simp at h; exact h⟩
  := by
  stop
  suffices ∀ l (h_l : l = FoldableOps.toList c) i h, List.get l ⟨i,h⟩ = Indexed.nth c ⟨i, by simp [h_l] at h; exact h⟩ by
    apply this
    rfl
  intro l h_l i h_i
  rw [toList_eq_default_toList] at h_l
  simp [FoldableOps.toList, FoldableOps.defaultImpl,
        Foldable'.fold', Foldable'.Correct.fold',
        canonicalToList, Foldable.fold] at h_l
  have := Range.fold'_ind
    (stop := Size.size c)
    (β := List τ)
    (f := fun acc i h =>
        Indexed.nth c ⟨Size.size c - i - 1, _⟩ :: acc)
    (motive := λ len h acc =>
      (acc.length = len) ∧ (
        (h_acc : acc.length = len) →
        (∀ i, (h_i : i < len) →
          List.get acc ⟨i, h_acc.symm.subst h_i⟩
            = Indexed.nth c ⟨i, Nat.lt_of_lt_of_le h_i h⟩)))
    (by
      simp
      sorry
      )
    (by
      sorry)
  sorry

structure Map (C) [Indexed C τ] where
  val : C

namespace Map

instance [Indexed C τ] : MapLike (Map C) Nat τ where
  fold c f acc :=
    Range.fold' ⟨Size.size c.val⟩ (λ acc i h_i =>
      f acc (i, Indexed.nth c.val ⟨i,h_i⟩)
    ) acc
  get? i c :=
    if h : i < Size.size c.val then
      some (Indexed.nth c.val ⟨i, h⟩)
    else none
