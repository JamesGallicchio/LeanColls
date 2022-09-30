/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes
import LeanColls.Range
import LeanColls.View
import LeanColls.List

namespace LeanColls

namespace IndexedOps

instance [Indexed C τ] : Membership τ C where
  mem x c := ∃ i, x = Indexed.nth c i

instance [Indexed C τ] : Iterable C τ where
  ρ := Σ' (c : C), Iterable'.ρ Nat (Range.mk <| Size.size c)
  toIterator c := ⟨c, Iterable'.toIterator (Range.mk <| Size.size c)⟩
  step := λ ⟨c,r⟩ => Iterable'.step r
                    |>.map (fun (⟨i,h⟩,r) => (Indexed.nth c ⟨i,h⟩, ⟨c,r⟩))

theorem size_pos_iff_mem [Indexed C τ] {c : C}
  : Size.size c > 0 ↔ ∃ x, x ∈ c
  := by
  constructor
  case mp =>
    intro h
    apply Exists.intro (Indexed.nth c ⟨0,h⟩)
    simp [Membership.mem]
    apply Exists.intro ⟨0,h⟩
    rfl
  case mpr =>
    intro h
    cases h; case intro x h =>
    cases h; case intro i _ =>
    exact i.size_positive

instance [Indexed C τ] : Foldable'.Correct C τ inferInstance where
  fold c f init :=
    Foldable'.Correct.fold' (Range.mk <| Size.size c) (λ acc i h =>
      f acc (Indexed.nth c ⟨i,h⟩)
    ) init
  fold' c f init :=
    Foldable'.Correct.fold' (Range.mk <| Size.size c) (λ acc i h =>
      f acc (Indexed.nth c ⟨i,h⟩) ⟨⟨i,h⟩, rfl⟩
    ) init
  foldCorrect := by
    intro β c f acc
    simp [Foldable.fold]
    rw [Foldable'.fold_canonicalToList_fold'_eq_fold']
  memCorrect x c := by
    simp [Foldable.fold, canonicalToList]
    constructor
    case mp =>
      intro h; simp at h; cases h; case intro i h =>
      have := Foldable'.fold'_append_singleton_eq_map
        (⟨Size.size c⟩ : Range)
        (fun i h => Indexed.nth c ⟨i,h⟩)
      simp [Membership.mem] at this ⊢
      simp [this, Foldable.fold]
      rw [List.map'_rw _ (Range.toList_eq_canonicalToList ⟨Size.size c⟩).symm]
      rw [List.map']
      apply (List.mem_of_map_iff _ _ _).mpr
      simp
      cases i; case mk i h_i =>
      have : i ∈ Range.toList ⟨Size.size c⟩ := by
          rw [Range.toList_eq_canonicalToList]
          apply (Range.memCorrect _ _).mp
          assumption
      apply Exists.intro i
      apply Exists.intro this
      simp
      constructor
      case left =>
        simp [List.mem_of_subtypeByMem _ i this]
      case right =>
        exact h.symm
    case mpr =>
      intro h
      rw [Foldable'.Correct.fold'Correct] at h
      rw [List.foldl'_eq_subtypeByMem_foldl] at h
      rw [List.foldl_eq_map] at h
      rw [(List.mem_of_map_iff _ _ _)] at h
      cases h; case intro x h =>
      cases x; case mk i h_i =>
      simp [Membership.mem]
      have h_i' : i < Size.size c := by
        simp [Foldable.fold] at h_i
        rw [←Range.memCorrect] at h_i
        exact h_i
      apply Exists.intro ⟨i, h_i'⟩
      exact h.2.symm
  fold'Correct := by
    intro β c f acc
    simp
    conv => rhs; simp [Foldable'.Correct.fold', Foldable.fold]
    have := Foldable'.canonicalToList_fold'_eq_map'
      (⟨Size.size c⟩ : Range)
      (fun x h => Indexed.nth c ⟨x,h⟩)
    simp [Foldable'.Correct.fold'] at this
    rw [List.foldl'_rw _ _ _ _ this]
    simp [Foldable'.Correct.fold'Correct, List.foldl'_eq_subtypeByMem_foldl]
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

class IndexedOps (C) (τ : Type u) [Indexed C τ] where
  slice (c : C) (off len : Nat)
    {h : off + len ≤ Size.size c} : IndexedOps.Slice C τ
  map (c : C) {τ' : Type u} (f : τ → τ') [Initable C' (Size.size c) τ'] : C'
  findi (c : C) (f : τ → Bool) : Option (Fin (Size.size c) × τ)
  findMapi (c : C) {τ' : Type u} (f : τ → Option τ') : Option (Fin (Size.size c) × τ')

namespace IndexedOps

instance [Indexed C τ] : Inhabited (IndexedOps C τ) where
  default := {
    slice := λ c off len h => ⟨c,off,len,h⟩
    map := λ c _ f => Initable.init (fun i => f (Indexed.nth c i))
    findi := λ c f =>
      View.view' (Range.mk (Size.size c))
      |>.map (fun ⟨i,h⟩ => (⟨i,h⟩ : Fin (Size.size c)))
      |> FoldableOps.find (f := fun i => f (Indexed.nth c i))
      |> Option.map (fun i => (i, Indexed.nth c i))
    findMapi := λ c _ f =>
      View.view' (Range.mk (Size.size c))
      |>.map (fun ⟨i,h⟩ => (⟨i,h⟩ : Fin (Size.size c)))
      |> FoldableOps.findMap (f := fun i =>
        f (Indexed.nth c i) |>.map (fun x => (i, x))
        )
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
      canonicalToList ((⟨Size.size c⟩ : Range).foldl)
      |>.map' (fun x h => Indexed.nth c ⟨x, hL h⟩))
  := by
  simp [FoldableOps.toList]
  rw [Foldable'.Correct.fold'Correct]
  -- Get RHS to Range.foldr'
  suffices ∀ L (h : L = canonicalToList (⟨Size.size c⟩ : Range).foldl) f'
    (h_f' : ∃ (h' : ∀ {x}, x ∈ L → _), ∀ x (h : x ∈ L), f' x h = Indexed.nth c ⟨x, h' h⟩),
    _ = List.map' L f'
    from this _ rfl _ (by
      apply Exists.intro _
      intro x h
      simp
      intro x h
      apply (Range.memCorrect _ _).mpr h
      )
  intro L h f' h_f'
  rw [←Range.toList_eq_canonicalToList] at h
  cases h
  conv =>
    rhs
    rw [←List.foldr'_eq_map']
    rw [←Range.foldr'_correct _ (Range.toList_eq_canonicalToList _)
      (f := fun x h acc =>
        f' x (by
          rw [Range.toList_eq_canonicalToList]
          apply (Range.memCorrect _ _).mp h
        ) :: acc)]
    simp
  -- Get LHS to Range.foldl'
  suffices ∀ L (h : L = canonicalToList fun {β} => Foldable.fold (⟨Size.size c⟩ : Range)),
    List.foldl' L (fun acc x h' =>
      Indexed.nth c ⟨Size.size c - x - 1, by
        have : Size.size c > 0 := by
          rw [h] at h'
          rw [←Foldable'.Correct.memCorrect] at h'
          simp [Membership.mem] at h'
          apply Nat.lt_of_le_of_lt (Nat.zero_le x)
          assumption
        rw [Nat.sub_sub]
        apply Nat.sub_lt
        assumption
        apply Nat.zero_lt_succ
      ⟩ :: acc) []
    = _
    from this _ rfl
  intro L h
  simp [Foldable.fold] at h
  rw [←Range.toList_eq_canonicalToList] at h
  cases h
  conv =>
    lhs
    rw [←Range.foldl'_correct _ (Range.toList_eq_canonicalToList _)
      (f := fun acc x h =>
        Indexed.nth c ⟨Size.size c - x - 1, by rw [Nat.sub_sub]; apply Nat.sub_lt; exact Range.size_pos_of_mem h; apply Nat.zero_lt_succ⟩ :: acc)]
  -- Use range lemma
  rw [Range.foldr'_eq_foldl'_mapped]
  congr
  funext acc x h
  rw [h_f'.2]

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
  rw [toList_eq_default_toList]
  simp [FoldableOps.toList, FoldableOps.defaultImpl, Foldable.fold]
  rw [Foldable'.canonicalToList_fold'_eq_map']
  simp [Foldable.fold]
  rw [←Range.toList_eq_canonicalToList]
  simp

theorem get_toList_eq_get [Indexed C τ] (c : C) (i : Nat) (h : i < _)
  : List.get (FoldableOps.toList c) ⟨i, h⟩ = Indexed.nth c ⟨i, by simp at h; exact h⟩
  := by
  suffices ∀ L (hL : L = FoldableOps.toList c),
    List.get L ⟨i, by rw [hL]; exact h⟩ = _
    from this _ rfl
  intro L hL
  simp at h
  rw [toList_eq_default_toList] at hL
  simp [FoldableOps.defaultImpl, canonicalToList, Foldable.fold, Foldable'.Correct.fold'] at hL
  rw [Range.foldl'_correct _ (Range.toList_eq_canonicalToList _)] at hL
  rw [List.foldl'_eq_map'] at hL
  rw [List.map'] at hL
  cases hL
  simp

structure Map (C) [Indexed C τ] where
  val : C

namespace Map

instance [Indexed C τ] : MapLike (Map C) Nat τ where
  fold c f acc :=
    Range.foldl' ⟨Size.size c.val⟩ (λ acc i h_i =>
      f acc (i, Indexed.nth c.val ⟨i,h_i⟩)
    ) acc
  get? i c :=
    if h : i < Size.size c.val then
      some (Indexed.nth c.val ⟨i, h⟩)
    else none
