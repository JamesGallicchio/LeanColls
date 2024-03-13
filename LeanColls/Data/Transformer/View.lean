/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes.Ops

/-! ## Views

Views are suspended collection computations.

This allows programmers to avoid producing intermediary values
in a series of collection operations,
which can often produce faster and more memory-efficient code.
-/

namespace LeanColls

namespace View

variable [Fold.{u,v,w} C τ] [ToList C τ] [Fold.ToList C τ]

/-! ## Map -/

structure Map (f : τ → τ') (C) where
  val : C

instance {g : τ → τ'} : Fold (Map g C) τ' where
  fold  := fun ⟨c⟩ f acc => Fold.fold c (fun acc x => f acc (g x)) acc
  foldM := fun ⟨c⟩ f acc => Fold.foldM c (fun acc x => f acc (g x)) acc

instance {g : τ → τ'} : ToList (Map g C) τ' where
  toList := fun ⟨c⟩ => (toList c).map g

instance {g : τ → τ'} : Fold.ToList (Map g C) τ' where
  fold_eq_fold_toList := by
    rintro ⟨c⟩
    have ⟨L, hL, h⟩ := Fold.ToList.fold_eq_fold_toList c
    use L.map g
    simp [fold, toList, hL.map, List.foldl_map, h]
  foldM_eq_fold := by
    intros
    simp [foldM, fold, Fold.ToList.foldM_eq_fold]

def map (f : τ → τ') (c : C) : Map f C := ⟨c⟩

/-! ## Filter -/

structure Filter (f : τ → Bool) (C) where
  val : C

instance {g : τ → Bool} : Fold (Filter g C) τ where
  fold  := fun ⟨c⟩ f acc => Fold.fold c (fun acc x => if g x then f acc x else acc) acc
  foldM := fun ⟨c⟩ f acc => Fold.foldM c (fun acc x => if g x then f acc x else pure acc) acc

instance {g : τ → Bool} : ToList (Filter g C) τ where
  toList := fun ⟨c⟩ => (toList c).filter g

instance {g : τ → Bool} : Fold.ToList (Filter g C) τ where
  fold_eq_fold_toList := by
    rintro ⟨c⟩
    have ⟨L, hL, h⟩ := Fold.ToList.fold_eq_fold_toList c
    use L.filter g
    simp [fold, toList, hL.filter, h]
    intros; rw [List.foldl_filter]
  foldM_eq_fold := by
    intros
    simp [foldM, fold, Fold.ToList.foldM_eq_fold]
    congr; funext acc x
    split <;> simp

def filter (f : τ → Bool) (c : C) : Filter f C := ⟨c⟩

/-! ## FilterMap -/

structure FilterMap (f : τ → Option τ') (C) where
  val : C

instance {g : τ → Option τ'} : Fold (FilterMap g C) τ' where
  fold  := fun ⟨c⟩ f acc =>
    Fold.fold c (fun acc x =>
              match g x with
              | none => acc
              | some x' => f acc x'
          ) acc
  foldM := fun ⟨c⟩ f acc =>
    Fold.foldM c (fun acc x =>
              match g x with
              | none => pure acc
              | some x' => f acc x'
          ) acc

instance {g : τ → Option τ'} : ToList (FilterMap g C) τ' where
  toList := fun ⟨c⟩ => (toList c).filterMap g

instance {g : τ → Option τ'} : Fold.ToList (FilterMap g C) τ' where
  fold_eq_fold_toList := by
    rintro ⟨c⟩
    have ⟨L, hL, h⟩ := Fold.ToList.fold_eq_fold_toList c
    use L.filterMap g
    simp [fold, toList, hL.filterMap, h]
    intros; rw [List.foldl_filterMap]; congr; funext acc x; split <;> simp [*]
  foldM_eq_fold := by
    intros
    simp [foldM, fold, Fold.ToList.foldM_eq_fold]
    congr; funext acc x
    split <;> simp

def filterMap (f : τ → Option τ') (c : C) : FilterMap f C := ⟨c⟩

/-! ## FlatMap -/

section
variable [Fold C' τ'] [ToList C' τ'] [Fold.ToList C' τ']

structure FlatMap (f : τ → C') (C) where
  val : C

instance {g : τ → C'} : Fold (FlatMap g C) τ' where
  fold  := fun ⟨c⟩ f acc => Fold.fold c (fun acc x => Fold.fold (g x) f acc) acc
  foldM := fun ⟨c⟩ f acc => Fold.foldM c (fun acc x => Fold.foldM (g x) f acc) acc

instance {g : τ → C'} : ToList (FlatMap g C) τ' where
  toList := fun ⟨c⟩ => (toList c).bind (toList ∘ g)

instance {g : τ → C'} : Fold.ToList (FlatMap g C) τ' where
  fold_eq_fold_toList := by
    rintro ⟨c⟩
    have ⟨L, hL, h⟩ := Fold.ToList.fold_eq_fold_toList c
    use L.bind (toList ∘ g)
    simp [fold, toList, h, hL.bind_right]
    intros; rw [List.foldl_bind]; congr
    funext acc x
    have ⟨L2, hL2, h2⟩ := Fold.ToList.fold_eq_fold_toList (g x)
    rw [h2]
    sorry -- realizing that the permutations become scuffed here :(
  foldM_eq_fold := by
    intros
    simp [foldM, fold, Fold.ToList.foldM_eq_fold]
    congr; funext acc x
    sorry -- same lemma as is used in Ops.lean Foldable section

def flatMap (f : τ → C') (c : C) : FlatMap f C := ⟨c⟩

end

/-! ## Append -/
section
variable [Fold C₁ τ] [ToList C₁ τ] [Fold.ToList C₁ τ]
         [Fold C₂ τ] [ToList C₂ τ] [Fold.ToList C₂ τ]

structure Append (C₁ C₂) where
  val₁ : C₁
  val₂ : C₂

instance : Fold (Append C₁ C₂) τ where
  fold  := fun ⟨c₁,c₂⟩ f acc => Fold.fold c₁ f acc |> Fold.fold c₂ f
  foldM := fun ⟨c₁,c₂⟩ f acc => Fold.foldM c₁ f acc >>= Fold.foldM c₂ f

instance : ToList (Append C₁ C₂) τ where
  toList := fun ⟨c₁,c₂⟩ => (toList c₁) ++ (toList c₂)

instance : Fold.ToList (Append C₁ C₂) τ where
  fold_eq_fold_toList := by
    rintro ⟨c₁,c₂⟩
    have ⟨L1, hL1, h1⟩ := Fold.ToList.fold_eq_fold_toList c₁
    have ⟨L2, hL2, h2⟩ := Fold.ToList.fold_eq_fold_toList c₂
    use L1 ++ L2
    simp [fold, toList, h1, h2, List.Perm.append hL1 hL2]
  foldM_eq_fold := by
    intros
    simp [foldM, fold, Fold.ToList.foldM_eq_fold]
    sorry -- same lemma as is used in Ops.lean Foldable section?

def append (c₁ : C₁) (c₂ : C₂) : Append C₁ C₂ := ⟨c₁, c₂⟩

instance : HAppend C₁ C₂ (Append C₁ C₂) where
  hAppend v1 v2 := append v1 v2

end
