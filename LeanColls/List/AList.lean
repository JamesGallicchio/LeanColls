/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes
import LeanColls.List.Basic

open LeanColls

/-! ## Association Lists -/
def AList (κ τ) := List (κ × τ)

namespace AList

variable [DecidableEq κ]

def get? (k : κ) : AList κ τ → Option τ
| [] => none
| (k', t') :: as =>
  if k = k'
  then some t'
  else get? k as

instance : LeanColls.MapLike (AList κ τ) κ τ where
  fold l := l.foldl
  get? := get?

def update (k : κ) (t : Option τ) : AList κ τ → AList κ τ
| []  => match t with | none => [] | some t => [(k,t)]
| (k', t') :: as =>
  if k = k' then
    match t with
    | none => update k none as
    | some t => (k,t) :: as
  else
    (k', t') :: update k t as

def set (k : κ) (t : τ) (as : AList κ τ) := update k (some t) as

def remove (k : κ) (as : AList κ τ) := update k none as


def getAndUpdate (k : κ) (t : Option τ) : AList κ τ → Option τ × AList κ τ
| []  => match t with | none => (none, []) | some t => (none, [(k,t)])
| (k', t') :: as =>
  if k = k' then
    (t', match t with
    | none => update k none as
    | some t => (k,t) :: as)
  else
    let (old, as') := getAndUpdate k t as
    (old, (k', t') :: as')

def getAndSet (k : κ) (t : τ) (as : AList κ τ) := getAndUpdate k (some t) as

def getAndRemove (k : κ) (as : AList κ τ) := getAndUpdate k none as


@[simp]
theorem getAndUpdate_eq (k t) (as : AList κ τ)
  : getAndUpdate k t as = (get? k as, update k t as)
  := by
  induction as with
  | nil =>
    simp [getAndUpdate, get?, update]
    split <;> simp
  | cons hd tl ih =>
    simp [getAndUpdate, get?, update, ih]
    split <;> simp

@[simp]
theorem getAndSet_eq (k t) (as : AList κ τ)
  : getAndSet k t as = (get? k as, set k t as)
  := by simp [getAndSet, set]

@[simp]
theorem getAndRemove_eq (k) (as : AList κ τ)
  : getAndRemove k as = (get? k as, remove k as)
  := by simp [getAndRemove, remove]


@[simp]
theorem get?_update (k' k : κ) (t : Option τ) (as : AList κ τ)
  : get? k' (update k t as) = if k' = k then t else get? k' as
  := by
  induction as with
  | nil =>
    simp [update]
    split <;> simp [get?]
  | cons hd tl ih =>
    match hd with
    | (hd_k,hd_t) =>
    simp [update]
    split
    case inl h_hd =>
      cases h_hd
      split
      case h_2 =>
        split
        subst_vars; simp [get?]
        case inr h_k =>
        simp [h_k, get?]
      case h_1 =>
        split
        subst_vars; simp at ih; exact ih
        case inr h_k =>
        simp [h_k] at ih
        simp [get?, h_k, ih]
    case inr h_hd =>
      simp [get?]
      split
      case inl h_k' =>
        cases h_k'
        simp [Ne.symm h_hd]
      case inr =>
        assumption

@[simp]
theorem get?_set (k' k : κ) (t : τ) (as : AList κ τ)
  : get? k' (set k t as) = if k' = k then some t else get? k' as
  := by simp [set]

@[simp]
theorem get?_remove (k' k : κ) (as : AList κ τ)
  : get? k' (remove k as) = if k' = k then none else get? k' as
  := by simp [remove]

theorem length_remove (k : κ) (as : AList κ τ)
  : (remove k as).length ≤ as.length
  := by
  unfold remove
  induction as with
  | nil => simp [update]
  | cons hd tl ih =>
    simp [update]
    split
    apply Nat.le_step; assumption
    apply Nat.succ_le_succ; assumption

/-! Number of distinct keys in the map. Runtime is quadratic in the result;
this definition is used in LeanColls for expressing size invariants. -/
def size : AList κ τ → Nat
| [] => 0
| (k,_) :: as =>
  have := Nat.succ_le_succ <| length_remove k as
  1 + size (remove k as)
termination_by size as => as.length

theorem remove_update (k' k : κ) (t : Option τ) (as) (h_ks : k' ≠ k)
  : remove k' (update k t as) = update k t (remove k' as)
  := by
  induction as with
  | nil =>
    cases t <;> simp [update, remove, h_ks]
  | cons hd tl ih =>
    match hd with
    | (hd_k,hd_t) =>
    simp [update]
    split
    case inl h_k =>
      cases h_k
      cases t <;> simp [remove, update, h_ks]
      exact ih
    case inr h_k =>
      simp [remove, update]
      split
      case inl h_k' =>
        cases h_k'
        exact ih
      case inr h_k' =>
        simp [update, h_k]
        congr

theorem size_update (k t) (as : AList κ τ)
  : size (update k t as) + (if (get? k as).isSome then 1 else 0)
    = size as + (if t.isSome then 1 else 0)
  := by
  match as with
  | [] =>
    cases t <;> simp [update, size, remove, get?]
  | (hd_k,hd_t)::tl =>
    simp [update, get?]
    split
    case inl h_hd =>
      cases h_hd
      simp [size, remove]
      cases t
      simp [Nat.add_comm]
      simp [size, remove]
    case inr h_hd =>
    have :=
      have := Nat.succ_le_succ <| length_remove hd_k tl
      size_update k t (remove hd_k tl)
    simp [size]
    split
    case inl h_get =>
      simp [h_hd, h_get, update] at this
      rw [remove_update, Nat.add_assoc, this, Nat.add_assoc]
      exact Ne.symm h_hd
    case inr h_get =>
      simp [h_hd, h_get, set] at this
      rw [remove_update, this]
      simp [add_assoc]
      exact Ne.symm h_hd
termination_by size_update as => as.length


@[simp]
theorem size_set (k : κ) (t : τ) (as : AList κ τ)
  : size (set k t as) =
    if (get? k as).isSome then as.size else as.size + 1
  := by
  simp [set]
  have := size_update k (some t) as
  split
  case inl h_get =>
    simp [h_get] at this
    assumption
  case inr h_get =>
    simp [h_get] at this
    assumption

@[simp]
theorem size_remove (k : κ) (t : τ) (as : AList κ τ)
  : size (remove k as) + 1 =
    if (get? k as).isSome then as.size else as.size + 1
  := by
  simp [remove]
  have := size_update k none as
  split
  case inl h_get =>
    simp [h_get] at this
    assumption
  case inr h_get =>
    simp [h_get] at this
    rw [this]


theorem size_pos_of_get?_some (k : κ) (as : AList κ τ)
  : (get? k as).isSome → size as > 0
  := by
  intro h
  simp [Option.isSome] at h
  split at h <;> try contradiction
  clear h; rename get? _ _ = _ => h
  induction as with
  | nil => contradiction
  | cons hd tl ih =>
    cases hd
    simp [get?] at h
    split at h
    subst_vars; simp [size]
    apply Nat.le_add_right
    simp [size]
    apply Nat.le_add_right
