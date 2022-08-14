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
  if k' = k
  then some t'
  else get? k as

instance : LeanColls.MapLike (AList κ τ) κ τ where
  fold := List.fold
  get? := get?

def set' (k : κ) (t : τ) : AList κ τ → Option τ × AList κ τ
| [] => (none, [(k,t)])
| (k', t') :: as =>
  if k' = k
  then (some t', (k,t) :: as)
  else
    let (old, as') := set' k t as
    (old, (k', t') :: as')
  
def set (k : κ) (t : τ) (as : AList κ τ) := set' k t as |>.snd

theorem get?_set'_eq (k : κ) (t : τ) (as : AList κ τ)
  : get? k (set' k t as).snd = some t
  := by
  induction as with
  | nil =>
    simp [get?, set']
  | cons a as ih =>
    match a with
    | (k',t') =>
    simp [set']
    split
    simp [get?]
    rename ¬ k' = k => h
    simp [get?]
    simp [h]
    exact ih

theorem get?_set_eq (k : κ) (t : τ) (as : AList κ τ)
  : get? k (set k t as) = some t
  := by
  simp [set, get?_set'_eq]

theorem get?_set'_ne (k' k : κ) (t : τ) (as : AList κ τ)
  (h_k : k ≠ k')
  : get? k' (set' k t as).snd = get? k' as
  := by
  induction as with
  | nil =>
    simp [get?, set', h_k]
  | cons a as =>
  match a with
  | (k'', t'') =>
  simp [set']
  split
  case inl =>
    rename k'' = k => h
    cases h
    simp [get?, h_k]
  case inr =>
    simp [get?]
    split
    rfl
    assumption

theorem get?_set_ne (k' k : κ) (t : τ) (as : AList κ τ)
  (h_k : k ≠ k')
  : get? k' (set k t as) = get? k' as
  := by
  simp [set, get?_set'_ne _ _ _ _ h_k]

theorem length_set' (k : κ) (t : τ) (as : AList κ τ)
  : match set' k t as with
  | (some _, as') => as'.length = as.length
  | (none, as') => as'.length = as.length + 1
  := by
  simp
  split
  case h_1 as' h =>
    rename Option τ × AList κ τ => x
    clear x
    induction as generalizing as' with
    | nil =>
      simp [set'] at h
    | cons a as ih =>
      cases a; case mk k' t' =>
      simp [set'] at h
      split at h
      case inl h_k =>
        simp at *
        cases h_k
        simp [←h]
      case inr h_k =>
        simp at *
        cases h; case intro h_l h_r =>
        cases h_r
        simp
        apply ih
        rw [←h_l]
  case h_2 as' h =>
    rename Option τ × AList κ τ => x
    clear x
    induction as generalizing as' with
    | nil =>
      simp [set'] at h
      simp [←h]
    | cons a as ih =>
      cases a; case mk k' t' =>
      simp [set'] at h
      split at h
      case inl h_k =>
        simp at *
      case inr h_k =>
        simp at *
        cases h; case intro h_l h_r =>
        cases h_r
        simp
        apply ih
        rw [←h_l]

end AList