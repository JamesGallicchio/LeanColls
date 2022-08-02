import LeanColls.FoldableOps
import LeanColls.AuxLemmas

open LeanColls

namespace List

def fold {β} (c : List τ) (f a) := @List.foldl β _ f a c

@[specialize, inline]
def fold' : (l : List τ) → (β → (x : τ) → x ∈ l → β) → β → β :=
  let rec @[specialize,inline] go
    (l : List τ) (f : β → (x : τ) → x ∈ l → β) (acc : β)
    (rest : List τ) (h : ∀ x, x ∈ rest → x ∈ l) : β :=
    match rest with
    | [] => acc
    | x::xs => go l f (f acc x (h x (List.Mem.head _ _))) xs
      (by intros x hxs; exact h _ (List.Mem.tail _ hxs))
  λ l f acc => go l f acc l (by intros; trivial)

theorem fold_eq_fold' (c : List τ) (f : β → τ → β) (acc : β)
  : fold c f acc = fold' c (λ acc x _ => f acc x) acc
  := by
  simp [fold, fold']
  suffices ∀ l h, foldl f acc l = fold'.go c (fun acc x x_1 => f acc x) acc l h from
    this c _
  intro l h
  induction l generalizing acc with
  | nil =>
    simp [foldl, fold'.go]
  | cons x xs ih =>
    simp [foldl, fold'.go]
    apply ih (f acc x)

end List


/-! ## Association Lists -/
def AList (κ τ) := List (κ × τ)

namespace AList

instance [DecidableEq κ] : MapLike (AList κ τ) κ τ where
  fold := List.fold
  get? L k := L.find? (fun (k',_) => k' = k) |>.map Prod.snd

inductive UpdateEffect
| replaced
| inserted

def set [DecidableEq κ] (k : κ) (t : τ) : AList κ τ → UpdateEffect × AList κ τ
| [] => (.inserted, [(k,t)])
| x :: xs =>
  if x.1 = k
  then (.replaced, (k,t) :: xs)
  else
    let (eff, xs') := set k t xs
    (eff, x :: xs')

theorem length_set [DecidableEq κ] (k : κ) (t : τ) (as : AList κ τ)
  : match set k t as with
  | (.replaced, as') => as'.length = as.length
  | (.inserted, as') => as'.length = as.length + 1
  := by
  simp
  split
  case h_1 as' h =>
    rename UpdateEffect × AList κ τ => x
    clear x
    induction as generalizing as' with
    | nil => simp [set] at h
    | cons a as ih =>
      cases a; case mk k' t' =>
      simp [set] at h
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
    rename UpdateEffect × AList κ τ => x
    clear x
    induction as generalizing as' with
    | nil =>
      simp [set] at h
      simp [←h]
    | cons a as ih =>
      cases a; case mk k' t' =>
      simp [set] at h
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