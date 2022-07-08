import LeanColls.FoldableOps
open LeanColls

namespace List

instance : Foldable (List τ) τ where
  fold := List.foldl

instance : Iterable (List τ) τ where
  ρ := List τ
  step := List.front?
  toIterator := id

instance [BEq τ] : FoldableOps (List τ) τ := default

instance : Enumerable (List τ) τ where
  ρ := List τ
  fromEnumerator := id
  insert := λ
    | none => []
    | some ⟨x,xs⟩ => x::xs
end List

/-! ## Association Lists -/
def AList (κ τ) := List (κ × τ)

namespace AList

instance [DecidableEq κ] : MapLike (AList κ τ) κ τ where
  fold := List.foldl
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