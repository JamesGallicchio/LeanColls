/-
Copyright (c) 2021 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Fold

namespace Stream

variable [Stream ρ τ] (s : ρ)

def take (s : ρ) : Nat → List τ × ρ
| 0 => ([], s)
| n+1 =>
  match next? s with
  | none => ([], s)
  | some (x,rest) =>
    let (L,rest) := take rest n
    (x::L, rest)

def isEmpty : Bool :=
  Option.isNone (next? s)

theorem take_empty (n : Nat) :
  isEmpty s → take s n = ([], s)
  := by
  intro h
  cases h_next : next? s
  case some =>
    simp [isEmpty, Option.isNone, h_next] at h
  case none =>
  cases n
  simp [take, h_next]
  simp [take, h_next]

theorem take_adds [Stream ρ τ] (s : ρ) (n₁ n₂ : Nat) :
  match take s n₁ with
  | (L₁, mid) =>
  match take mid n₂ with
  | (L₂, tail) =>
  match take s (n₁ + n₂) with
  | (L, tail') =>
  L₁ ++ L₂ = L ∧ tail = tail'
  := by
  simp
  induction n₁ generalizing s
  case zero =>
    simp [take]
  case succ n ih =>
    cases h : next? s
    case none =>
      have : isEmpty s := by simp [isEmpty, Option.isNone, h]
      simp [take_empty _ _ this]
    case some p =>
    cases p
    case mk elem s' =>
    rw [Nat.succ_add _ _]
    cases ih s'
    case intro l r =>
    simp [take, h, l]
    exact r

def lengthBoundedBy (n : Nat) : Prop :=
  isEmpty (take s n).2

def hasNext : ρ → ρ → Prop
  := λ s1 s2 => ∃ x, next? s1 = some ⟨x,s2⟩

theorem lengthStep {s1 s2 : ρ} (h_steps : hasNext s1 s2)
                    {n : Nat} (h_len : lengthBoundedBy s1 n.succ)
  : lengthBoundedBy s2 n
  := by
  cases h_steps; case intro x h_steps =>
  simp [lengthBoundedBy, take, h_steps] at h_len
  assumption
  
def isFinite : Prop :=
  ∃ n, lengthBoundedBy s n

instance hasNextWF : WellFoundedRelation {s : ρ // isFinite s} where
  rel := λ s1 s2 => hasNext s2.val s1.val
  wf := ⟨λ ⟨s,h⟩ => ⟨⟨s,h⟩, by
    simp
    cases h; case intro w h =>
    induction w generalizing s
    case zero =>
      intro ⟨s',h'⟩ h_next
      simp [hasNext] at h_next
      cases h_next; case intro x h_next =>
      simp [lengthBoundedBy, isEmpty, Option.isNone, take, h_next] at h
    case succ n ih =>
      intro ⟨s',h'⟩ h_next
      simp [hasNext] at h_next
      cases h_next; case intro x h_next =>
      simp [lengthBoundedBy, take, h_next] at h
      have := ih s' h
      exact Acc.intro (⟨s',h'⟩ : {s : ρ // isFinite s}) this
  ⟩⟩

def foldUntil (f : α → τ → ContOrDone φ α) (acc : α)
  : {l : ρ // isFinite l} → ContOrDone φ α
  | ⟨l,h⟩ =>
    match h:next? l with
    | none => ContOrDone.Cont acc
    | some (x,xs) =>
      have h_next : hasNext l xs := by exists x; simp [hasNext, h]
      do
      let acc ← f acc x
      foldUntil f acc ⟨xs, by sorry⟩
  termination_by _ l => l
  decreasing_by
    simp [hasNextWF, InvImage, WellFoundedRelation.rel]
    assumption

instance [S : Stream ρ τ] : FoldUntil {s : ρ // isFinite s} τ := ⟨foldUntil⟩

end Stream
