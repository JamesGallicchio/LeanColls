/-
Copyright (c) 2021 James Gallicchio.

Authors: James Gallicchio
-/

set_option pp.match false

namespace Stream

variable [Stream ρ τ] (s : ρ)

def drop (s : ρ) : Nat → ρ
| 0 => s
| n+1 =>
  match next? s with
  | none => s
  | some (_,rest) =>
    drop rest n

def isEmpty : Bool :=
  Option.isNone (next? s)

theorem drop_empty (n : Nat) :
  isEmpty s → drop s n = s
  := by
  intro h
  match h_next : next? s with
  | some _ =>
    simp [isEmpty, Option.isNone, h_next] at h
  | none =>
    cases n <;> simp [drop, h_next]

theorem drop_adds [Stream ρ τ] (s : ρ) (n₁ n₂ : Nat) :
  drop (drop s n₁) n₂ = drop s (n₁ + n₂)
  := by
  simp
  induction n₁ generalizing s
  case zero =>
    simp [drop]
  case succ n ih =>
    match h : next? s with
    | none =>
      have : isEmpty s := by simp [isEmpty, Option.isNone, h]
      simp [drop_empty _ _ this]
    | some ⟨_,s'⟩ =>
      rw [Nat.succ_add _ _]
      simp [drop, h]
      exact ih s'

def lengthBoundedBy (n : Nat) : Prop :=
  isEmpty (drop s n)

def hasNext : ρ → ρ → Prop
  := λ s1 s2 => ∃ x, next? s1 = some ⟨x,s2⟩

theorem lengthStep {s1 s2 : ρ} (h_steps : hasNext s1 s2)
                    {n : Nat} (h_len : lengthBoundedBy s1 n.succ)
  : lengthBoundedBy s2 n
  := by
  cases h_steps; case intro x h_steps =>
  simp [lengthBoundedBy, drop, h_steps] at h_len
  assumption
  
def isFinite : Prop :=
  ∃ n, lengthBoundedBy s n

end Stream

class FinStream (ρ : Type u) (τ : outParam (Type v))
  extends Stream ρ τ where
  h_finite : (s : ρ) → Stream.isFinite s

class SizedStream (ρ : Type u) (τ : outParam (Type v))
  extends FinStream ρ τ where
  size : ρ → Nat
  h_size s : Stream.lengthBoundedBy s (size s)
  h_finite s := ⟨size s, h_size s⟩

namespace FinStream
open Stream

instance hasNextWF [FinStream ρ τ] : WellFoundedRelation ρ where
  rel := λ s1 s2 => hasNext s2 s1
  wf := ⟨λ s => ⟨s, by
    cases FinStream.h_finite s; case intro w h =>
    induction w generalizing s
    case zero =>
      intro s' h_next
      apply False.elim
      simp [hasNext] at h_next
      cases h_next; case intro x h_next =>
      simp [lengthBoundedBy, drop, isEmpty, Option.isNone, h_next] at h
    case succ n ih =>
      intro s' h_next
      suffices lengthBoundedBy s' n from
        Acc.intro s' (ih s' this)
      simp [hasNext] at h_next
      cases h_next; case intro _ h_next =>
      simp [lengthBoundedBy, drop, h_next] at h ⊢
      assumption
  ⟩⟩

end FinStream
