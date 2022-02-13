import LeanColls.Queue
import LeanColls.LazyList

/-
Amortized, lazy queue implementation.

Essentially the same as `BQueue`, but amortized costs
are shared across all persistent copies of the queue
by lazily flipping the back of the queue periodically.
-/
structure LBQueue (τ) :=
  F : LazyList τ
  F_len : Nat
  R : LazyList τ
  R_len : Nat
  h_lens : F.length = F_len ∧ R.length = R_len ∧ F_len ≥ R_len

namespace LBQueue

def empty : LBQueue τ :=
  ⟨ LazyList.nil, 0,
    LazyList.nil, 0,
    by simp⟩

private def balance (F : LazyList τ) (F_len) (R : LazyList τ) (R_len)
  (h_lens : F.length = F_len ∧ R.length = R_len) :=
  if h : F_len ≥ R_len then
    (⟨F, F_len, R, R_len,
      by
      cases h_lens
      apply And.intro; assumption;
      apply And.intro; assumption; assumption
    ⟩ : LBQueue τ)
  else
    ⟨ F ++ R.reverse, F_len + R_len,
      LazyList.nil, 0,
      by
      cases h_lens; case intro l r =>
      simp
      apply And.intro
      simp [l, r]
      sorry
    ⟩

def enq (Q : LBQueue τ) (x : τ) : LBQueue τ :=
  let ⟨F, F_len, R, R_len, h_lens⟩ := Q
  balance F F_len (LazyList.cons x R) (1+R_len) (by
    simp
    cases h_lens; case intro l r =>
    simp [l,r, Nat.add_comm]
    )

def deq (Q : LBQueue τ) : Option (τ × LBQueue τ) :=
  let ⟨F, F_len, R, R_len, h_lens⟩ := Q
  match h:F.get with
  | some (x, F) => some (x, balance F (F_len-1) R R_len (by sorry))
  | none => none

instance : Queue (LBQueue τ) τ where
  model := λ ⟨F,_,B,_,_⟩ => (F.toList ++ (B.toList.reverse))
  empty := empty
  h_empty := by sorry
  enq   := enq
  h_enq := by
    intros c x
    cases c
    case mk F F_len R R_len h_lens =>
    simp [List.isEmpty, List.append, enq, dite, instDecidableEqBool, Model.enq]
    sorry
  deq   := deq
  h_deq := by
    intro c
    cases c
    case mk F F_len R R_len h_lens =>
    sorry
end LBQueue
