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
  h_lens : F.length = F_len ∧ R.length = R_len ∧ R_len ≤ F_len

namespace LBQueue

private def model_fn : LBQueue τ → Model τ := λ ⟨F,_,R,_,_⟩ => (F ++ (R.reverse)).toList

def empty : LBQueue τ :=
  ⟨ LazyList.nil, 0,
    LazyList.nil, 0,
    by simp⟩

private def balance (F : LazyList τ) (F_len) (R : LazyList τ) (R_len)
  (h_lens : F.length = F_len ∧ R.length = R_len) :=
  if h : R_len ≤ F_len then
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
      exact Nat.zero_le _
    ⟩

private theorem balance_inv {F : LazyList α} {F_len} {R} {R_len} {h_lens}
  : model_fn (balance F F_len R R_len h_lens) = (F ++ (R.reverse)).toList
  := by
  simp [balance]
  cases (Nat.decLe R_len F_len)
  simp [dite, model_fn]
  simp [dite, model_fn]

def enq (Q : LBQueue τ) (x : τ) : LBQueue τ :=
  let ⟨F, F_len, R, R_len, h_lens⟩ := Q
  balance F F_len (LazyList.cons x R) (1+R_len) (by
    simp
    cases h_lens; case intro l r =>
    simp [l,r, Nat.add_comm]
    )

def deq (Q : LBQueue τ) : Option (τ × LBQueue τ) :=
  let ⟨F, F_len, R, R_len, h_lens⟩ := Q
  match h:F.force with
  | some (x, F') => some (x, balance F' (F_len-1) R R_len (by
      cases h_lens; case intro f_len h_lens =>
      cases h_lens; case intro r_len h_lens =>
      rw [r_len, ←f_len]
      simp
      rw [←LazyList.length_toList,←LazyList.length_toList]
      rw [LazyList.toList_force_some h]
      simp
      rw [Nat.succ_sub_succ]
      rw [Nat.sub_zero]
    ))
  | none => none

instance : Queue (LBQueue τ) τ where
  model := model_fn
  empty := empty
  h_empty := by simp [empty, model_fn]
  enq   := enq
  h_enq := by
    intros c x
    cases c; case mk F F_len R R_len h_lens =>
    simp [enq, balance_inv]
    simp [Model.enq, model_fn]
    rw [←List.append_assoc]
    simp [HAppend.hAppend, Append.append]
  deq   := deq
  h_deq := by
    intro c
    cases c; case mk F F_len R R_len h_lens =>
    cases h_lens; case intro h_flen h_lens =>
    cases h_lens; case intro h_rlen h_lens =>
    cases h':F.force
    case none =>
      have h_flist := LazyList.toList_force_none.mp h'
      simp [←LazyList.length_toList F, h_flist] at h_flen
      rw [←h_rlen, ←h_flen] at h_lens
      have h_lens := Nat.eq_zero_of_le_zero h_lens
      rw [←LazyList.length_toList R] at h_lens
      have h_rlist : LazyList.toList R = [] := by
        cases h_afsoc:LazyList.toList R
        simp
        simp [h_afsoc] at h_lens
      simp [Model.deq, model_fn, h_flist, h_rlist]
      suffices deq ⟨F, F_len, R, R_len, _⟩ = none by
        rw [this]
        simp [Option.map, Option.bind]
      simp [deq]
      sorry
    sorry
end LBQueue
