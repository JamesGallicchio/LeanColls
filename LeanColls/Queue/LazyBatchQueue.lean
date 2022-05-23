/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Queue
import LeanColls.LazyList

namespace LeanColls

/-!
# Lazy Batched Queues

Amortized, lazy queue implementation.

Essentially the same as `BatchQueue`, but amortized costs
are shared across all persistent copies of the queue
by lazily flipping the back of the queue periodically.

## References

See [Okasaki1996], Section 3.4.2

-/
structure LazyBatchQueue (τ) :=
  F : LazyList τ
  F_len : Nat
  R : LazyList τ
  R_len : Nat
  h_lens : F.length = F_len ∧ R.length = R_len ∧ R_len ≤ F_len

namespace LazyBatchQueue

private def model_fn : LazyBatchQueue τ → List τ := λ ⟨F,_,R,_,_⟩ => (F ++ (R.reverse)).toList

def empty : LazyBatchQueue τ :=
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
    ⟩ : LazyBatchQueue τ)
  else
    ⟨ F ++ R.reverse, F_len + R_len,
      LazyList.nil, 0,
      by
      cases h_lens; case intro l r =>
      simp
      simp [l, r]
    ⟩

private theorem balance_inv {F : LazyList α} {F_len} {R} {R_len} {h_lens}
  : model_fn (balance F F_len R R_len h_lens) = (F ++ (R.reverse)).toList
  := by
  simp [balance]
  cases (Nat.decLe R_len F_len)
  simp [dite, model_fn]
  simp [dite, model_fn]

def enq (Q : LazyBatchQueue τ) (x : τ) : LazyBatchQueue τ :=
  let ⟨F, F_len, R, R_len, h_lens⟩ := Q
  balance F F_len (LazyList.cons x R) (1+R_len) (by
    simp
    cases h_lens; case intro l r =>
    simp [l,r, Nat.add_comm]
    )

def deq (Q : LazyBatchQueue τ) : Option (τ × LazyBatchQueue τ) :=
  let ⟨F, F_len, R, R_len, h_lens⟩ := Q
  match h:F.force with
  | some (x, F') => some (x, balance F' (F_len-1) R R_len (by
      rw [←LazyList.length_toList, LazyList.toList_force_some h] at h_lens
      simp at h_lens
      rw [←h_lens.1, h_lens.2.1]
      simp [Nat.succ_sub_succ, Nat.sub_zero]
    ))
  | none => none


instance : Queue (LazyBatchQueue τ) τ where
  empty := empty
  enq   := enq
  deq   := deq

instance : instQueueLazyBatchQueue.CorrectFIFO (τ := τ) where
  model := model_fn
  h_empty := by simp [empty, model_fn]
  h_enq := by
    intros c x
    cases c; case mk F F_len R R_len h_lens =>
    simp [Queue.enq, enq, balance_inv]
    simp [model_fn]
    rw [←List.append_assoc]
  h_deq := by
    intro c
    cases c; case mk F F_len R R_len h_lens =>
    simp [Queue.deq, deq]
    match h_lens with
    | ⟨hf, hr, h_lens'⟩ =>
    split
    case h_2 h =>
      simp [Option.map, Option.bind, model_fn]
      have hF : F.toList = []
        := LazyList.toList_force_none.mp h
      have hFL : F_len = 0
        := by
        rw [←LazyList.length_toList] at hf
        simp [hF] at hf
        exact hf.symm
      have hRL : R_len = 0
        := by
        rw [hFL] at h_lens'
        exact Nat.eq_zero_of_le_zero h_lens'
      have hR : R.toList = []
        := by
        rw [hRL] at hr
        rw [←LazyList.length_toList] at hr
        unfold List.length at hr
        split at hr
        assumption
        contradiction
      simp [hF, hR, List.front?]
    case h_1 x F' h =>
      simp [Option.map, Option.bind, model_fn]
      have hF : F.toList = x :: F'.toList
        := LazyList.toList_force_some h
      simp [hF, List.front?]
      suffices _ by
        have := @balance_inv _ F' (F_len-1) R R_len this
        simp [model_fn] at this
        exact this.symm

end LazyBatchQueue
