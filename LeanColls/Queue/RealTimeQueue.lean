/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Queue
import LeanColls.LazyList

namespace LeanColls

/-!
# Real Time Queues

On any sequence of operations, this implementation
provides O(1) `enq` and `deq` (not amortized). However,
the constant is much larger than for `BatchQueue` and
`LazyBatchQueue`.

## References

See [Okasaki1996], Section 4.2

-/
structure RTQueue (τ) :=
  F : LazyList τ
  R : List τ
  S : LazyList τ
  h_lens : F.length = R.length + S.length

namespace RTQueue

private def model_fn : RTQueue τ → List τ :=
  λ ⟨F,R,_,_⟩ => F.toList ++ (R.reverse)

def empty : RTQueue τ :=
  ⟨ LazyList.nil,
    List.nil,
    LazyList.nil,
    by simp
  ⟩

@[inline] private def rotate (f : LazyList τ) (r : τ) (rs : List τ) (a : LazyList τ)
  (h : f.length = rs.length) : LazyList τ :=
  LazyList.delayed (Thunk.mk (λ () =>
    match h_f:f.force with
    | none =>  LazyList.cons r a
    | some (x, f') =>
    match h_r:rs with
    | [] => by
      rw [←LazyList.length_toList] at h
      simp[LazyList.toList_force_some h_f] at h
    | r'::rs' =>
      LazyList.cons x (rotate f' r' rs' (LazyList.cons r a) (by
        rw [←LazyList.length_toList] at h
        rw [LazyList.toList_force_some h_f] at h
        simp at h
        exact h
        ))
      )
  )

private theorem rotate_inv {F : LazyList α} {r R S}
  : (h : _) → (rotate F r R S h).toList = F.toList ++ r :: R.reverse
  := by
  intro h
  unfold rotate
  simp [Thunk.get]
  unfold rotate.match_1
  unfold rotate.match_2
  unfold rotate.proof_1
  unfold rotate.proof_2
  unfold rotate.proof_3
  unfold rotate.proof_4
  induction F using LazyList.ind
  case nil =>
    simp [LazyList.force]
    sorry
  case cons hd tl ih =>
    simp
    sorry
  case delayed F ih =>
    simp
    sorry
  

@[inline] private def balance (F : LazyList τ) (R : List τ) (S : LazyList τ)
  (h_lens : F.length + 1 = R.length + S.length) : RTQueue τ :=
  match h:S.force with
  | some (_, S') =>
    ⟨F, R, S', by
      rw [←@LazyList.length_toList τ S] at h_lens
      rw [LazyList.toList_force_some h] at h_lens
      simp [Nat.add_succ] at h_lens
      assumption
    ⟩
  | none =>
  match R with
  | [] => by
    rw [←LazyList.length_toList S, LazyList.toList_force_none.mp h] at h_lens
    contradiction
  | r::rs =>
    let F' := rotate F r rs LazyList.nil (by
      rw [←@LazyList.length_toList τ S] at h_lens
      rw [LazyList.toList_force_none] at h
      rw [h] at h_lens
      simp at h_lens
      assumption
    )
    ⟨F', List.nil, F', by simp⟩

private theorem balance_inv {F : LazyList α} {R} {S} (h_lens)
  : model_fn (balance F R S h_lens) = F.toList ++ R.reverse
  := by
  simp [balance]
  sorry

def enq (Q : RTQueue τ) (x : τ) : RTQueue τ :=
  let ⟨F, R, S, h_lens⟩ := Q
  balance F (List.cons x R) S (by
    simp [h_lens, Nat.add_one, Nat.succ_add])

def deq (Q : RTQueue τ) : Option (τ × RTQueue τ) :=
  let ⟨F, R, S, h_lens⟩ := Q
  match h:F.force with
  | some (x, F') => some (x, balance F' R S (by
      rw [←h_lens]
      simp
      rw [←LazyList.length_toList,←LazyList.length_toList]
      rw [LazyList.toList_force_some h]
      simp
    ))
  | none => none

instance : Queue (RTQueue τ) τ where
  model := model_fn
  empty := empty
  h_empty := by simp [empty, model_fn]
  enq   := enq
  h_enq := by
    intros c x
    cases c; case mk F R S h_lens =>
    simp [enq, balance_inv]
    simp [List.cons, model_fn]
    rw [←List.append_assoc]
  deq   := deq
  h_deq := by
    intro c
    sorry
    /-cases c; case mk F F_len R R_len h_lens =>
    cases h':F.force
    case none =>
      simp [deq]
      sorry
    sorry-/
end RTQueue
