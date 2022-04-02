/-
Copyright (c) 2021 James Gallicchio.

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

@[inline] private def rotate (f : LazyList τ) (r : List τ) (a : LazyList τ)
  (h : f.length + 1 = r.length) : LazyList τ :=
  LazyList.delayed (Thunk.mk (λ () =>
    match h_r:r with
    | List.nil => False.elim (by simp [List.length] at h; cases h)
    | y::r' =>
    match h_f:f.force with
    | none =>  LazyList.cons y a
    | some (x, f') => LazyList.cons x (rotate f' r' (LazyList.cons y a) (by
      rw [←LazyList.length_toList] at h
      rw [LazyList.toList_force_some h_f] at h
      simp at h
      exact h
      ))
  ))

private theorem rotate_inv {F : LazyList α} {R} {S}
  : (h : _) → (rotate F R S h).toList = F.toList ++ R.reverse
  := by
  induction F using LazyList.ind
  case nil =>
    intro h
    simp at h
    match R with
    | [] => contradiction
    | [x] =>
      unfold rotate
      simp [Thunk.get]
      unfold LazyList.force.match_1
      unfold LazyList.force.proof_1
      unfold LazyList.force.proof_2
      simp [LazyList.force]
      sorry
    | _::_::_ =>
      simp at h
      contradiction
  case cons hd tl ih =>
    intro h
    simp
    sorry
  case delayed F ih =>
    intro h
    simp
    sorry
  case mk fn ih =>
    intro h
    exact ih ()
  

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
    let F' := rotate F R LazyList.nil (by
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
  match S.force with
  | none =>
    simp [dite, model_fn]
  | some _ =>
    simp [dite, model_fn]

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
    simp [Model.enq, model_fn]
    rw [←List.append_assoc]
    simp [HAppend.hAppend, Append.append]
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
