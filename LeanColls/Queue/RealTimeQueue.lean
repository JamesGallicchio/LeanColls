/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Queue
import LeanColls.LazyList
import LeanColls.AuxLemmas

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

private theorem rotate_inv {F : LazyList α} {r rs acc}
  : (h : _) → (rotate F r rs acc h).toList = F.toList ++ rs.reverse ++ [r] ++ acc.toList
  := by
  intro h
  induction rs generalizing F r acc
  case nil =>
    have : F.toList = [] := by
      generalize hFl : F.toList = Fl
      rw [←LazyList.length_toList, hFl] at h
      match Fl with
      | [] => rfl
      | _ :: _ => simp at h
    unfold rotate
    simp [LazyList.force, Thunk.get]
    split
    case h_2 heq =>
      contradiction
    case h_1 =>
      simp [this]
  case cons hd tl ih =>
    have : ∃ x F', F.toList = x :: F' := by
      rw [←LazyList.length_toList] at h
      match hList : F.toList with
      | [] => rw [hList] at h; contradiction
      | x::F' => exact ⟨x,⟨F',rfl⟩⟩
    match this with
    | ⟨x, ⟨F', h⟩⟩ =>
    unfold rotate
    simp [Thunk.get]
    split
    case h_1 heq =>
      rw [LazyList.toList_force_none.mp heq] at h
      contradiction
    case h_2 x F' heq =>
      simp [this, ih]
      rw [LazyList.toList_force_some heq]
      rw [List.append_cons]
      simp [List.append_assoc]
  

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
  split
  case h_1 _ S' heq =>
    simp [model_fn]
  case h_2 heq =>
    split
    case h_1 x y h_lens =>
      rw [←LazyList.length_toList S, LazyList.toList_force_none.mp heq] at h_lens
      contradiction
    case h_2 =>
      simp [model_fn, rotate_inv, List.append_assoc]

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
  empty := empty
  enq   := enq
  deq   := deq

instance : Queue.CorrectFIFO (@instQueueRTQueue τ) where
  model := model_fn
  h_empty := by simp [empty, model_fn]
  h_enq := by
    intros c x
    cases c; case mk F R S h_lens =>
    simp [Queue.enq, enq, balance_inv]
    simp [List.cons, model_fn]
    rw [←List.append_assoc]
  h_deq := by
    intro c
    cases c; case mk F R S h_lens =>
    simp [Queue.deq, deq]
    split
    case h_1 x S' hF =>
      simp [Option.map, Option.bind, balance_inv]
      simp [model_fn, LazyList.toList_force_some hF]
    case h_2 hF =>
      simp [Option.map, Option.bind, model_fn]
      simp [LazyList.toList_force_none.mp hF]
      suffices R = [] by
        simp [this, List.front?]
      suffices List.length R = 0 by
        cases R; simp; contradiction
      have : LazyList.length F = 0 := by
        rw [←LazyList.length_toList, LazyList.toList_force_none.mp hF]
        simp
      rw [this] at h_lens
      have := Nat.eq_zero_of_add_eq_zero h_lens.symm
      exact this.left
