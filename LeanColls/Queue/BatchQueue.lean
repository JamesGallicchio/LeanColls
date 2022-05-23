/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Queue

namespace LeanColls

/-!
# Batched Queues

Amortized O(1) queues, with front list and back list
where the back list is flipped to the front as needed.

Slightly different from Okasaki: `⟨[],[x]⟩` is allowed
and represents the same queue as `⟨[x],[]⟩`

## References

See [Okasaki1996], Figure 3.2
-/
structure BatchQueue (τ) :=
  F : List τ
  B : List τ

namespace BatchQueue

def empty : BatchQueue τ := ⟨[],[]⟩ 

def enq (Q : BatchQueue τ) (x : τ) : BatchQueue τ :=
  match Q with
  | ⟨F,B⟩ => {F := F, B := x::B}

def deq (Q : BatchQueue τ) : Option (τ × BatchQueue τ) :=
  match Q with
  | ⟨F,B⟩ =>
  match F with
  | f::F => some (f, ⟨F,B⟩)
  | [] =>
  match B.reverse with
  | f::F =>  some (f, ⟨F,[]⟩)
  | [] => none

instance : Queue (BatchQueue τ) τ where
  empty := empty
  enq   := enq
  deq   := deq

instance : Queue.CorrectFIFO (instQueueBatchQueue (τ := τ)) where
  model := λ ⟨F,B⟩ => F ++ (B.reverse)
  h_empty := by
    simp [HAppend.hAppend, Append.append, List.append, List.reverse, empty, List.reverseAux]
  h_enq := by
    intros c x
    cases c
    case mk F B =>
    simp [List.isEmpty, List.append, enq, dite, instDecidableEqBool, List.cons]
    rw [←List.append_assoc]
  h_deq := by
    intro c
    cases c
    case mk F B =>
    cases F
    case cons f F =>
      simp [List.front?, Queue.deq, deq, Option.map, Option.bind]
    case nil =>
    cases h : List.reverse B
    case cons f F =>
      simp [List.front?, Queue.deq, deq, Option.map, Option.bind, h]
    case nil =>
      simp [List.front?, Queue.deq, deq, Option.map, Option.bind, h]

end LeanColls.BatchQueue
