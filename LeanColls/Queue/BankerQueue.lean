import LeanColls.Queue

/-
Amortized O(1) queues, with front list and back list
where the back list is flipped to the front as needed.

Slightly different from Okasaki: `⟨[],[x]⟩` is allowed
and represents the same queue as `⟨[x],[]⟩`
-/
structure BQueue (τ) :=
  F : List τ
  B : List τ

namespace BQueue

def empty : BQueue τ := ⟨[],[]⟩ 

def enq (Q : BQueue τ) (x : τ) : BQueue τ :=
  match Q with
  | ⟨F,B⟩ => {F := F, B := x::B}

def deq (Q : BQueue τ) : Option (τ × BQueue τ) :=
  match Q with
  | ⟨F,B⟩ =>
  match F with
  | f::F => some (f, ⟨F,B⟩)
  | [] =>
  match B.reverse with
  | f::F =>  some (f, ⟨F,[]⟩)
  | [] => none

instance : Queue (BQueue τ) τ where
  model := λ ⟨F,B⟩ => F ++ (B.reverse)
  empty := empty
  h_empty := by
    simp [HAppend.hAppend, Append.append, List.append, List.reverse, empty, List.reverseAux]
  enq   := enq
  h_enq := by
    intros c x
    cases c
    case mk F B =>
    simp [List.isEmpty, List.append, enq, dite, instDecidableEqBool, Model.enq]
    rw [←List.append_assoc]
    simp [HAppend.hAppend, Append.append]
  deq   := deq
  h_deq := by
    intro c
    cases c
    case mk F B =>
    cases F
    case cons f F =>
      simp [Model.deq, deq, Option.map, Option.bind]
    case nil =>
    cases h : List.reverse B
    case cons f F =>
      simp [Model.deq, deq, Option.map, Option.bind, h]
    case nil =>
      simp [Model.deq, deq, Option.map, Option.bind, h]

end BQueue
