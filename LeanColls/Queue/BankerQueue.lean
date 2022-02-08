import LeanColls.Queue

-- Slightly different from Okasaki: `⟨[],[x]⟩` is allowed
structure BQueue (τ) :=
  F : List τ
  B : List τ

namespace BQueue

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

instance : IsQueue (BQueue τ) τ where
  model := λ ⟨F,B⟩ => F ++ (B.reverse)
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
