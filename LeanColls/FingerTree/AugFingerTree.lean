/-
Copyright (c) 2021 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.AuxLemmas

/-!
# Finger Trees

TODO: Describe

## References

See [Matthieu2007], section 4

-/

inductive Digit (τ : Type u) (msr : τ → M) [Monoid M]
| Digit1 : (a : τ) →
            Cached (msr a) → Digit τ msr
| Digit2 : (a : τ) → (b : τ) →
            Cached (msr a ++ msr b) → Digit τ msr
| Digit3 : (a : τ) → (b : τ) → (c : τ) →
            Cached (msr a ++ msr b ++ msr c) → Digit τ msr
| Digit4 : (a : τ) → (b : τ) → (c : τ) → (d : τ) →
            Cached (msr a ++ msr b ++ msr c ++ msr d) → Digit τ msr

namespace Digit
variable {msr : τ → M} [Monoid M] (d : Digit τ msr)

@[inline]
def tryAddLeft (a : τ) (av : Cached (msr a)) (sc : Digit τ msr → α) (fc : τ → τ → τ → τ → α) : α :=
  match d with
  | Digit1 b       v => sc (Digit2 a b ⟨av.1 ++ v.1,by simp [av.2]⟩)
  | Digit2 b c     v => sc (Digit3 a b c ⟨av.1 ++ v.1,by simp [av.2]⟩)
  | Digit3 b c d   v => sc (Digit4 a b c d ⟨av.1 ++ v.1,by simp [av.2]⟩)
  | Digit4 b c d e _ => fc b c d e

@[inline]
def tryFront (sc : τ → Digit τ msr → α) (fc : (a : τ) → Cached (msr a) → α) : α :=
  match d with
  | Digit1 a       v => fc a v
  | Digit2 a b     _ => sc a (Digit1 b (cached (msr b)))
  | Digit3 a b c   _ => sc a (Digit2 b c (cached (msr b ++ msr c)))
  | Digit4 a b c d _ => sc a (Digit3 b c d (cached (msr b ++ msr c ++ msr d)))

@[inline]
def tryAddRight (z : τ) (zv : Cached (msr z)) (sc : Digit τ msr → α) (fc : τ → τ → τ → τ → α) : α :=
  match h':d with
  | Digit1 y       v => sc (Digit2 y z ⟨v.1 ++ zv.1,by simp [zv.2]⟩)
  | Digit2 x y     v => sc (Digit3 x y z ⟨v.1 ++ zv.1,by simp [zv.2]⟩)
  | Digit3 w x y   v => sc (Digit4 w x y z ⟨v.1 ++ zv.1,by simp [zv.2]⟩)
  | Digit4 v w x y _ => fc v w x y

@[inline]
def tryBack (sc : τ → Digit τ msr → α) (fc : (a : τ) → Cached (msr a) → α) : α :=
  match d with
  | Digit1 z       v => fc z v
  | Digit2 y z     v => sc z (Digit1 y (cached (msr y)))
  | Digit3 x y z   v => sc z (Digit2 x y (cached (msr x ++ msr y)))
  | Digit4 w x y z v => sc z (Digit3 w x y (cached (msr w ++ msr x ++ msr y)))

def toList : Digit τ msr → List τ
| Digit1 a       _ => [a]
| Digit2 a b     _ => [a,b]
| Digit3 a b c   _ => [a,b,c]
| Digit4 a b c d _ => [a,b,c,d]


end Digit

open Digit


inductive Node (τ : Type u) (msr : τ → M) [Monoid M]
| Node2 : (a : τ) → (b : τ) →
          Cached (msr a ++ msr b) → Node τ msr
| Node3 : (a : τ) → (b : τ) → (c : τ) →
          Cached (msr a ++ msr b ++ msr c) → Node τ msr

namespace Node

def toDigit {msr : τ → M} [Monoid M] : Node τ msr → Digit τ msr
| Node2 a b   => Digit.Digit2 a b (cached (msr a ++ msr b))
| Node3 a b c => Digit.Digit3 a b c (cached (msr a ++ msr b ++ msr c))

def toList {msr : τ → M} [Monoid M] : Node τ msr → List τ
| Node2 a b   => [a,b]
| Node3 a b c => [a,b,c]

end  Node

open Node


inductive FingerTree [Monoid M] : (τ : Type u) → (msr : τ → M) → Type (u+3000)
| Empty : FingerTree τ msr
| Single : (t : τ) → FingerTree τ msr 
| Deep : Digit τ msr → FingerTree (Node τ) msr → Digit τ msr → FingerTree τ msr

namespace FingerTree

def toList : FingerTree τ → List τ
| Empty => []
| Single x => [x]
| Deep pr tr sf => pr.toList ++ (tr.toList.bind Node.toList) ++ sf.toList

@[inline]
def cons (f : FingerTree τ) (a : τ) : FingerTree τ :=
  match f with
  | Empty => Single a
  | Single b => Deep (Digit1 a) Empty (Digit1 b)
  | Deep pr tr sf =>
    tryAddLeft pr a
      (λ pr' => Deep pr' tr sf)
      (λ b c d e => Deep (Digit2 a b) (tr.cons (Node3 c d e)) sf)

@[inline]
def front? (f : FingerTree τ) : Option (τ × FingerTree τ) :=
  match f with
  | Empty         => none
  | Single a      => some (a, Empty)
  | Deep pr tr sf => some (
    tryFront pr
      (λ a pr' => (a, Deep pr' tr sf))
      (λ a => /- pr = Digit1 a -/ (a,
        match front? tr with
        | some (n, tr') => Deep n.toDigit tr' sf
        | none => /- tr empty -/
          tryFront sf
            (λ b sf' => Deep (Digit1 b) Empty sf')
            (λ b => /- sf = Digit1 b -/
              Single b))))

theorem toList_cons (f : FingerTree τ) (a : τ)
  : (f.cons a).toList = a :: f.toList
  := by
  induction f
  simp [cons, toList]
  simp [cons, toList, Digit.toList, List.bind, List.map, List.join]
  case Deep pr tr sf ih =>
  simp [cons, tryAddLeft]
  split
  simp [toList, Digit.toList, List.bind, List.map, List.join]
  simp [toList, Digit.toList, List.bind, List.map, List.join]
  simp [toList, Digit.toList, List.bind, List.map, List.join]
  case h_4 b c d e =>
  simp [toList, Digit.toList, List.bind, List.map, List.join, ih]
  split
  simp [toList, Digit.toList, Node.toList, List.bind, List.map, List.join]
  simp [toList, Digit.toList, Node.toList, List.bind, List.map, List.join]
  simp [toList, Digit.toList, Node.toList, List.bind, List.map, List.join]
  simp [toList, Digit.toList, Node.toList, List.bind, List.map, List.join]

theorem toList_front (f : FingerTree τ)
  : f.front?.map (λ (a,f') => (a,f'.toList)) = f.toList.front?
  := by
  induction f
  simp [front?, toList, List.front?, Option.map, Option.bind]
  simp [front?, toList, List.front?, Option.map, Option.bind]
  case Deep pr tr sf ih =>
  match pr with
  | Digit2 a b     => simp [front?, toList, List.front?, tryFront, Option.map, Option.bind, HAppend.hAppend, Append.append, List.append]
  | Digit3 a b c   => simp [front?, toList, List.front?, tryFront, Option.map, Option.bind, HAppend.hAppend, Append.append, List.append]
  | Digit4 a b c d => simp [front?, toList, List.front?, tryFront, Option.map, Option.bind, HAppend.hAppend, Append.append, List.append]
  | Digit1 a =>
    match h:front? tr with
    | some (t,tr') =>
      rw [h] at ih
      simp [Option.map, Option.bind, List.front?] at ih
      split at ih
      contradiction
      case h_2 h_tr x =>
      cases x
      simp [h,h_tr,front?, toList, List.front?, tryFront, Option.map, Option.bind, HAppend.hAppend, Append.append, List.append, List.bind, List.map, List.join]
      cases t
      repeat {simp [Digit.toList, Node.toDigit, Node.toList]}
    | none =>
      rw [h] at ih
      simp [Option.map, Option.bind, List.front?] at ih
      split at ih
      focus {
        case h_1 h_tr x =>
        simp [h,h_tr,front?, toList, List.front?, tryFront, Option.map, Option.bind, HAppend.hAppend, Append.append, List.append, List.bind, List.map, List.join]
        split
        simp [Digit.toList, toList, List.bind, List.join, List.map]
        simp [Digit.toList, toList, List.bind, List.join, List.map]
        simp [Digit.toList, toList, List.bind, List.join, List.map]
        simp [Digit.toList, toList, List.bind, List.join, List.map]
      }
      contradiction

def snoc (f : FingerTree τ) (z : τ) : FingerTree τ :=
  match f with
  | Empty => Single z
  | Single b => Deep (Digit1 b) Empty (Digit1 z)
  | Deep pr tr sf =>
    tryAddRight sf z
      (λ sf' => Deep pr tr sf')
      (λ a b c d => Deep pr (tr.snoc (Node3 a b c)) (Digit2 d z))

def back? (f : FingerTree τ) : Option (FingerTree τ × τ) :=
  match f with
  | Empty         => none
  | Single z      => some (Empty, z)
  | Deep pr tr sf => some (
    tryBack pr
      (λ z sf' => (Deep pr tr sf', z))
      (λ z => /- sf = Digit1 z -/ (
        match back? tr with
        | some (tr', n) => Deep pr tr' n.toDigit
        | none => /- tr empty -/
          tryBack pr
            (λ y pr' => Deep pr' Empty (Digit1 y))
            (λ y => /- pr = Digit1 y -/
              Single y),
        z)))

theorem toList_snoc (f : FingerTree τ) (a : τ)
  : (f.snoc a).toList = f.toList.concat a
  := by
  induction f
  simp [snoc, toList, List.concat]
  simp [snoc, toList, Digit.toList, List.bind, List.map, List.join, List.concat]
  case Deep pr tr sf ih =>
  simp [snoc, tryAddRight]
  split
  simp [toList, Digit.toList, List.bind, List.map, List.join, List.concat_append, List.concat]
  simp [toList, Digit.toList, List.bind, List.map, List.join, List.concat_append, List.concat]
  simp [toList, Digit.toList, List.bind, List.map, List.join, List.concat_append, List.concat]
  case h_4 b c d e =>
  simp [toList, Digit.toList, List.bind, List.map, List.join, ih, List.concat_append, List.concat]
  split
  simp [toList, Digit.toList, Node.toList, List.bind, List.map, List.join, List.concat_append, List.concat, List.map_concat, List.join_concat, List.append_assoc]
  simp [toList, Digit.toList, Node.toList, List.bind, List.map, List.join, List.concat_append, List.concat, List.map_concat, List.join_concat, List.append_assoc]
  simp [toList, Digit.toList, Node.toList, List.bind, List.map, List.join, List.concat_append, List.concat, List.map_concat, List.join_concat, List.append_assoc]
  simp [toList, Digit.toList, Node.toList, List.bind, List.map, List.join, List.concat_append, List.concat, List.map_concat, List.join_concat, List.append_assoc]

theorem toList_back (f : FingerTree τ)
  : f.back?.map (λ (f',a) => (f'.toList,a)) = f.toList.back?
  := by sorry


def append (f1 f2 : FingerTree τ) : FingerTree τ :=
  match f1, f2 with
  | f1, Empty => f1
  | Empty, f2 => f2
  | f1, Single z => f1.snoc z
  | Single a, f1 => f1.cons a
  | Deep pr1 tr1 sf1, Deep pr2 tr2 sf2 =>
    let tr' := match sf1, pr2 with
    | Digit1 a, Digit1 b => (tr1.snoc (Node2 a b)).append tr2
    | Digit2 a b, Digit1 c => (tr1.snoc (Node3 a b c)).append tr2
    | Digit1 a, Digit2 b c => tr1.append (tr2.cons (Node3 a b c))
    | Digit3 a b c, Digit1 d => (tr1.snoc (Node2 a b)).append (tr2.cons (Node2 c d))
    | Digit2 a b, Digit2 c d => (tr1.snoc (Node2 a b)).append (tr2.cons (Node2 c d))
    | Digit1 a, Digit3 b c d => (tr1.snoc (Node2 a b)).append (tr2.cons (Node2 c d))
    | Digit4 a b c d, Digit1 e => (tr1.snoc (Node3 a b c)).append (tr2.cons (Node2 d e))
    | Digit3 a b c, Digit2 d e => (tr1.snoc (Node3 a b c)).append (tr2.cons (Node2 d e))
    | Digit2 a b, Digit3 c d e => (tr1.snoc (Node2 a b)).append (tr2.cons (Node3 c d e))
    | Digit1 a, Digit4 b c d e => (tr1.snoc (Node2 a b)).append (tr2.cons (Node3 c d e))
    | Digit4 a b c d, Digit2 e f => (tr1.snoc (Node3 a b c)).append (tr2.cons (Node3 d e f))
    | Digit3 a b c, Digit3 d e f => (tr1.snoc (Node3 a b c)).append (tr2.cons (Node3 d e f))
    | Digit2 a b, Digit4 c d e f => (tr1.snoc (Node3 a b c)).append (tr2.cons (Node3 d e f))
    | Digit4 a b c d, Digit3 e f g => (tr1.snoc (Node3 a b c)).append ((tr2.cons (Node2 f g)).cons (Node2 d e))
    | Digit3 a b c, Digit4 d e f g => ((tr1.snoc (Node2 a b)).snoc (Node2 c d)).append (tr2.cons (Node3 e f g))
    | Digit4 a b c d, Digit4 e f g h => (tr1.snoc (Node3 a b c)).append ((tr2.cons (Node3 f g h)).cons (Node2 d e))

    Deep pr1 tr' sf2

end FingerTree