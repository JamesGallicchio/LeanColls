/-
Copyright (c) 2021 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.AuxLemmas

/-!
# Finger Trees

TODO: Describe

## References

See [Sozeau2007], section 4 and [Claessen2020]

-/

inductive Digit (τ : Type u)
| _1 : τ → Digit τ
| _2 : τ → τ → Digit τ
| _3 : τ → τ → τ → Digit τ

namespace Digit

@[inline]
def tryAddLeft (d : Digit τ) (a : τ) (sc : Digit τ → α) (fc : τ → τ → τ → α) : α :=
  match d with
  | _1 b     => sc (_2 a b)
  | _2 b c   => sc (_3 a b c)
  | _3 b c d => fc b c d

@[inline]
def tryFront (d : Digit τ) (sc : τ → Digit τ → α) (fc : τ → α) : α :=
  match d with
  | _1 a       => fc a
  | _2 a b     => sc a (_1 b)
  | _3 a b c   => sc a (_2 b c)

@[inline]
def tryAddRight (d : Digit τ) (z : τ) (sc : Digit τ → α) (fc : τ → τ → τ → α) : α :=
  match h':d with
  | _1 y        => sc (_2 y z)
  | _2 x y      => sc (_3 x y z)
  | _3 w x y  => fc w x y

@[inline]
def tryBack (d : Digit τ) (sc : τ → Digit τ → α) (fc : τ → α) : α :=
  match d with
  | _1 z       => fc z
  | _2 y z     => sc z (_1 y)
  | _3 x y z   => sc z (_2 x y)

def toList : Digit τ → List τ
| _1 a       => [a]
| _2 a b     => [a,b]
| _3 a b c   => [a,b,c]

end Digit


inductive Node (τ : Type u)
| _2 : τ → τ → Node τ 
| _3 : τ → τ → τ → Node τ

namespace Node

def toDigit : Node τ → Digit τ
| _2 a b => Digit._2 a b
| _3 a b c => Digit._3 a b c

def toList : Node τ → List τ
| _2 a b     => [a,b]
| _3 a b c   => [a,b,c]

theorem toList_toDigit {n : Node τ}
  : n.toDigit.toList = n.toList
  := by
  cases n
  repeat { simp [Digit.toList, toDigit, toList] }

end Node

open Node

def NodeTree (τ : Type u) : Nat → Type u
| 0 => τ
| (n+1) => Node (NodeTree τ n)


inductive FingerTree (τ : Type u) : (n : Nat) → Type u
| Empty : FingerTree τ n
| Single : NodeTree τ n → FingerTree τ n
| Deep : Digit (NodeTree τ n) → FingerTree τ (n+1) → Digit (NodeTree τ n) → FingerTree τ n

namespace FingerTree

def empty : FingerTree τ 0 := Empty

def toList : FingerTree τ n → List (NodeTree τ n)
| Empty => []
| Single x => [x]
| Deep pr tr sf =>
  pr.toList ++
  (tr.toList.bind Node.toList : List (NodeTree τ n)) ++
  sf.toList

@[inline]
def cons (f : FingerTree τ n) (a : NodeTree τ n) : FingerTree τ n :=
  match f with
  | Empty => Single a
  | Single b => Deep (Digit._1 a) Empty (Digit._1 b)
  | Deep pr tr sf =>
    Digit.tryAddLeft pr a
      (λ pr' => Deep pr' tr sf)
      (λ b c d => Deep (Digit._2 a b) (tr.cons (Node._2 c d)) sf)

@[inline]
def front? (f : FingerTree τ n) : Option (NodeTree τ n × FingerTree τ n) :=
  match f with
  | Empty         => none
  | Single a      => some (a, Empty)
  | Deep pr tr sf => some (
    Digit.tryFront pr
      (λ a pr' => (a, Deep pr' tr sf))
      (λ a => /- pr = Digit1 a -/ (a,
        match front? tr with
        | some (n, tr') => Deep n.toDigit tr' sf
        | none => /- tr empty -/
          Digit.tryFront sf
            (λ b sf' => Deep (Digit._1 b) Empty sf')
            (λ b => /- sf = Digit1 b -/
              Single b))))

theorem toList_cons (f : FingerTree τ n) (a : NodeTree τ n)
  : (f.cons a).toList = a :: f.toList
  := by
  induction f
  simp [cons, toList]
  simp [cons, toList, Digit.toList, List.bind, List.map, List.join]
  case Deep pr tr sf ih =>
  simp [cons, Digit.tryAddLeft]
  split
  simp [toList, Digit.toList, List.bind, List.map, List.join]
  simp [toList, Digit.toList, List.bind, List.map, List.join]
  case h_3 b c d =>
  simp [toList, Digit.toList, List.bind, List.map, List.join, ih]
  split
  simp [toList, Digit.toList, Node.toList, List.bind, List.map, List.join]
  simp [toList, Digit.toList, Node.toList, List.bind, List.map, List.join]
  simp [toList, Digit.toList, Node.toList, List.bind, List.map, List.join]

theorem toList_front (f : FingerTree τ n)
  : f.front?.map (λ (a,f') => (a,f'.toList)) = f.toList.front?
  := by
  induction f
  simp [front?, toList, List.front?, Option.map, Option.bind]
  simp [front?, toList, List.front?, Option.map, Option.bind]
  case Deep pr tr sf ih =>
  match pr with
  | Digit._2 a b     => simp [front?, toList, List.front?, Digit.tryFront, Option.map, Option.bind, HAppend.hAppend, Append.append, List.append]
  | Digit._3 a b c   => simp [front?, toList, List.front?, Digit.tryFront, Option.map, Option.bind, HAppend.hAppend, Append.append, List.append]
  | Digit._1 a =>
    match h:front? tr with
    | some (t,tr') =>
      rw [h] at ih
      simp [Option.map, Option.bind, List.front?] at ih
      split at ih
      contradiction
      case h_2 x h_tr =>
      cases ih
      simp [h,h_tr,front?, toList, List.front?, Digit.tryFront, Option.map, Option.bind, HAppend.hAppend, Append.append, List.append, List.bind, List.map, List.join]
      cases t
      repeat {simp [Digit.toList, Node.toDigit, Node.toList]}
    | none =>
      rw [h] at ih
      simp [Option.map, Option.bind, List.front?] at ih
      split at ih
      focus {
        case h_1 x h_tr =>
        simp [h,h_tr,front?, toList, List.front?, Digit.tryFront, Option.map, Option.bind, HAppend.hAppend, Append.append, List.append, List.bind, List.map, List.join]
        split
        repeat { simp [Digit.toList, toList, List.bind, List.join, List.map] }
      }
      contradiction

def snoc (f : FingerTree τ n) (z : NodeTree τ n) : FingerTree τ n :=
  match f with
  | Empty => Single z
  | Single b => Deep (Digit._1 b) Empty (Digit._1 z)
  | Deep pr tr sf =>
    Digit.tryAddRight sf z
      (λ sf' => Deep pr tr sf')
      (λ a b c => Deep pr (tr.snoc (Node._3 a b c)) (Digit._1 z))

def back? (f : FingerTree τ n) : Option (FingerTree τ n × NodeTree τ n) :=
  match f with
  | Empty         => none
  | Single z      => some (Empty, z)
  | Deep pr tr sf => some (
    Digit.tryBack sf
      (λ z sf' => (Deep pr tr sf', z))
      (λ z => /- sf = Digit1 z -/ (
        match back? tr with
        | some (tr', n) => Deep pr tr' n.toDigit
        | none => /- tr empty -/
          Digit.tryBack pr
            (λ y pr' => Deep pr' Empty (Digit._1 y))
            (λ y => /- pr = Digit1 y -/
              Single y),
        z)))

theorem toList_snoc (f : FingerTree τ n) (a : NodeTree τ n)
  : (f.snoc a).toList = f.toList.concat a
  := by
  induction f
  simp [snoc, toList, List.concat]
  simp [snoc, toList, Digit.toList, List.bind, List.map, List.join, List.concat]
  case Deep pr tr sf ih =>
  simp [snoc, Digit.tryAddRight]
  split
  simp [toList, Digit.toList, List.bind, List.map, List.join, List.concat_append, List.concat]
  simp [toList, Digit.toList, List.bind, List.map, List.join, List.concat_append, List.concat]
  case h_3 b c d e =>
  simp [toList, Digit.toList, List.bind, List.map, List.join, ih, List.concat_append, List.concat]
  split
  simp [toList, Digit.toList, Node.toList, List.bind, List.map, List.join, List.concat_append, List.concat, List.map_concat, List.join_concat, List.append_assoc]
  simp [toList, Digit.toList, Node.toList, List.bind, List.map, List.join, List.concat_append, List.concat, List.map_concat, List.join_concat, List.append_assoc]
  simp [toList, Digit.toList, Node.toList, List.bind, List.map, List.join, List.concat_append, List.concat, List.map_concat, List.join_concat, List.append_assoc]

theorem toList_back (f : FingerTree τ n)
  : f.back?.map (λ (f',a) => (f'.toList,a)) = f.toList.back?
  := by
  induction f
  simp [back?, toList, List.back?, Option.map, Option.bind]
  simp [back?, toList, List.back?, Option.map, Option.bind]
  case Deep pr tr sf ih =>
  match sf with
  | Digit._2 a b =>
    simp [toList, Digit.toList]
    have : [a,b] = [a].concat b := by rfl
    rw [this, ←List.concat_append, List.back_concat]
    simp [back?, Option.map, Option.bind, Digit.tryBack, toList, Digit.toList]
  | Digit._3 a b c =>
    simp [toList, Digit.toList]
    have : [a,b,c] = [a,b].concat c := by rfl
    rw [this, ←List.concat_append, List.back_concat]
    simp [back?, Option.map, Option.bind, Digit.tryBack, toList, Digit.toList]
  | Digit._1 a =>
    match h:back? tr with
    | some (tr',t) =>
      rw [h] at ih
      simp [Option.map, Option.bind] at ih
      have : toList tr = (toList tr').concat t :=
        (List.back_some_iff_concat _).mp ih.symm
      simp [this, back?, Digit.tryBack, Option.map, Option.bind, h, toList]
      have : Digit.toList (Digit._1 a) = [].concat a := by rfl
      rw [this]
      rw [←List.concat_append,List.back_concat]
      simp [List.bind, Node.toList_toDigit, List.append_assoc]
    | none =>
      rw [h] at ih
      simp [Option.map, Option.bind] at ih
      have : tr = Empty := by
        match tr with
        | Empty => rfl
        | Single _ => contradiction
        | Deep _ _ _ => contradiction
      simp [Option.map, Option.bind, back?, this, Digit.tryBack]
      simp [toList, Digit.toList, List.bind, List.map, List.join]
      have : [a] = [].concat a := by rfl
      rw [this]
      rw [←List.concat_append,List.back_concat]
      simp
      split
      repeat { simp [Digit.toList, toList, List.bind, List.join, List.map] }


def append (f1 f2 : FingerTree τ n) : FingerTree τ n :=
  match f1, f2 with
  | f1, Empty => f1
  | Empty, f2 => f2
  | f1, Single z => f1.snoc z
  | Single a, f1 => f1.cons a
  | Deep pr1 tr1 sf1, Deep pr2 tr2 sf2 =>
    let tr' := match sf1, pr2 with
    | Digit._1 a,     Digit._1 b     => (tr1.snoc (Node._2 a b)).append tr2
    | Digit._2 a b,   Digit._1 c     => (tr1.snoc (Node._3 a b c)).append tr2
    | Digit._1 a,     Digit._2 b c   => tr1.append (tr2.cons (Node._3 a b c))
    | Digit._3 a b c, Digit._1 d     => (tr1.snoc (Node._2 a b)).append (tr2.cons (Node._2 c d))
    | Digit._2 a b,   Digit._2 c d   => (tr1.snoc (Node._2 a b)).append (tr2.cons (Node._2 c d))
    | Digit._1 a,     Digit._3 b c d => (tr1.snoc (Node._2 a b)).append (tr2.cons (Node._2 c d))
    | Digit._3 a b c, Digit._2 d e   => (tr1.snoc (Node._3 a b c)).append (tr2.cons (Node._2 d e))
    | Digit._2 a b,   Digit._3 c d e => (tr1.snoc (Node._2 a b)).append (tr2.cons (Node._3 c d e))
    | Digit._3 a b c, Digit._3 d e f => (tr1.snoc (Node._3 a b c)).append (tr2.cons (Node._3 d e f))

    Deep pr1 tr' sf2
  termination_by _ f1 f2 => sizeOf (f1,f2)
  decreasing_by sorry

end FingerTree