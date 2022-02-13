/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/

import LeanColls.Fold

inductive LazyList (α : Type u)
| nil : LazyList α
| cons (hd : α) (tl : LazyList α) : LazyList α
| delayed (t : Thunk (LazyList α)) : LazyList α

namespace LazyList
variable {α : Type u} {β : Type v} {δ : Type w}

instance : Inhabited (LazyList α) :=
⟨nil⟩

@[inline] protected def pure : α → LazyList α
| a => cons a nil

-- Height measures number of nodes (including delayeds)
noncomputable def height (ll : LazyList α) : Nat :=
  @LazyList.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    α 0 (fun _ _ ih => ih + 1) (fun _ ih => ih + 1) (fun _ ih => ih ()) ll

@[simp] theorem height_nil : (@LazyList.nil α).height = 0 := rfl
@[simp] theorem height_cons : (@LazyList.cons α a l).height = l.height + 1 := rfl
@[simp] theorem height_delayed (as) :
  (@LazyList.delayed α as).height = as.get.height + 1 := by
  have : as = ⟨fun x => as.get⟩ := by
    cases as with | _ fn => apply congrArg; funext (); rfl
  rw [this]; rfl

def get : LazyList α → Option (α × LazyList α)
| delayed as => get as.get
| nil        => none
| cons a as  => some (a, as)
termination_by _ as => as.height

def isEmpty : LazyList α → Bool
| nil        => true
| cons _ _   => false
| delayed as => isEmpty as.get
termination_by _ as => as.height

/-
Length of a list is number of actual elements
in the list, ignoring delays
-/
def length : LazyList α → Nat
| nil        => 0
| cons _ as  => length as + 1
| delayed as => length as.get
termination_by _ as => as.height

@[simp] theorem length_nil : (@nil α).length = 0 := by simp [length]
@[simp] theorem length_cons : (@cons α a as).length = as.length + 1 := by simp [length]
@[simp] theorem length_delayed (as)
  : (@delayed α as).length = as.get.length
  := by
  have : as = ⟨fun x => as.get⟩ := by
    cases as with | _ fn => apply congrArg; funext (); rfl
  rw [this]; rfl

def toList : LazyList α → List α
| nil        => []
| cons a as  => a :: toList as
| delayed as => toList as.get
termination_by _ as => as.height

def append : LazyList α → LazyList α → LazyList α
| nil,        bs => bs
| cons a as,  bs => cons a (delayed (append as bs))
| delayed as, bs => append as.get bs
termination_by _ as _ => as.height

instance : Append (LazyList α) :=
⟨LazyList.append⟩

@[simp] theorem length_append (l₁ l₂ : LazyList α)
  : (l₁ ++ l₂).length = l₁.length + l₂.length
  := @rec α
    (λ l => (l ++ l₂).length = l.length + l₂.length)
    (λ t => (t.get ++ l₂).length = t.get.length + l₂.length)
    (by simp [HAppend.hAppend, Append.append, append])
    (by
      intros hd tl tl_ih
      simp [HAppend.hAppend, Append.append, append, Thunk.get] at tl_ih |-
      simp [tl_ih, Nat.add_comm, Nat.add_assoc]
      )
    (by
      intros t t_ih
      simp [HAppend.hAppend, Append.append, append] at t_ih |-
      assumption
      )
    (by
      intros fn fn_ih
      have := fn_ih ()
      simp [HAppend.hAppend, Append.append, append, Thunk.get] at this |-
      assumption
      )
    l₁

@[simp] def revAppend : LazyList α → LazyList α → LazyList α
| nil,        bs => bs
| cons a as,  bs => revAppend as (cons a bs)
| delayed as, bs => revAppend as.get bs
termination_by _ as _ => as.height

@[simp] theorem length_revAppend (l₁ l₂ : LazyList α)
  : (revAppend l₁ l₂).length = l₁.length + l₂.length
  := @rec α
    (λ l => ∀ l2, (revAppend l l2).length = l.length + l2.length)
    (λ t => ∀ l2, (revAppend t.get l2).length = t.get.length + l2.length)
    (by simp)
    (by
      intros hd tl tl_ih l2
      simp [Thunk.get] at tl_ih |-
      have := tl_ih (cons hd l2)
      rw [this]
      simp [Nat.add_assoc]
      simp [Nat.add_comm]
      )
    (by
      intros t t_ih
      simp [HAppend.hAppend, Append.append, append] at t_ih |-
      assumption
      )
    (by
      intros fn fn_ih
      have := fn_ih ()
      simp [HAppend.hAppend, Append.append, append, Thunk.get] at this |-
      assumption
      )
    l₁ l₂


@[simp] def reverse (l : LazyList α) := revAppend l nil

@[simp] theorem length_reverse (l : LazyList α) : l.reverse.length = l.length
  := by simp

def interleave : LazyList α → LazyList α → LazyList α
| nil,        bs => bs
| cons a as,  bs =>
  have : bs.height + as.height < as.height + 1 + bs.height := by
    rw [Nat.add_comm, Nat.add_right_comm]; decreasing_tactic
  cons a (delayed (interleave bs as))
| delayed as, bs =>
  have : as.get.height + bs.height < as.get.height + 1 + bs.height := by
    rw [Nat.add_right_comm]; decreasing_tactic
  interleave as.get bs
termination_by _ as bs => as.height + bs.height

@[specialize] def map (f : α → β) : LazyList α → LazyList β
| nil        => nil
| cons a as  => cons (f a) (delayed (map f as))
| delayed as => map f as.get
termination_by _ as => as.height

@[specialize] def map₂ (f : α → β → δ) : LazyList α → LazyList β → LazyList δ
| nil, _ => nil
| _, nil => nil
| cons a as, cons b bs =>
  have : as.height + bs.height < as.height + 1 + bs.height + 1 := by
    rw [Nat.add_right_comm as.height]
    exact Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)
 cons (f a b) (delayed (map₂ f as bs))
| delayed as, bs =>
  have : as.get.height + bs.height < as.get.height + 1 + bs.height := by
    rw [Nat.add_right_comm]; decreasing_tactic
  map₂ f as.get bs
| as, delayed bs => map₂ f as bs.get
termination_by _ as bs => as.height + bs.height

@[inline] def zip : LazyList α → LazyList β → LazyList (α × β) :=
map₂ Prod.mk

def join : LazyList (LazyList α) → LazyList α
| nil        => nil
| cons a as  => a ++ delayed (join as)
| delayed as => join as.get
termination_by _ as => as.height

@[inline] protected def bind (x : LazyList α) (f : α → LazyList β) : LazyList β :=
join (x.map f)

def take : Nat → LazyList α → List α
| 0, as => []
| _, nil => []
| i+1, cons a as => a :: take i as
| i+1, delayed as => take (i+1) as.get
termination_by _ as => as.height

@[specialize] def filter (p : α → Bool) : LazyList α → LazyList α
| nil          => nil
| (cons a as)  => if p a then cons a (delayed (filter p as)) else filter p as
| (delayed as) => filter p as.get
termination_by _ as => as.height

instance : Monad LazyList where
  pure := @LazyList.pure
  bind := @LazyList.bind
  map := @LazyList.map

instance : Alternative LazyList where
  failure := nil
  orElse  := fun as bs => LazyList.append as (delayed (Thunk.mk bs))

def foldUntil (f : α → τ → ContOrDone φ α) (acc : α)
: LazyList τ → ContOrDone φ α
| nil        => ContOrDone.Cont acc
| cons a as  => do
  let acc ← f acc a
  foldUntil f acc as
| delayed as => foldUntil f acc (as.get)
termination_by _ as => as.height

instance : FoldUntil (LazyList τ) τ := ⟨foldUntil⟩


@[specialize] partial def iterate (f : α → α) : α → LazyList α
| x => cons x (delayed (iterate f (f x)))

@[specialize] partial def iterate₂ (f : α → α → α) : α → α → LazyList α
| x, y => cons x (delayed (iterate₂ f y (f x y)))


partial def cycle : LazyList α → LazyList α
| xs => xs ++ delayed (cycle xs)

partial def repeat : α → LazyList α
| a => cons a (delayed (repeat a))

def inits : LazyList α → LazyList (LazyList α)
| nil        => cons nil nil
| cons a as  => cons nil (delayed (map (fun as => cons a as) (inits as)))
| delayed as => inits as.get
termination_by _ as => as.height

private def addOpenBracket (s : String) : String :=
if s.isEmpty then "[" else s

def approxToStringAux [ToString α] : Nat → LazyList α → String → String
| _,   nil,        r => (if r.isEmpty then "[" else r) ++ "]"
| 0,   _,          r => (if r.isEmpty then "[" else r) ++ ", ..]"
| n+1, cons a as,  r => approxToStringAux n as ((if r.isEmpty then "[" else r ++ ", ") ++ toString a)
| n,   delayed as, r => approxToStringAux n as.get r
termination_by _ n as _ => as.height

def approxToString [ToString α] (as : LazyList α) (n : Nat := 10) : String :=
as.approxToStringAux n ""

instance [ToString α] : ToString (LazyList α) :=
⟨approxToString⟩

end LazyList


private unsafe def List.toLazyUnsafe {α : Type u} (xs : List α) : LazyList α :=
  unsafeCast xs

@[implementedBy List.toLazyUnsafe]
def List.toLazy {α : Type u} : List α → LazyList α
| []     => LazyList.nil
| (h::t) => LazyList.cons h (toLazy t)


def fib : LazyList Nat :=
LazyList.iterate₂ (·+·) 0 1

def tst : LazyList String := do
  let x ← [1, 2, 3].toLazy
  let y ← [2, 3, 4].toLazy
  -- dbgTrace (toString x ++ " " ++ toString y) $ λ _,
  guard (x + y > 5)
  return (toString x ++ " + " ++ toString y ++ " = " ++ toString (x+y))

open LazyList

def iota (i : UInt32 := 0) : LazyList UInt32 :=
iterate (·+1) i

partial def sieve : LazyList UInt32 → LazyList UInt32
| nil          => nil
| (cons a as)  => cons a (delayed (sieve (filter (fun b => b % a != 0) as)))
| (delayed as) => sieve as.get

partial def primes : LazyList UInt32 :=
sieve (iota 2)

#eval show IO Unit from do
  let n := 10
  IO.println $ tst.isEmpty ;
  -- IO.println $ [1, 2, 3].toLazy.cycle,
  -- IO.println $ [1, 2, 3].toLazy.cycle.inits,
  -- IO.println $ ((iota.filter (λ v, v % 5 == 0)).approx 50000).foldl (+) 0,
  IO.println $ (primes.take 2000).foldl (·+·) 0
  -- IO.println $ tst.head,
  -- IO.println $ fib.interleave (iota.map (+100)),
  -- IO.println $ ((iota.map (+10)).filter (λ v, v % 2 == 0)),
  return ()