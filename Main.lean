/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls

open LeanColls

theorem inferred_fold_eq_list_fold
  : Foldable'.fold' (C := List Nat) (β := β)
    = List.fold'
  := rfl

def main := ((do
  let iters := 100
  let len := 10000
  let list := List.iota len
  timeit "fold" do
    for _ in [0:iters] do
      let res := Foldable.fold (λ acc _ => acc+1) 0 list
      if res ≠ len then
        IO.print "ohno"
  timeit "fold'" do
    for _ in [0:iters] do
      let res := Foldable'.fold' list (λ acc _ _ => acc+1) 0
      if res ≠ len then
        IO.print "ohno"
  ) : IO Unit)

