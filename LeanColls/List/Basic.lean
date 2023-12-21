/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.AuxLemmas

namespace List

@[deprecated pmap]
def map' (L : List τ) (f : (x : τ) → x ∈ L → τ') :=
  L.subtypeByMem.map (fun ⟨x,h⟩ => f x h)

@[deprecated single_le_sum]
theorem get_le_sum (L : List Nat) (i : Nat) (h_i : i < L.length)
  : L.get ⟨i,h_i⟩ ≤ L.sum
  := by
  apply single_le_sum
  · simp
  · exact get_mem L i h_i 
