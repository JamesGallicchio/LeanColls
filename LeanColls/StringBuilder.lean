/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Array.ArrayUninit

namespace LeanColls

structure StringBuilder where
  parts : List String
  totLength : Nat
  h_length : totLength = parts.foldr (·.length + ·) 0

namespace StringBuilder

def append (s : String) : StringBuilder → StringBuilder
| ⟨parts, totLength, h_length⟩ =>
  ⟨s::parts, totLength + s.length, by simp [List.foldr, h_length]; rw [Nat.add_comm]⟩

def toString : StringBuilder → String
| ⟨parts, _, _⟩ =>
