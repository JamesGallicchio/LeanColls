/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Array.ArrayBuffer

namespace LeanColls

structure VarArray (α) where
  backing : ArrayBuffer α
deriving Inhabited

namespace VarArray

instance : Indexed (VarArray α) α where
  size a := a.backing.size
  nth a i := a.backing.get i

instance : IndexedOps (VarArray α) α := default

instance [ToString α] : ToString (VarArray α) where
  toString := toString ∘ (FoldableOps.toList)

instance : Enumerable (VarArray α) α where
  ρ := ArrayBuffer α
  insert A :=
    match A with
    | some ⟨a,A⟩ => A.push a
    | none => ArrayBuffer.empty ()
  fromEnumerator A := ⟨A⟩

def empty : VarArray α := ⟨ArrayBuffer.empty ()⟩

def size {α} := instIndexedVarArray.size (C := VarArray α)

def get {α} := instIndexedVarArray.nth (τ := α)

def set : (A : VarArray α) → Fin A.size → α → VarArray α
| ⟨A⟩, i, a => ⟨A.copyIfShared.set ⟨i, by simp; apply i.isLt⟩ a⟩

def push : VarArray α → α → VarArray α
| ⟨A⟩, a => ⟨A.copyIfShared.push a⟩
