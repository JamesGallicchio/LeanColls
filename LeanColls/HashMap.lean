/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.AuxLemmas
import LeanColls.Array
import LeanColls.View
import LeanColls.Classes
import LeanColls.FoldableOps

namespace LeanColls 

structure HashMap (κ τ : Type) [Hashable κ] [DecidableEq κ] where
  cap : Nat
  h_cap : cap > 0
  backing : COWArray (AList κ τ) cap
  size : Cached (
    View.view backing
    |>.map List.length
    |> FoldableOps.sum)

namespace HashMap
variable {κ τ : Type} [Hashable κ] [DecidableEq κ]

@[inline] private
def calc_idx' (k : κ) (cap : Nat) (h_cap : cap > 0) (h : cap < UInt64.size) : Fin cap :=
  let idx := (hash k) % (UInt64.ofNat cap)
  ⟨idx.toNat, by
    simp [UInt64.mod_def, Fin.mod_def]
    apply Nat.mod_lt_of_lt
    rw [UInt64.val_eq_of_lt h]
    apply Nat.mod_lt
    assumption
    exact UInt64.size_positive
    ⟩

@[inline]
def calc_idx (k : κ) (m : HashMap κ τ) : Fin m.cap :=
  match m with
  | ⟨cap, h_cap, backing, _⟩ =>
  calc_idx' k cap h_cap (
    Nat.lt_of_lt_of_le
      backing.backing.size_lt_usize
      USize.usize_bounded)

/- TODO: add Array.getU64 -/
def get? (k : κ) (m : HashMap κ τ) : Option τ :=
  m.backing.get (calc_idx k m)
  |> MapLike.get?.{0,0,0,0} k

def set' (k : κ) (t : τ) (m : HashMap κ τ) : Option τ × HashMap κ τ :=
  let idx := calc_idx k m
  match h : m.backing.get idx |> AList.set' k t with
  | (old, newSlot) =>
  let newSize :=
    match old with | none => m.size + 1 | some _ => m.size
  ⟨old, m.cap, m.h_cap, m.backing.set idx newSlot, newSize, by
    have : newSize = match old, h with | none, h => _ | some _, h => _ := rfl
    rw [this]
    clear this newSize
    match old with
    | none =>
      simp
      conv => lhs; rw [View.view_eq_view_canonicalToList]
      conv => rhs; rw [View.view_eq_view_canonicalToList]
      simp
      sorry
    | some _ =>
      simp
      sorry
    ⟩

def set (k : κ) (t : τ) (m : HashMap κ τ) : HashMap κ τ :=
  (m.set' k t).2

def fold (m : HashMap κ τ) (f : β → (κ × τ) → β) (acc : β) :=
  Foldable.fold m.backing (fun acc l =>
    Foldable.fold l f acc
  ) acc

instance : Membership κ (HashMap κ τ) where
  mem k m := get? k m |>.isSome

instance : MapLike (HashMap κ τ) κ τ where
  get? := get?
  fold := fold

theorem get_set_eq [Hashable κ] (k : κ) (t : τ) (m : HashMap κ τ)
  : (m.set k t |>.get? k) = some t
  := by
  simp [get?, set, set', calc_idx, calc_idx']
  simp [COWArray.get, COWArray.set]
  simp [MapLike.get?]
  simp [AList.get?_set'_eq]

theorem get_set_ne [Hashable κ]
  (k : κ) (t : τ) (k' : κ) (m : HashMap κ τ)
  (h_k : k ≠ k')
  : (m.set k t |>.get? k') = m.get? k'
  := by
  simp [get?, set, set']
  simp [COWArray.get, COWArray.set]
  simp [calc_idx]
  generalize calc_idx' k _ _ _ = k_idx
  generalize calc_idx' k' _ _ _ = k'_idx
  match h : decide (k_idx = k'_idx) with
  | true =>
    simp at h
    simp [h]
    simp [MapLike.get?]
    rw [AList.get?_set'_ne _ _ _ _ h_k]
  | false =>
    have : k_idx ≠ k'_idx := by
      intro h; cases h; simp at h
    simp [this, Array.copy_def]
