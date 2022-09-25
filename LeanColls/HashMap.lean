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
  h_cap : 0 < cap ∧ cap < UInt64.size
  backing : COWArray (AList κ τ) cap
  size : Cached (
    View.view backing
    |>.map List.length
    |> FoldableOps.sum)

namespace HashMap
variable {κ τ : Type} [Hashable κ] [DecidableEq κ]

def new (cap : Nat := 16) (h_cap : 0 < cap ∧ cap < UInt64.size := by decide) : HashMap κ τ :=
  ⟨cap, h_cap, COWArray.new [] cap, cached' 0 (by
    clear h_cap
    simp [View.map, View.view, FoldableOps.sum,
      FoldableOps.defaultImpl, Foldable.fold, Foldable'.Correct.fold']
    simp [Size.size, COWArray.new, Indexed.nth, COWArray.get, Array.new, Array.get]
    generalize Range.foldl'' _ _ _ _ = res
    match res with
    | ⟨_,A,hA⟩ =>
    clear res
    simp
    conv =>
      rhs
      arg 2
      intro acc i h
      rw [hA]
      simp
    clear hA A
    induction cap
    case zero => simp
    case succ n ih _ =>
    simp
    apply ih
    simp)⟩

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
  | ⟨cap, h_cap, _, _⟩ =>
  calc_idx' k cap h_cap.1 h_cap.2

/- TODO: add Array.getU64 -/
def get? (k : κ) (m : HashMap κ τ) : Option τ :=
  m.backing.get (calc_idx k m)
  |> MapLike.get?.{0,0,0,0} k

@[inline]
private def setNoRebalance (k : κ) (t : τ) (m : HashMap κ τ) : Option τ × HashMap κ τ :=
  let idx := calc_idx k m
  match h : m.backing.get idx |> AList.set' k t with
  | (old, newSlot) =>
  let newSize :=
    match old with | none => m.size + 1 | some _ => m.size
  ⟨old, m.cap, m.h_cap, m.backing.set idx newSlot, newSize,
  by
    have : newSize = match old, h with | none, h => _ | some _, h => _ := rfl
    rw [this]
    clear this newSize
    have := AList.length_set' k t (COWArray.get m.backing idx)
    rw [h] at this
    match old with
    | none =>
      simp at this ⊢
      conv => lhs; rw [View.view_eq_view_canonicalToList]
      conv => rhs; rw [View.view_eq_view_canonicalToList]
      simp
      simp [List.map_set]
      rw [List.sum_set]
      case h_i =>
        simp [idx.isLt]
      simp
      rw [this]
      have := List.get_map_reverse List.length
        (l := Array.toList m.backing.backing)
        (n := ⟨calc_idx k m, by simp [idx.isLt]⟩)
      rw [this]
      rw [←Nat.sub_add_comm (by apply List.get_le_sum)]
      conv =>
        rhs; arg 1; arg 2
        rw [Nat.add_comm]
      rw [←Nat.add_assoc]
      simp [COWArray.get, ←Array.toList_get]
    | some _ =>
      simp at this ⊢
      conv => lhs; rw [View.view_eq_view_canonicalToList]
      conv => rhs; rw [View.view_eq_view_canonicalToList]
      simp
      simp [List.map_set]
      rw [List.sum_set]
      case h_i =>
        simp [idx.isLt]
      simp
      rw [this]
      have := List.get_map_reverse List.length
        (l := Array.toList m.backing.backing)
        (n := ⟨calc_idx k m, by simp [idx.isLt]⟩)
      rw [this]
      rw [←Nat.sub_add_comm (by apply List.get_le_sum)]
      simp [COWArray.get, ←Array.toList_get]
    ⟩

def rebalance : HashMap κ τ → HashMap κ τ
| ⟨cap, h_cap, backing, size⟩ =>
  if size >= cap then
    new (cap := min (2 * cap) (UInt64.size - 1)) (by
      constructor
      case left =>
        simp [min]
        split
        case inl =>
          rw [(by simp : 0 = 0 * 0)]
          apply Nat.mul_lt_mul'
          decide
          exact h_cap.1
          decide
        case inr =>
          simp
      case right =>
        simp [min]
        split
        case inl h =>
          exact Nat.succ_le_succ h
        case inr h =>
          simp)
    |> Foldable.fold backing (fun acc L =>
      L.foldl (fun acc (k,t) => (acc.setNoRebalance k t).2) acc)
  else
    ⟨cap, h_cap, backing, size⟩

def set' (k : κ) (t : τ) (m : HashMap κ τ) : Option τ × HashMap κ τ :=
  let (o, h) := m.setNoRebalance k t
  (o, rebalance h)

def set (k : κ) (t : τ) (m : HashMap κ τ) : HashMap κ τ :=
  rebalance (m.setNoRebalance k t).2

def fold (m : HashMap κ τ) (f : β → (κ × τ) → β) (acc : β) :=
  Foldable.fold m.backing (fun acc l =>
    Foldable.fold l f acc
  ) acc

instance : Membership κ (HashMap κ τ) where
  mem k m := get? k m |>.isSome

instance : MapLike (HashMap κ τ) κ τ where
  get? := get?
  fold := fold

theorem get_rebalance (k : κ) (m : HashMap κ τ)
  : m.rebalance.get? k = m.get? k
  := by
  simp [rebalance]
  split <;> simp
  simp [get?]
  sorry

theorem get_set_eq [Hashable κ] (k : κ) (t : τ) (m : HashMap κ τ)
  : (m.set k t |>.get? k) = some t
  := by
  simp [set, get_rebalance]
  simp [get?, setNoRebalance, calc_idx, calc_idx']
  simp [COWArray.get, COWArray.set]
  simp [MapLike.get?]
  simp [AList.get?_set'_eq]

theorem get_set_ne [Hashable κ]
  (k : κ) (t : τ) (k' : κ) (m : HashMap κ τ)
  (h_k : k ≠ k')
  : (m.set k t |>.get? k') = m.get? k'
  := by
  simp [set, get_rebalance]
  simp [get?, setNoRebalance]
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
