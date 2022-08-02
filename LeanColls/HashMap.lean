/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.AuxLemmas
import LeanColls.Array
import LeanColls.View
import LeanColls.Classes

namespace LeanColls

structure HashMap (κ τ : Type u) [Hashable κ] [DecidableEq κ] where
  cap : Nat
  h_cap : cap > 0
  backing : Array (List (κ × τ)) cap
  size : Cached (
    View.view backing
    |>.map (fun p => p.2.length)
    |> FoldableOps.sum
  )

namespace HashMap
variable {κ : Type u} {τ} [Hashable κ] [DecidableEq κ]

@[inline] private
def calc_idx (k : κ) (m : HashMap κ τ) : Fin m.cap :=
  let idx := (hash k) % m.cap
  ⟨idx.toNat, by
    simp [HMod.hMod, UInt64.modn, UInt64.toNat, Fin.modn, Mod.mod]
    apply Nat.mod_lt_of_lt
      (Nat.mod_lt _ m.h_cap)
      (by decide)
    ⟩

/- TODO: add Array.getU64 -/
def get (m : HashMap κ τ) (k : κ) : Option τ :=
  m.backing.get (calc_idx k m)
  |>.find? (λ ⟨k',_⟩ => k = k')
  |>.map Prod.snd

def set (k : κ) (t : τ) (m : HashMap κ τ) : HashMap κ τ :=
  let idx := calc_idx k m
  let (eff, newSlot) := m.backing.get idx |> AList.set k t
  let newSize :=
    match eff with | .replaced => m.size | .inserted => m.size + 1
  ⟨m.cap, m.h_cap, m.backing.set idx newSlot, ⟨newSize, by
    simp
    clear newSize
    match eff with
    | .replaced =>
      simp
      stop
      simp [Foldable.fold, View.instFoldableOpsViewInstFoldableView_1, default, FoldableOps.defaultImpl]
      simp [Size.size, Array.size_set]
      apply Range.fold'_ind (motive := λ i h a => sorry)
      stop
      suffices ∀ acc i, Range.fold'.loop m.cap (fun acc i h_i => acc + List.length (Indexed.nth m.backing { val := i, isLt := h_i })) acc i =
                Range.fold'.loop m.cap (fun acc i h_i => acc + List.length
                  (Indexed.nth (Array.set m.backing (LeanColls.HashMap.calc_idx k m) newSlot) { val := i, isLt := h_i })) acc i
        from this 0 0
      intro acc i; induction i generalizing acc
      unfold Range.fold'.loop
      simp
      split <;> simp
      sorry
      sorry
    | .inserted =>
      simp
      sorry
    ⟩⟩

def fold (f) (acc : β) (m : HashMap κ τ) :=
  m.backing
  |> Foldable.fold (fun acc (_,l) =>
    Foldable.fold f acc l
  ) acc

instance : Membership κ (HashMap κ τ) where
  mem k m := get m k |>.isSome

instance : MapLike (HashMap κ τ) κ τ where
  get? := get
  fold := fold