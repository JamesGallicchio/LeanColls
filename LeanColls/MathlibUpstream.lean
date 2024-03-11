/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.OfFn

def Fin.foldl' (n : Nat) {β : (i : Nat) → i ≤ n → Sort u}
      (init : β 0 (Nat.zero_le _))
      (f : (i : Nat) → (h : i < n) → β i (Nat.le_of_lt h) → β (i+1) h)
      : β n (Nat.le_refl _) :=
  aux _ _ init
where
  aux (i : Nat) (h : i ≤ n) (acc : β i h) : β n (Nat.le_refl _) :=
    if h' : i < n then
      aux (i+1) h' (f i h' acc)
    else
      have : i = n := Nat.le_antisymm h (Nat.not_lt.mp h')
      this ▸ acc
termination_by n-i

theorem Fin.foldl_eq_foldl' (n : Nat) (f : α → Fin n → α) (init : α)
  : Fin.foldl n f init = Fin.foldl' (n := n) (β := fun _ _ => α) init (fun i h acc => f acc ⟨i,h⟩)
  := by
  simp [foldl, foldl']
  suffices ∀ i j (hj : i + j = n) acc,
    foldl.loop n f acc i =
      foldl'.aux (n := n) (β := fun _ _ => α)
        init (fun i h acc => f acc ⟨i, h⟩)
        i (hj ▸ Nat.le_add_right i j) acc
    from this 0 n (by simp) init
  intro i j hj
  induction j generalizing i with
  | zero =>
    intro acc
    simp at hj; cases hj
    unfold foldl.loop; unfold foldl'.aux
    simp
  | succ j' ih =>
    intro acc
    simp_all
    rw [Nat.add_succ, ← Nat.succ_add] at hj
    have hi : i < n := by calc
      _ ≤ Nat.succ i + j' := Nat.le_add_right _ _
      _ = n := hj
    have := ih (i+1) hj (f acc ⟨i,hi⟩)
    clear ih
    unfold foldl.loop; unfold foldl'.aux
    simp [*]

def Fin.foldlM [Monad m] (n : Nat) {β : Type u}
      (init : β)
      (f : Fin n → β → m β)
      : m β :=
  aux 0 init
where
  aux (i : Nat) (acc : β) : m β :=
    if h' : i < n then
      f ⟨i, h'⟩ acc >>= fun acc => aux (i+1) acc
    else
      pure acc
termination_by n-i

theorem Fin.foldlM_eq_foldl [Monad m] [LawfulMonad m] (n : Nat) {β : Type u} (init : β)
    (f : Fin n → β → m β)
  : Fin.foldlM n init f = Fin.foldl n (fun macc i => macc >>= fun acc => f i acc) (pure init)
  := by
  simp [foldl, foldlM]
  suffices ∀ i j (hj : i + j = n) macc,
    (macc >>= fun acc => foldlM.aux n f i acc) =
      foldl.loop n _ macc i
    by
    have := this 0 n (by simp) (pure init)
    simp at this
    exact this
  intro i j hj
  induction j generalizing i with
  | zero =>
    intro macc
    simp at hj; cases hj
    unfold foldl.loop; unfold foldlM.aux
    simp
  | succ j' ih =>
    intro macc
    rw [Nat.add_succ, ← Nat.succ_add] at hj
    have hi : i < n := by calc
      _ ≤ Nat.succ i + j' := Nat.le_add_right _ _
      _ = n := hj
    have := ih (i+1) hj (macc >>= fun acc => f ⟨i,hi⟩ acc)
    clear ih
    unfold foldl.loop; unfold foldlM.aux
    simp_all

theorem Fin.foldl_eq_foldl_ofFn (n) (f : α → Fin n → α) (init : α)
  : Fin.foldl n f init = List.foldl f init (List.ofFn id) := by
  unfold foldl
  suffices ∀ init i j (h : i + j = n),
    foldl.loop n f init i =
      List.foldl f init (List.ofFn (n := j) (fun x => Fin.natAdd i x |>.cast h))
    by
      have := this init 0 n (by simp)
      simp at this; rw [this]; rfl
  intro init i j h
  induction j generalizing init i with
  | zero =>
    unfold foldl.loop
    simp at h
    simp [List.drop_eq_nil_of_le, h]
  | succ j ih =>
    unfold foldl.loop
    have : i < n := by omega
    simp [this, cast]
    generalize f init _ = init'
    have : (i+1) + j = n := by omega
    specialize ih init' (i+1) this
    rw [ih]; clear ih
    congr
    funext ⟨x,hx⟩; simp; omega
