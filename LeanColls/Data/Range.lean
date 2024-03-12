/- Copyright (c) 2023 James Gallicchio

Authors: James Gallicchio
-/

import Std.Data.Range.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Basic

import LeanColls.Classes.Ops
import LeanColls.MathlibUpstream

namespace LeanColls

structure Range extends Std.Range where
  step_pos : step > 0
  start_le_stop : start ≤ stop

namespace Range

attribute [simp] step_pos start_le_stop

@[simp] def ofStd : Std.Range → Range
| {start, stop, step} =>
  { start := start
  , stop := max start stop
  , step := max 1 step
  , step_pos := by simp
  , start_le_stop := by simp
  }

instance : Coe Std.Range Range where
  coe := ofStd

instance : CoeHead Range Std.Range where
  coe r := r.toRange


def contains (r : Range) (i : Nat) :=
  r.start ≤ i && i < r.stop && r.step ∣ (i - r.start)

instance : Membership Nat Range where
  mem i r := contains r i

theorem mem_def (r : Range) : x ∈ r ↔ r.start ≤ x ∧ x < r.stop ∧ (r.step ∣ x - r.start) := by
  simp [Membership.mem, contains]
  exact and_assoc

def nth (r : Range) (i : Nat) : Nat :=
  r.start + i * r.step

@[simp] theorem nth_ge_start (r : Range) (i : Nat) : nth r i ≥ r.start := by
  simp [nth]

@[simp] theorem nth_sub_start (r : Range) (i : Nat) : r.step ∣ (nth r i - r.start) := by
  simp [nth]

def ofNth (r : Range) (x : Nat) : Nat :=
  (x - r.start) / r.step

theorem ofNth_nth (r : Range) (i : Nat)
  : ofNth r (nth r i) = i := by
  simp [nth, ofNth]

theorem nth_ofNth {r : Range} {x : Nat} (h : x ∈ r)
  : nth r (ofNth r x) = x := by
  simp [mem_def] at h
  simp [nth, ofNth]
  rw [Nat.div_mul_cancel h.2.2]
  simp only [*, ge_iff_le, add_tsub_cancel_of_le]

def size (r : Range) : Nat :=
  (r.stop - r.start + r.step - 1) / r.step

instance : Size Range where
  size := size

theorem nth_lt_stop_iff_lt_size (r : Range) (i : Nat)
  : nth r i < r.stop ↔ i < size r := by
  simp [nth, size, Nat.lt_iff_add_one_le,
        Nat.le_div_iff_mul_le r.step_pos]
  zify; simp
  constructor <;> intro h <;> linarith

@[simp] theorem nth_mem_iff_lt_size (r : Range) (i : Nat)
  : nth r i ∈ r ↔ i < size r := by
  simp [mem_def, nth_lt_stop_iff_lt_size]

theorem nth_size_eq_stop (r : Range) (h : r.step = 1)
  : r.nth r.size = r.stop := by
    simp [nth, size, h]

theorem nth_size_lt (r : Range)
  : r.nth r.size < r.stop + r.step := by
    simp [nth, size]
    rw [Nat.add_comm, Nat.lt_iff_add_one_le, Nat.add_assoc]
    apply Nat.add_le_of_le_sub
    · apply Nat.add_le_add; simp; apply r.step_pos
    convert Nat.div_mul_le_self _ _ using 1
    rw [Nat.add_comm, Nat.sub_add_eq,
        Nat.add_sub_assoc r.start_le_stop,
        Nat.add_comm,
        Nat.add_sub_assoc r.step_pos]


def empty (start := 0) : Range where
  start := start
  stop := start
  step_pos := by simp
  start_le_stop := by simp

@[inline] def isEmpty (r : Range) : Bool :=
  r.start = r.stop

theorem size_eq_zero_iff_isEmpty (r : Range)
  : r.size = 0 ↔ r.isEmpty := by
  simp [size, isEmpty]
  rw [Nat.div_eq_zero_iff r.step_pos,
      Nat.lt_iff_add_one_le,
      Nat.sub_add_cancel]
  · simp
    rw [Nat.sub_eq_zero_iff_le, Nat.le_antisymm_iff]
    simp only [start_le_stop, true_and]
  · exact le_add_left r.step_pos


def get (r : Range) (i : Fin (size r)) : Nat := nth r i

theorem get_mem (r : Range) (i) : get r i ∈ r := by
  rcases i with ⟨i,hi⟩
  simp [get, mem_def, nth_lt_stop_iff_lt_size]
  simp [nth, hi]

theorem mem_iff_exists_get (r : Range) : x ∈ r ↔ ∃ i, x = get r i := by
  constructor
  · intro h
    have := nth_ofNth h
    rw [← this] at h ⊢; clear this
    simp at h
    use ⟨_,h⟩
    rfl
  · rintro ⟨⟨i,hi⟩,rfl⟩
    simp [get, hi]


def foldl (r : Range) (f : α → Nat → α) (init : α) : α :=
  aux r.start (fun h => by simp_all [mem_def]) init
where
  aux i (hi : i < r.stop → i ∈ r) (acc : α) :=
    if h : i < r.stop then
      have := r.step_pos
      have : r.stop - (i + r.step) < r.stop - i := by
        rw [Nat.sub_add_eq]; apply Nat.sub_lt
        repeat simp [*]
      aux (i + r.step) (fun h => by
        simp_all [mem_def]; rcases hi with ⟨left,right⟩
        constructor
        · apply le_add_right; assumption
        · rw [Nat.sub_add_comm left]; simp [*]
        ) (f acc i)
    else
      acc
termination_by r.stop - i

instance : Fold Range Nat where
  fold := foldl

def foldl' (r : Range) (f : α → (i : Nat) → i ∈ r → α) (init : α) : α :=
  aux r.start (fun h => by simp_all [mem_def]) init
where
  aux i (hi : i < r.stop → i ∈ r) (acc : α) :=
    if h : i < r.stop then
      have := r.step_pos
      have : r.stop - (i + r.step) < r.stop - i := by
        rw [Nat.sub_add_eq]; apply Nat.sub_lt
        repeat simp [*]
      aux (i + r.step) (fun h => by
        simp_all [mem_def]; rcases hi with ⟨left,right⟩
        constructor
        · apply le_add_right; assumption
        · rw [Nat.sub_add_comm left]; simp [*]
        ) (f acc i (hi h))
    else
      acc
termination_by r.stop - i

theorem fold_def (r : Range) (f : β → Nat → β)
    : fold r f init =
      Fin.foldl (r.size) (fun acc i => f acc (r.get i)) init
  := by
  simp [fold, foldl, Fin.foldl]
  sorry -- TODO
