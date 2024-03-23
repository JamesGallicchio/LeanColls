/- Copyright (c) 2023-2024 James Gallicchio

Authors: James Gallicchio
-/

import Std.Data.Range.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Basic

import LeanColls.Classes.Ops
import LeanColls.MathlibUpstream

namespace LeanColls

namespace Range

/-! ## Generalized Ranges

Mathlib defines 9 common intervals over preorders,
based on whether the left and right bounds are
- closed (inclusive)
- open (exclusive)
- infinite (unbounded)

These are denoted `Range.XX` here.
`X` is `C` for closed, `O` for open, and `I` for infinite.
-/

structure II (ι : Type u)
structure IC {ι : Type u} (  R : ι)
structure IO {ι : Type u} (  R : ι)
structure CI {ι : Type u} (L   : ι)
structure OI {ι : Type u} (L   : ι)
structure OO {ι : Type u} (L R : ι)
structure CO {ι : Type u} (L R : ι)
structure OC {ι : Type u} (L R : ι)
structure CC {ι : Type u} (L R : ι)

/-! ## Range Notation

- Ranges are denoted by `a..b`
- By default the endpoints are included
- Write `a<..b` or `a..<b` to exclude either endpoint.
- Write `a..` or `..b` or `..` for ranges unbounded on left/right
-/

notation    ".."    => II
notation    ".."  r => IC r
notation    "..<" r => IO r
notation l  ".."    => CI l
notation l "<.."    => OI l
notation l  ".."  r => OO l r
notation l  "..<" r => CO l r
notation l "<.."  r => OC l r
notation l "<..<" r => CC l r

/-! ## Range Membership -/

section
variable [LE ι] [DecidableRel (· ≤ · : ι → ι → Prop)] [LT ι] [DecidableRel (· < · : ι → ι → Prop)]

@[inline] def II.contains (_self : II (ι := ι)    ) : ι → Prop := fun _i => true
@[inline] def IC.contains (_self : IC (ι := ι) r  ) : ι → Prop := fun i => r ≤ i
@[inline] def IO.contains (_self : IO (ι := ι) r  ) : ι → Prop := fun i => r < i
@[inline] def CI.contains (_self : CI (ι := ι) l  ) : ι → Prop := fun i => l ≤ i
@[inline] def OI.contains (_self : OI (ι := ι) l  ) : ι → Prop := fun i => l < i
@[inline] def OO.contains (_self : OO (ι := ι) l r) : ι → Prop := fun i => l < i && i < r
@[inline] def CO.contains (_self : CO (ι := ι) l r) : ι → Prop := fun i => l ≤ i && i < r
@[inline] def OC.contains (_self : OC (ι := ι) l r) : ι → Prop := fun i => l < i && i ≤ r
@[inline] def CC.contains (_self : CC (ι := ι) l r) : ι → Prop := fun i => l ≤ i && i ≤ r

@[inline] instance : Membership ι (II (ι := ι)    ) := ⟨Function.swap II.contains⟩
@[inline] instance : Membership ι (IC (ι := ι) r  ) := ⟨Function.swap IC.contains⟩
@[inline] instance : Membership ι (IO (ι := ι) r  ) := ⟨Function.swap IO.contains⟩
@[inline] instance : Membership ι (CI (ι := ι) l  ) := ⟨Function.swap CI.contains⟩
@[inline] instance : Membership ι (OI (ι := ι) l  ) := ⟨Function.swap OI.contains⟩
@[inline] instance : Membership ι (OO (ι := ι) l r) := ⟨Function.swap OO.contains⟩
@[inline] instance : Membership ι (CO (ι := ι) l r) := ⟨Function.swap CO.contains⟩
@[inline] instance : Membership ι (OC (ι := ι) l r) := ⟨Function.swap OC.contains⟩
@[inline] instance : Membership ι (CC (ι := ι) l r) := ⟨Function.swap CC.contains⟩

instance : DecidablePred (II.contains (self : II (ι := ι)    )) := by unfold II.contains; infer_instance
instance : DecidablePred (IC.contains (self : IC (ι := ι) r  )) := by unfold IC.contains; infer_instance
instance : DecidablePred (IO.contains (self : IO (ι := ι) r  )) := by unfold IO.contains; infer_instance
instance : DecidablePred (CI.contains (self : CI (ι := ι) l  )) := by unfold CI.contains; infer_instance
instance : DecidablePred (OI.contains (self : OI (ι := ι) l  )) := by unfold OI.contains; infer_instance
instance : DecidablePred (OO.contains (self : OO (ι := ι) l r)) := by unfold OO.contains; infer_instance
instance : DecidablePred (CO.contains (self : CO (ι := ι) l r)) := by unfold CO.contains; infer_instance
instance : DecidablePred (OC.contains (self : OC (ι := ι) l r)) := by unfold OC.contains; infer_instance
instance : DecidablePred (CC.contains (self : CC (ι := ι) l r)) := by unfold CC.contains; infer_instance

instance II.instDecidableMem : Decidable (i ∈ (self : II (ι := ι)    )) := by simp [Membership.mem]; infer_instance
instance IC.instDecidableMem : Decidable (i ∈ (self : IC (ι := ι) r  )) := by simp [Membership.mem]; infer_instance
instance IO.instDecidableMem : Decidable (i ∈ (self : IO (ι := ι) r  )) := by simp [Membership.mem]; infer_instance
instance CI.instDecidableMem : Decidable (i ∈ (self : CI (ι := ι) l  )) := by simp [Membership.mem]; infer_instance
instance OI.instDecidableMem : Decidable (i ∈ (self : OI (ι := ι) l  )) := by simp [Membership.mem]; infer_instance
instance OO.instDecidableMem : Decidable (i ∈ (self : OO (ι := ι) l r)) := by simp [Membership.mem]; infer_instance
instance CO.instDecidableMem : Decidable (i ∈ (self : CO (ι := ι) l r)) := by simp [Membership.mem]; infer_instance
instance OC.instDecidableMem : Decidable (i ∈ (self : OC (ι := ι) l r)) := by simp [Membership.mem]; infer_instance
instance CC.instDecidableMem : Decidable (i ∈ (self : CC (ι := ι) l r)) := by simp [Membership.mem]; infer_instance

end

/-! ## Range Folds -/

section
variable [LE ι] [DecidableRel (· ≤ · : ι → ι → Prop)] [LT ι] [DecidableRel (· < · : ι → ι → Prop)]
          [Add ι] [One ι]

def foldlAux (f : β → ι → β) (acc : β) (start stop : ι) : β :=
  aux

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
    constructor <;> intro h
    · apply Nat.le_antisymm
      exact r.start_le_stop
      have := (Nat.sub_eq_iff_eq_add r.start_le_stop).mp h
      simp [this]
    · simp [h]
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
