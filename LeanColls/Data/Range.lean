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

/-! ## Range Stepping -/

/-- Step function for range types.
`step i = i'` should be the smallest `i'` s.t. `i < i'`.
-/
class Step (ι : Type u) where
  step : ι → ι

class LawfulStep (ι) [Step ι] [LT ι] [LE ι] where
  step_minimal : ∀ i : ι, (∃ i', i < i') → ∀ i', i < i' → Step.step i ≤ i'

instance : Step Nat where
  step := Nat.succ

instance : LawfulStep Nat where
  step_minimal := by
    rintro i - i'' hi''
    exact hi''

instance : Step (Fin n) where
  step := fun i =>
    have : n > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
    ⟨(i+1) % n, Nat.mod_lt _ this⟩

instance : LawfulStep (Fin n) where
  step_minimal := by
    rintro i - i'' hi''
    cases i; cases i''
    simp_all [Step.step]
    rw [Nat.mod_eq_of_lt]
    · assumption
    · omega

/-! ## Range Folds -/

class WellFoundedStepLE (ι) [Step ι] [LE ι] where
  wf_step_le : ∀ stop, WellFounded (fun (x y : ι) => x ≤ stop ∧ Step.step y = x)

class WellFoundedStepLT (ι) [Step ι] [LT ι] where
  wf_step_lt : ∀ stop, WellFounded (fun (x y : ι) => x < stop ∧ Step.step y = x)

instance : WellFoundedStepLE Nat where
  wf_step_le stop := by
    constructor
    intro x
    simp [Step.step]
    if hx : ¬(x ≤ stop) then
      constructor
      intro y ⟨h,rfl⟩
      exfalso; apply hx (Nat.le_of_succ_le h)
    else
    simp at hx
    let diff := stop - x
    have : x = stop - diff := by
      simp only; rw [Nat.sub_sub_self hx]
    rw [this]; clear hx this
    have : diff ≤ stop := by omega
    clear_value diff
    induction diff with
    | zero =>
      constructor
      rintro - ⟨h,rfl⟩
      exfalso
      simp at h; exact Nat.not_succ_le_self _ h
    | succ i ih =>
      constructor
      rintro - ⟨-,rfl⟩
      have : (stop - i.succ).succ = (stop - i) := by omega
      rw [this]; clear this
      apply ih
      omega

instance : WellFoundedStepLT Nat where
  wf_step_lt stop := by
    constructor
    intro x
    simp [Step.step]
    if hx : ¬(x < stop) then
      constructor
      intro y ⟨h,rfl⟩
      exfalso; apply hx (Nat.le_of_succ_le h)
    else
    simp at hx
    let diff := stop - x
    have : x = stop - diff := by
      rw [Nat.sub_sub_self]; exact Nat.le_of_lt hx
    rw [this]; clear hx this
    have : diff ≤ stop := by omega
    clear_value diff
    induction diff with
    | zero =>
      constructor
      rintro - ⟨h,rfl⟩
      exfalso
      simp at h; exact Nat.not_succ_le_self _ (Nat.le_of_lt h)
    | succ i ih =>
      constructor
      rintro - ⟨-,rfl⟩
      have : (stop - i.succ).succ = (stop - i) := by omega
      rw [this]; clear this
      apply ih
      omega

structure StepToLE (ι : Type u) where
  (start stop : ι)

instance [Step ι] [LE ι] [WellFoundedStepLE ι] : WellFoundedRelation (StepToLE ι) where
  rel := fun ⟨start,stop⟩ ⟨start',stop'⟩ =>
    stop = stop' ∧ Step.step start' = start ∧ start ≤ stop
  wf := by
    constructor
    rintro ⟨start,stop⟩
    simp
    have ⟨this⟩ := WellFoundedStepLE.wf_step_le stop
    specialize this start
    induction this with
    | intro start _h ih =>
      constructor
      rintro ⟨start', stop'⟩
      simp_all

structure StepToLT (ι : Type u) where
  (start stop : ι)

instance [Step ι] [LT ι] [WellFoundedStepLT ι] : WellFoundedRelation (StepToLT ι) where
  rel := fun ⟨start,stop⟩ ⟨start',stop'⟩ =>
    stop = stop' ∧ Step.step start' = start ∧ start < stop
  wf := by
    constructor
    rintro ⟨start,stop⟩
    simp
    have ⟨this⟩ := WellFoundedStepLT.wf_step_lt stop
    specialize this start
    induction this with
    | intro start _h ih =>
      constructor
      rintro ⟨start', stop'⟩
      simp_all

section
variable [DecidableEq ι]
    [LE ι] [DecidableRel (· ≤ · : ι → ι → Prop)]
    [LT ι] [DecidableRel (· < · : ι → ι → Prop)]
    [Step ι]

attribute [-instance] instSizeOf

def foldAuxIncl [LawfulStep ι] [WellFoundedStepLE ι] (stop : ι) (f : β → ι → β) (i : ι) (acc : β) : β :=
  if h : i < stop then
    have := (LawfulStep.step_minimal i) ⟨stop,h⟩ _ h
    foldAuxIncl stop f (Step.step i) (f acc i)
  else
    f acc i
termination_by StepToLE.mk i stop

def foldAuxExcl [LawfulStep ι] [WellFoundedStepLE ι] (stop : ι) (f : β → ι → β) (i : ι) (acc : β) : β :=
  if h : i < stop then
    have := (LawfulStep.step_minimal i) ⟨stop,h⟩ _ h
    foldAuxExcl stop f (Step.step i) (f acc i)
  else
    acc
termination_by StepToLE.mk i stop

end
