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

instance [One ι] [Add ι] : Step ι where
  step x := x + 1

class LawfulStep (ι) [Step ι] [LT ι] [LE ι] where
  step_minimal : ∀ i : ι, (∃ i', i < i') → ∀ i', i < i' → Step.step i ≤ i'

instance : LawfulStep Nat where
step_minimal := by
    rintro i - i'' hi''
    exact hi''

instance [NeZero n] : LawfulStep (Fin n) where
  step_minimal := by
    rintro i - i'' hi''
    cases i; cases i''
    simp_all [Step.step, Fin.add_def]
    rw [Nat.mod_eq_of_lt]
    · assumption
    · omega

instance : LawfulStep UInt8 where
  step_minimal := by
    rintro ⟨⟨i,hi⟩⟩ - ⟨⟨i',hi'1⟩⟩ hi'2
    simp [
        Step.step, Nat.lt_iff_add_one_le,
        instLEUInt8, UInt8.le,
        instLTUInt8, UInt8.lt,
        UInt8.add_def, Fin.add_def
      ] at hi'2 ⊢
    rw [Nat.mod_eq_of_lt]
    · exact hi'2
    · calc _ ≤ i' := hi'2
        _ < UInt8.size := hi'1

/-- Defines well-founded stepping in terms of accessibility.

The relation used is `x R y ↔ x = step y ∧ y < stop`.
This way, when `y = stop`, there is no `x` such that `x R y`,
which serves as the base case for the `Acc` predicate.
But when `y < stop`, `step y R y`,
which forms a chain of accessibility to any `x ≤ stop`.
 -/
class WellFoundedStep (ι) [Step ι] extends LinearOrder ι where
  wf_step_le : ∀ stop, ∀ x, Acc (fun (x y : ι) => y < stop ∧ Step.step y = x) x

instance : WellFoundedStep Nat where
  wf_step_le stop := by
    intro x
    by_cases hx : x ≤ stop
    case neg =>
      constructor
      rintro - ⟨h,rfl⟩
      exfalso
      rw [Preorder.lt_iff_le_not_le] at h
      exact hx h.1
    case pos =>
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
      simp at h
    | succ i ih =>
      constructor
      rintro - ⟨-,rfl⟩
      have : (stop - i.succ) + 1 = (stop - i) := by omega
      conv => arg 2; simp [Step.step]; rw [this]
      clear this
      apply ih
      omega

instance [NeZero n] : WellFoundedStep (Fin n) where
  wf_step_le := by
    intro ⟨stop,hstop⟩ ⟨x,hxstop⟩
    by_cases hx : x ≤ stop
    case neg =>
      constructor
      rintro - ⟨h,rfl⟩
      exfalso
      rw [Preorder.lt_iff_le_not_le] at h
      exact hx h.1
    case pos =>
    simp at hx
    let diff := stop - x
    have : x = stop - diff := by
      rw [Nat.sub_sub_self]; exact hx
    have hdiff : diff ≤ stop := by omega
    clear_value diff; clear hx
    cases this
    induction diff with
    | zero =>
      constructor
      rintro - ⟨h,rfl⟩
      exfalso
      simp_all [Step.step]
    | succ i ih =>
      constructor
      rintro - ⟨-,rfl⟩
      have : stop - i.succ + 1 = (stop - i) := by omega
      have : (stop - i.succ + 1) % n = stop - i := by
        rw [this]; apply Nat.mod_eq_of_lt
        apply Nat.lt_of_le_of_lt; apply Nat.sub_le; exact hstop
      convert ih ?_ ?_
      · simp [Step.step, Fin.add_def, this]
      · omega
      · omega

instance : WellFoundedStep UInt8 where
  wf_step_le := by
    intro ⟨stop,hstop⟩ ⟨x,hxstop⟩
    by_cases hx : x ≤ stop
    case neg =>
      constructor
      rintro - ⟨h,rfl⟩
      exfalso
      rw [Preorder.lt_iff_le_not_le] at h
      exact hx h.1
    case pos =>
    simp at hx
    let diff := stop - x
    have : x = stop - diff := by
      rw [Nat.sub_sub_self]; exact hx
    have hdiff : diff ≤ stop := by omega
    clear_value diff; clear hx
    cases this
    induction diff with
    | zero =>
      constructor
      rintro - ⟨h,rfl⟩
      exfalso
      simp_all [Step.step]
    | succ i ih =>
      constructor
      rintro - ⟨-,rfl⟩
      have : stop - i.succ + 1 = (stop - i) := by omega
      have : (stop - i.succ + 1) % UInt8.size = stop - i := by
        rw [this]; apply Nat.mod_eq_of_lt
        apply Nat.lt_of_le_of_lt; apply Nat.sub_le; exact hstop
      convert ih ?_ ?_
      · simp [Step.step, UInt8.add_def, Fin.add_def, ← Fin.val_inj]; exact this
      · omega
      · omega

structure StepToRel (ι : Type u) where
  (start stop : ι)

instance [Step ι] [WellFoundedStep ι] : WellFoundedRelation (StepToRel ι) where
  rel := fun ⟨start,stop⟩ ⟨start',stop'⟩ =>
    stop = stop' ∧ Step.step start' = start ∧ start' < stop
  wf := by
    constructor
    rintro ⟨start,stop⟩
    simp
    have := WellFoundedStep.wf_step_le stop start
    induction this with
    | intro start _h ih =>
      constructor
      rintro ⟨start', stop'⟩
      simp
      rintro rfl rfl h
      simp_all

/-! ## Range Folds -/

section
variable [DecidableEq ι] [Step ι] [WellFoundedStep ι] [LawfulStep ι]

attribute [-instance] instSizeOf

def foldIncl (stop : ι) (f : β → ι → β) (i : ι) (acc : β) : β :=
  if i ≤ stop then
    aux i acc
  else
    acc
where
  aux (i acc) :=
    if i < stop then
      aux (Step.step i) (f acc i)
    else
      f acc i
  termination_by StepToRel.mk i stop

def foldExcl (stop : ι) (f : β → ι → β) (i : ι) (acc : β) : β :=
  if i < stop then
    foldExcl stop f (Step.step i) (f acc i)
  else
    acc
termination_by StepToRel.mk i stop

@[inline] def CC.foldl (_self : CC (ι := ι) l r) (f : β → ι → β) (acc : β) : β :=
  foldIncl r f l acc

@[inline] def OC.foldl (_self : OC (ι := ι) l r) (f : β → ι → β) (acc : β) : β :=
  foldIncl r f (Step.step l) acc

@[inline] def CO.foldl (_self : CO (ι := ι) l r) (f : β → ι → β) (acc : β) : β :=
  foldExcl r f l acc

@[inline] def OO.foldl (_self : OO (ι := ι) l r) (f : β → ι → β) (acc : β) : β :=
  foldExcl r f (Step.step l) acc

@[inline] def CI.foldl [Top ι] (_self : CI (ι := ι) l  ) (f : β → ι → β) (acc : β) : β :=
  foldIncl ⊤ f l acc

@[inline] def OI.foldl [Top ι] (_self : OI (ι := ι) l  ) (f : β → ι → β) (acc : β) : β :=
  foldIncl ⊤ f (Step.step l) acc

@[inline] def IC.foldl [Bot ι] (_self : IC (ι := ι) r  ) (f : β → ι → β) (acc : β) : β :=
  foldIncl r f ⊥ acc

@[inline] def IO.foldl [Bot ι] (_self : IO (ι := ι) r  ) (f : β → ι → β) (acc : β) : β :=
  foldExcl r f ⊥ acc

@[inline] def II.foldl [Top ι] [Bot ι] (_self : II (ι := ι)    ) (f : β → ι → β) (acc : β) : β :=
  foldIncl ⊤ f ⊥ acc

end
