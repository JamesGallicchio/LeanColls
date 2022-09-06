/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes
import LeanColls.Range
import LeanColls.IndexedOps
import LeanColls.Uninit
import LeanColls.AuxLemmas
import LeanColls.View

namespace LeanColls

@[extern "leancolls_array_initialize"] private opaque arrayInit : IO Unit

builtin_initialize arrayInit

structure Array (α : Type u) (n : Nat) : Type u where
  data : (i : Fin n) → α

namespace Array

instance [Inhabited α] : Inhabited (Array α n) where
  default := ⟨fun _ => default⟩

-- External functions

@[extern "leancolls_array_new_uninit"]
def newUninit (n : Nat) : Array (Uninit α) n
  := ⟨λ _ => Uninit.uninit⟩

@[extern "leancolls_array_new"]
def new (x : @&α) (n : @& Nat) : Array α n
  := ⟨λ _ => x⟩

@[extern "leancolls_array_get"]
def get {α} {n : @& Nat}
        (A : @& Array α n) (i : @& Fin n) : α
  := A.data i

@[extern "leancolls_array_set"]
def set {α} {n : @& Nat}
        (A : Array α n) (i : @& Fin n) (x : α)
  : Array α n
  := ⟨λ a => if a = i then x  else A.data a⟩

@[extern "leancolls_array_resize"]
def resize {α} {n : @& Nat} (A : Array α n)
          (x : @&α) (m : @& Nat)
  : Array α m
  := ⟨λ i => if h:i < n
    then A.data ⟨i,h⟩
    else x⟩

unsafe def allInitUnsafe (A : Array (Uninit α) n)
  (_ : ∀ i, (A.get i).isInit) : Array α n
  := unsafeCast A
@[implementedBy allInitUnsafe]
def allInit (A : Array (Uninit α) n)
  (h : ∀ i, (A.get i).isInit) : Array α n
  := ⟨λ i => Uninit.getValue (A.get i) (h i)⟩

-- Axioms

/- This axiom holds, because instantiating an array of at least `USize.size`
  will cause the program to panic -/
axiom size_lt_usize {α n} : Array α n → n < USize.size

-- Preliminary theorems
theorem get_of_set_eq (f : Array α n) (i : Fin n) (x : α) {i' : Fin n} (h_i : i = i')
  : (f.set i x).get i' = x
  := by unfold get; unfold set; simp [h_i, Function.update, cast]

theorem get_of_set_ne (f : Array α n) (i : Fin n) (x : α) (j : Fin n) (h : i ≠ j)
  : (f.set i x).get j = f.get j
  := by
    unfold get; unfold set
    simp [Function.update]
    split
    exact False.elim $ h (by apply Eq.symm; assumption)
    rfl

@[simp]
theorem get_of_set (f : Array α n) (i : Fin n) (x : α) {i' : Fin n}
  : (f.set i x).get i' = if i = i' then x else f.get i'
  := by
  split
  apply get_of_set_eq; assumption
  apply get_of_set_ne; assumption

/-!
### Array.init

Utility function necessary to provide a runtime implementation
for `Array.mk`.
-/
@[inline]
def init {α : Type u} {n : Nat} (f : Fin n → α) : Array α n
  :=
  Range.foldl' ⟨n⟩ (λ A' i h => A'.set ⟨i,h⟩ (.init $ f ⟨i,h⟩)) (newUninit n)
  |>.allInit (by
    intro i
    cases i; case mk i hi =>
    simp [newUninit]
    suffices ∀ n' (hn : ∀ {i}, i < n' → i < n) (_ : i < n'),
      Uninit.isInit (
        get
          (Range.foldl'
            ⟨n'⟩
            (fun A i h => A.set ⟨i, hn h⟩ (.init $ f ⟨i, hn h⟩))
            (⟨λ _ => Uninit.uninit⟩ : Array (Uninit α) n))
          ⟨i, hi⟩)
      from this n (by simp) hi
    intro n' hn hi'
    induction n' with
    | zero =>
      contradiction
    | succ n' ih =>
      simp at hi
      simp [Range.foldl']
      match Nat.eq_or_lt_of_le hi' with
      | .inl h =>
        cases h
        simp
      | .inr h =>
        have : i < n' := Nat.le_of_succ_le_succ h
        simp [(Nat.ne_of_lt this).symm]
        apply ih
        exact this
    )

/-!
Implement the auto-generated `mk` and `data` functions with
actually-correct implementations above. This seals up all
routes to interact with the `Array`, ensuring safety.
-/
attribute [implementedBy init] Array.mk
def dataImpl {α : Type u} {n : Nat}
        (A : Array α n) (i : Fin n) : α
  := A.get i
attribute [implementedBy dataImpl] Array.data
def recImpl.{u_1,u}
  : {α : Type u} → {n : Nat} → {motive : Array α n → Sort u_1} →
    ((data : Fin n → α) → motive ⟨data⟩) →
    (t : Array α n) → motive t
  := λ f A => f (data A)
attribute [implementedBy recImpl] Array.rec

theorem init_eq_mk {f : Fin n → α}
  : init f = Array.mk f
  := by
    simp [init, forIn, Foldable.fold, Id.run, allInit]
    apply funext; intro i
    cases i; case mk i hi =>
    suffices ∀ n' (hn : ∀ {i}, i < n' → i < n) (hi' : i < n'),
      Uninit.getValue?
        (get (Range.foldl' ⟨n'⟩ (fun A' i h =>
                set A' ⟨i,hn h⟩ (Uninit.init (f ⟨i,hn h⟩))
              ) (newUninit n)
          ) ⟨i, hn hi'⟩)
        = some (f ⟨i, hi⟩)
      by
      apply Uninit.getValue_of_getValue?_some
      exact this n (by simp) hi
    intro n' hn hi'
    induction n' with
    | zero =>
      contradiction
    | succ n' ih =>
      simp [Range.foldl']
      match Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ hi') with
      | .inl hi' =>
        cases hi'
        simp [Uninit.getValue?_init]
      | .inr hi' =>
        simp [(Nat.ne_of_lt hi').symm]
        apply ih
        assumption

def empty : Array α 0 := init (Fin.elim0)

def copy {n : Nat} (A : Array α n) : Array α n
  := init A.get

theorem copy_def (A : Array α n) : A.copy = A
  := by
  simp [copy, init_eq_mk]
  rfl

instance : Indexed (Array α n) α where
  size _ := n
  nth := Array.get

instance : IndexedOps (Array α n) α := default

def toList (A : Array α n) : List α := FoldableOps.toList A

instance [Repr α] : Repr (Array α n) where
  reprPrec A := reprPrec (α := List α) A.toList

@[simp]
theorem canonicalToList_eq_toList (A : Array α n)
  : canonicalToList (Foldable.fold A) = A.toList
  := by
  unfold toList
  rw [IndexedOps.toList_eq_default_toList,
    FoldableOps.default_toList_eq_canonicalToList]

@[simp]
theorem size_set (A : Array α n) (i : Fin n) (x : α)
  : Size.size (A.set i x) = Size.size A
  := by simp [Size.size]

private def memRangeToList_to_fin (i : {a // a ∈ Range.toList ⟨n⟩})
  : Fin n := ⟨i.val, by
    cases i; case mk i hi =>
    rw [Range.toList_eq_canonicalToList] at hi
    rw [←Range.memCorrect] at hi
    simp [Membership.mem] at hi
    exact hi⟩

@[simp]
theorem toList_set (A : Array α n) (i : Fin n) (x : α)
  : (A.set i x).toList =
    List.set A.toList i x
  := set_option trace.Meta.isDefEq false in by
  simp [toList]
  rw [IndexedOps.toList_eq_range_toList_map]
  case hL => simp [Foldable.fold, ←Range.toList_eq_canonicalToList]
  rw [IndexedOps.toList_eq_range_toList_map]
  case hL => simp [Foldable.fold, ←Range.toList_eq_canonicalToList]
  have :
    canonicalToList (Range.mk (Size.size (A.set i x))).foldl
    = Range.toList ⟨n⟩ := by
    simp [Size.size, Range.toList_eq_canonicalToList]
  rw [List.map'_rw _ this]
  have :
    canonicalToList (Range.mk (Size.size A)).foldl
    = Range.toList ⟨n⟩ := by
    simp [Size.size, Range.toList_eq_canonicalToList]
  rw [List.map'_rw _ this]
  simp [Indexed.nth]
  rw [Range.set_map'_toList]
  congr
  funext j hj
  simp at hj
  cases i; case mk i hi =>
  split
  case inl h =>
    simp at h; simp [h]
  case inr h =>
    simp at h; simp [Ne.symm h]
