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
import LeanColls.Array.ArrayUninit

namespace LeanColls

/-! # Fixed-length arrays

Represented as an `ArrayUninit`.
-/
structure Array (α : Type u) (n : Nat) : Type u where
  data : ArrayUninit α n n (Nat.le_refl _)

namespace Array

/-!
### Array.new

Build an array of length `n` where all elements are instantiated to `x`.
-/
def new (x : α) (n : Nat) : Array α n :=
  have res := Range.foldl'' ⟨n⟩
    (motive := fun i => Σ' h, Σ' (A : ArrayUninit α n i h),
      ∀ j hm, A.get j (Nat.lt_of_lt_of_le hm h) hm = x)
    (fun _ h_i ⟨_, A, h⟩ =>
      ⟨h_i, A.push x h_i, by
        intro j hm
        simp
        split; rfl; apply h⟩
    ) ⟨Nat.zero_le _, ArrayUninit.new n, by intro _ hj; contradiction⟩
  ⟨res.2.1⟩

/-!
### Array.init

Build an array of length `n` where element `i` is instantiated to `f i`.
-/
def init {α : Type u} {n : Nat} (f : Fin n → α) : Array α n :=
  have res := Range.foldl'' ⟨n⟩
    (motive := fun i => Σ' h, Σ' (A : ArrayUninit α n i h),
      ∀ j hm, A.get j (Nat.lt_of_lt_of_le hm h) hm =
              f ⟨j,(Nat.lt_of_lt_of_le hm h)⟩)
    (fun i h_i ⟨_, A, h⟩ =>
      ⟨h_i, A.push (f ⟨i,h_i⟩) h_i, by
        intro j hj
        simp
        have := Nat.lt_or_eq_of_le <| Nat.le_of_succ_le_succ hj
        cases this
        case inr hj => simp [hj]
        case inl hj =>
          simp [Nat.ne_of_lt hj]
          apply h⟩
    ) ⟨Nat.zero_le _, ArrayUninit.new n, by intro _ hj; contradiction⟩
  ⟨res.2.1⟩

/-!
### Array.get

Gets an element at the specified index. An array is uniquely characterized
by its `get` (see `Array.ext`).
-/
@[inline]
def get (A : @& Array α n) (i : @& Fin n) : α
  := A.data.get i.val i.isLt i.isLt

/-!
### Array.set

Sets the element at index `i` to `x`, throwing out the old value.
-/
@[inline]
def set {n : @& Nat} (A : Array α n) (i : @& Fin n) (x : α) : Array α n
  := ⟨A.data.set i i.isLt x⟩

/-!
## Extensionality & simp lemmas
-/

@[simp]
theorem ext {α n} {A B : Array α n} : A = B ↔ A.get = B.get
  := by
  constructor
  intro h; rw [h]
  intro h; cases A; cases B
  simp [get] at h ⊢
  funext i h_i _
  exact congrFun h ⟨i,h_i⟩

@[simp]
theorem get_new {x : α} {n} {i : Fin n}
  : get (new x n) i = x
  := by
  simp [get, new]
  generalize Range.foldl'' _ _ _ _ = res
  match res with
  | ⟨_, _, h⟩ =>
  simp
  apply h

@[simp]
theorem get_init {f : Fin n → α} {i}
  : get (init f) i = f i
  := by
  simp [get, init]
  generalize Range.foldl'' _ _ _ _ = res
  match res with
  | ⟨_, _, h⟩ =>
  simp
  apply h

theorem get_of_set_eq (f : Array α n) (i : Fin n) (x : α) {i' : Fin n} (h_i : i = i')
  : (f.set i x).get i' = x
  := by
  simp [get, set, ArrayUninit.get_set, h_i]

theorem get_of_set_ne (f : Array α n) (i : Fin n) (x : α) (j : Fin n) (h : i ≠ j)
  : (f.set i x).get j = f.get j
  := by
  simp [get, set]
  cases i; cases j
  simp at h ⊢
  simp [h]

@[simp]
theorem get_of_set (f : Array α n) (i : Fin n) (x : α) {i' : Fin n}
  : (f.set i x).get i' = if i = i' then x else f.get i'
  := by
  split
  apply get_of_set_eq; assumption
  apply get_of_set_ne; assumption

def empty : Array α 0 := init (Fin.elim0)

def copy {n : Nat} (A : Array α n) : Array α n
  := init A.get

@[simp]
theorem copy_def (A : Array α n) : A.copy = A
  := by
  simp [copy]
  funext i
  simp

def copyIfShared (A : Array α n) : Array α n :=
  if ArrayUninit.isExclusive A then A else copy A

@[simp]
theorem copyIfShared_def (A : Array α n) : A.copyIfShared = A
  := by
  simp [copyIfShared]


/-! ## Class instances -/

instance : Indexed (Array α n) α where
  size _ := n
  nth := Array.get

instance : IndexedOps (Array α n) α := default

instance : Initable (Array α n) n α where
  init := init

instance [N : Nonempty α] : Nonempty (Array α n) :=
  Nonempty.elim N (fun a => ⟨new a n⟩)

instance [Inhabited α] : Inhabited (Array α n) where
  default := new default n

instance : GetElem (Array α n) Nat α (fun _ i => i < n) where
  getElem A i h := A.get ⟨i,h⟩

/-! ## Misc -/

def toList (A : Array α n) : List α := FoldableOps.toList A

def ofList (L : List α) : Array α L.length :=
  have res :=
    (Range.mk L.length).foldl''
      (motive := fun i =>
        Σ' h, Σ' (acc : ArrayUninit α L.length i h) (rest : List α),
        rest = L.drop i ∧ ∀ j h_j,
        acc.get j (Nat.lt_of_lt_of_le h_j h) h_j =
          L.get ⟨j, Nat.lt_of_lt_of_le h_j h⟩)
      (fun i h ⟨_, acc, rest, h_rest, h_acc⟩ =>
        match rest with
        | [] => False.elim <| by
          have := List.length_drop i L
          rw [←h_rest] at this
          simp at this
          apply Nat.ne_of_lt h
          apply Nat.le_antisymm
          exact Nat.le_of_lt h
          exact Nat.sub_eq_zero_iff_le.mp this.symm
        | x::rest =>
          ⟨h, acc.push x h
          , rest
          , by
            have := h_rest.symm ▸ List.get_drop_eq_drop L i h
            have h_x : x = L[i]' h := by
              simp at this; exact this.1.symm
            have h_rest : rest = L.drop i.succ := by
              simp at this; exact this.2.symm
            constructor
            exact h_rest
            intro j h_j
            simp
            split
            subst_vars
            simp [getElem]
            apply h_acc
            ⟩
      )
      ⟨Nat.zero_le _, ArrayUninit.new _, L, by simp,
        by intro j hj; contradiction⟩
  ⟨res.2.1⟩

instance [Repr α] : Repr (Array α n) where
  reprPrec A prec := "LeanColls.Array.ofList " ++ reprPrec A.toList prec

instance [ToString α] : ToString (Array α n) where
  toString A := toString A.toList

@[simp]
theorem get_ofList (L : List α) (i)
  : get (ofList L) i = L.get i
  := by
  simp [get, ofList]
  generalize Range.foldl'' _ _ _ _ = res
  match res with
  | ⟨h, acc, rest, h_rest, h_acc⟩ =>
  simp
  apply h_acc

instance [Repr α] : Repr (Array α n) where
  reprPrec A prec := "Array.ofList " ++ reprPrec (α := List α) A.toList prec

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

@[simp]
def length (_ : Array α n) := n

@[simp]
theorem length_toList (A : Array α n)
  : A.toList.length = n
  := by simp [toList, Size.size]

private def memRangeToList_to_fin (i : {a // a ∈ Range.toList ⟨n⟩})
  : Fin n := ⟨i.val, by
    cases i; case mk i hi =>
    rw [Range.toList_eq_canonicalToList] at hi
    rw [←Range.memCorrect] at hi
    simp [Membership.mem] at hi
    exact hi⟩

theorem toList_get (A : Array α n) (i : Fin n)
  : A.get i = List.get A.toList ⟨i,by simp; exact i.isLt⟩
  := by
  simp [toList]
  rw [IndexedOps.get_toList_eq_get]
  simp [Indexed.nth]
  rfl

@[simp]
theorem toList_set (A : Array α n) (i : Fin n) (x : α)
  : (A.set i x).toList =
    List.set A.toList i x
  := by
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
