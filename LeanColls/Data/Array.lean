/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import Std.Data.Array.Lemmas
import Std.Data.List.Lemmas
import Mathlib.Data.Array.Lemmas
import Mathlib.Tactic.Ring

import LeanColls.Classes.Seq
import LeanColls.Data.List
import LeanColls.Data.Range
import LeanColls.Data.Transformer.FixSize

open LeanColls

namespace Array

def cons (x : α) (A : Array α) : Array α := #[x] ++ A

def snoc := @Array.push
def getSnoc? (A : Array α) :=
  if h : A.size > 0 then
    let x := A[A.size-1]'(tsub_lt_self h (by decide))
    some (A.pop, x)
  else
    none

theorem ext_iff (A B : Array α) (h : A.size = B.size) : A = B ↔ ∀ (i : Nat) h1 h2, A[i]'h1 = B[i]'h2 := by
  constructor
  · rintro rfl; simp
  · apply ext _ _ h

theorem ext'_iff (A B : Array α) : A = B ↔ A.data = B.data := by
  cases A; cases B; simp

instance : ToList (Array α) α where
  toList := Array.toList

instance : Seq (Array α) α where
  ofFn := Array.ofFn
  size := Array.size
  empty := Array.empty
  insert := Array.push
  singleton := Array.singleton
  fold c f init := Array.foldl f init c
  get := Array.get
  set := Array.set
  cons := Array.cons
  snoc := Array.push
  getSnoc? := Array.getSnoc?

instance : LawfulSeq (Array α) α where
  mem_iff_mem_toList := by simp [LeanColls.toList, mem_def]
  toList_append := by simp [LeanColls.toList]
  toMultiset_empty := by
    simp [LeanColls.toList, ToMultiset.toMultiset, LeanColls.empty, empty]
  toMultiset_insert := by
    simp [LeanColls.toList, ToMultiset.toMultiset, LeanColls.insert]
  toMultiset_singleton := by
    simp [LeanColls.toList, ToMultiset.toMultiset, LeanColls.singleton]
  size_def := by
    simp [LeanColls.toList, LeanColls.size]
  toList_ofFn := by
    simp [LeanColls.toList, Seq.ofFn, List.ofFn]
  get_def := by
    rintro c ⟨i,hi⟩
    simp [LeanColls.toList, Seq.get]
    rw [getElem_eq_data_get, ← Option.some_inj,
      ← List.get?_eq_get, ← List.get?_eq_get, toList_eq]
  toList_set := by
    rintro c ⟨i,hi⟩ x
    simp [LeanColls.toList, Seq.set]
  getCons?_eq_none := by
    intro ⟨L⟩
    simp [LeanColls.toList, Seq.getCons?]
    split <;> simp <;> cases L <;> simp at *
  getCons?_eq_some := by
    intro ⟨L⟩ x ⟨L'⟩
    cases L
    · simp [LeanColls.toList, Seq.getCons?]
      intro h; split at h; simp_all; rw [size_eq_length_data] at *; simp at *
    next hd tl =>
    simp [LeanColls.toList, Seq.getCons?, getElem_eq_data_get]
    split <;> simp_all [size_mk]
    rintro rfl
    constructor
    · intro h
      have := congrArg size h
      simp at this; cases this
      have : List.length tl = List.length L' := by
        clear h; simp_all [size_mk]
      rw [Array.ext_iff] at h
      · simp at h; simp [getElem_eq_data_get] at h
        apply List.ext_get
        · assumption
        intro i h1 h2
        apply h i (this ▸ h1) h2
      · simp
    · rintro rfl
      rw [Array.ext_iff]
      · simp; simp [getElem_eq_data_get]
      · simp; simp_all [size_mk]
  getSnoc?_eq_none := by
    simp [LeanColls.toList, Seq.getSnoc?]
    rintro ⟨L⟩; simp [getSnoc?]; exact List.length_eq_zero
  getSnoc?_eq_some := by
    rintro ⟨L⟩ x ⟨L'⟩
    simp [LeanColls.toList, Seq.getSnoc?, getSnoc?]
    split <;> simp_all [List.length_eq_zero]
    simp [pop]
    rw [getElem_eq_data_get, ← List.getLast_eq_get L (List.ne_nil_of_length_pos ‹_›)]
    constructor
    · rintro ⟨rfl,rfl⟩
      simp only [List.dropLast_append_getLast]
    · rintro rfl
      simp only [List.dropLast_concat, List.getLast_append, and_self]
  toList_update := by
    rintro ⟨c⟩ ⟨i,h⟩ f
    simp [Seq.update, LeanColls.toList, getElem_eq_data_get]
    congr 2; apply List.get_eq_get
    · rw [toList_eq]
    · simp
  toList_cons := by
    simp [LeanColls.toList, Seq.cons, cons]
  toList_snoc := by
    simp [LeanColls.toList, Seq.snoc, snoc]

end Array

abbrev NArray (α : Type u) (n : Nat) := FixSize (Array α) n

/-! ### Scalar Arrays -/

namespace ByteArray

instance : ToList ByteArray UInt8 where
  toList := toList

instance : Fold ByteArray UInt8 where
  fold arr := arr.foldl
  foldM arr := arr.foldlM

instance : Fold.ToList ByteArray UInt8 where
  -- JG: silly me, thinking someone had proven even a single theorem about ByteArray.foldl
  fold_eq_fold_toList := by sorry
  foldM_eq_foldM_toList := by sorry

instance : Seq ByteArray UInt8 where
  size := size
  get := get
  set := set
  empty := empty
  insert := push
  ofFn := ofFn
  snoc := push
  -- TODO(JG): implement bytearray append directly

-- JG: again, silly me, thinking anyone has proven anything about ByteArray at all
/-
instance : LawfulSeq ByteArray UInt8 where
  toList_append := sorry
  toMultiset_empty := sorry
  toMultiset_insert := sorry
  toMultiset_singleton := by
    simp [LeanColls.singleton, ToMultiset.toMultiset, LeanColls.toList]
    sorry -- ... yikes..
  size_def := by
    intros; simp [LeanColls.size, LeanColls.toList]
    sorry -- ...
-/

end ByteArray

namespace FloatArray

instance : ToList FloatArray Float where
  toList := toList

instance : Fold FloatArray Float where
  fold arr := arr.foldl
  foldM arr := arr.foldlM

def append (A1 A2 : FloatArray) : FloatArray :=
  aux A1 0
where aux (acc : FloatArray) (i : Nat) : FloatArray :=
  if _h : i < A2.size then
    aux (acc.push A2[i]) (i+1)
  else
    acc
termination_by aux _ i => A2.size - i

instance : Append FloatArray where
  append := append

def ofFn (f : Fin n → Float) : FloatArray :=
  aux (FloatArray.mkEmpty n) 0
where aux (acc : FloatArray) (i : Nat) : FloatArray :=
  if h : i < n then
    aux (acc.push (f ⟨i,h⟩)) (i+1)
  else
    acc
termination_by aux i _ => n - i

instance : Seq FloatArray Float where
  size := size
  get := get
  set := set
  empty := empty
  insert := push
  ofFn := ofFn
  snoc := push
  append := append

theorem ext (A1 A2 : FloatArray) : A1.data = A2.data → A1 = A2 := by
  cases A1; cases A2; simp

theorem ext_iff (A1 A2 : FloatArray) : A1 = A2 ↔ A1.data = A2.data := by
  constructor
  · rintro rfl; rfl
  · apply ext

theorem append.aux_eq_acc_append (A2 : FloatArray) (acc : FloatArray) (i : Nat)
  : (aux A2 acc i).data = acc.data ++ (aux A2 FloatArray.empty i).data := by
  if i < A2.size then
    let j := size A2 - i
    have : i = size A2 - j := by
      simp; rw [Nat.sub_sub_self]; apply Nat.lt_succ.mp (Nat.le.step _); assumption
    rw [this]; clear this
    have : j ≤ size A2 := by simp
    generalize j = j' at *; clear j; clear! i
    induction j' generalizing acc with
    | zero => unfold aux; simp [empty, mkEmpty]
    | succ j ih =>
      unfold aux
      have : size A2 - j.succ < size A2 := by omega
      have : size A2 - j.succ + 1 = size A2 - j := by omega
      simp [*]
      have : j ≤ size A2 := Nat.le_of_lt ‹_›
      conv => lhs; rw [ih _ ‹_›]
      conv => rhs; rw [ih _ ‹_›]
      rw [←Array.append_assoc]
      congr 1
  else
    unfold aux
    simp [*, empty, mkEmpty]

theorem append.aux_fromEmpty (A : FloatArray)
  : (aux A FloatArray.empty 0).data = A.data := by
  rcases A with ⟨A⟩
  suffices ∀ i, i ≤ A.size → (aux ⟨A⟩ empty (A.size - i)).data = ⟨A.data.drop (A.size - i)⟩ by
    have := this A.size (Nat.le_refl _)
    simpa using this
  intro i hi
  induction i with
  | zero => unfold aux; simp [size, empty, mkEmpty]; rfl
  | succ i ih =>
    specialize ih (Nat.le_of_lt hi)
    unfold aux
    have : A.size - i.succ < A.size := by omega
    have : A.size - i.succ + 1 = A.size - i := by omega
    simp [size, *]
    rw [append.aux_eq_acc_append, ih, Array.ext'_iff]
    simp [push, empty, mkEmpty]
    have : A.size - i.succ < A.data.length := by omega
    conv => rhs; rw [List.drop_eq_get_cons ‹_›]
    congr 2
    omega

@[simp] theorem data_append (A1 A2 : FloatArray) : (A1 ++ A2).data = A1.data ++ A2.data := by
  rcases A1 with ⟨A1⟩
  rcases A2 with ⟨A2⟩
  simp [instAppendFloatArray, instHAppend, append]
  rw [append.aux_eq_acc_append, append.aux_fromEmpty]
  rfl


theorem ofFn.aux_spec (f : Fin n → Float) (acc : FloatArray) (i : Nat) (hi : i ≤ n)
  : aux f acc i = acc ++ ⟨Array.ofFn (fun (j : Fin (n-i)) => f (j.addNat i |>.cast (by omega)))⟩ := by
  have hi' := hi
  revert hi acc
  apply Nat.decreasingInduction' (n := n) (P := fun i => ∀ acc (hi : i ≤ n), aux f acc i = _)
  · intro j jlt _ilej ih acc hi
    unfold aux
    simp only [jlt, dite_true]
    rw [ih _ jlt, ext_iff]
    rw [Array.ext'_iff]
    simp [push]
    rw [←List.ofFn_def, ←List.ofFn_def]
    have := List.ofFn_succ (fun (x : Fin (n - j.succ + 1)) => f (x.addNat j |>.cast (by omega)))
    convert this.symm using 1 <;> clear this
    · simp; constructor
      · congr; simp
      · funext x
        congr 1; simp [Fin.eq_iff_veq]; ring
    · apply List.ext_get
      · simp; omega
      · intro x h1 h2; simp
  · assumption
  · intro acc _
    unfold aux
    simp; cases acc; rw [ext_iff]; simp
    suffices Array.ofFn _ = #[] by
      rw [this]; simp
    rw [Array.ext'_iff]
    simp
    apply List.eq_nil_of_length_eq_zero
    simp

-- Not even going to try to write out the lawfulseq instance...

end FloatArray
