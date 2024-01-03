/-
Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Data.Array
import LeanColls.Util.Cached

import Mathlib.Data.Nat.Order.Lemmas

/-!
# Radix Balanced Finger Trees

An implementation of persistent vectors which has fast random
access, fast cons/snoc, and reasonable performance on most other
vector operations.

The implementation is an N-dimensional hypercube where all sides
are `WIDTH` wide. The first and last slice of the highest
dimension can be just partially filled, and are implemented as
"fingers" that provide O(1) access to the first/last elements.

The interior layers of the hypercube are completely full.
This allows for rapid index calculations, like a radix trie.
We also store incremental sizes at each joint of the fingers
to allow faster indexing calculations within the fingers.


## References

See the [Scala issue on GitHub](https://github.com/scala/scala/pull/8534)
introducing this collection. There are no formal references.
-/

open LeanColls Util

namespace LeanColls.Data.RBFT

@[inline] opaque WIDTH_PRED : Nat := 31
@[inline] def WIDTH : Nat := WIDTH_PRED.succ
@[simp] theorem WIDTH_pos : 0 < WIDTH := Nat.zero_lt_succ _

/- A hypercube array with `n` dimensions, each
  `WIDTH` wide, e.g. a total capacity of `WIDTH ^ n`
-/
def HyperArray (α : Type u) : Nat → Type u
| 0   => α
| n+1 => NArray (HyperArray α n) WIDTH

namespace HyperArray

variable {α : Type u}

@[inline, simp]
def size (_ : HyperArray α n) : Nat := WIDTH ^ n

def ofFn : {n : Nat} → (Fin (WIDTH ^ n) → α) → HyperArray α n
| 0, f => f ⟨0, by simp⟩
| n+1, f => Indexed.ofFn (C := NArray _ _) fun ⟨i,hi⟩ => ofFn fun ⟨j,hj⟩ =>
    f ⟨i*j, by rw [Nat.pow_succ, Nat.mul_comm]; apply mul_lt_mul'' hj hi; repeat simp⟩

def get : {n : Nat} → HyperArray α n → (i : Fin (WIDTH ^ n)) → α
| 0,   a, ⟨0,_⟩   => a
| n+1, A, ⟨i,h_i⟩ =>
  let q := i / WIDTH^n
  let r := i % WIDTH^n
  have h_q : q < WIDTH := Nat.div_lt_of_lt_mul h_i
  have h_r : r < WIDTH^n :=
    Nat.mod_lt _ (Nat.pos_pow_of_pos _ (by simp))
  let next := Indexed.get.{u,0,u} (C := NArray ..) A ⟨q, h_q⟩
  get next ⟨r, h_r⟩

@[simp] theorem get_ofFn (f : Fin (WIDTH ^ n) → α)
  : get (ofFn f) = f := by
  ext i
  induction n with
  | zero =>
    match i with
    | ⟨0,_⟩ => simp [get, ofFn]
  | succ n ih =>
    sorry

/- todo: make a tailrec version of this
that uses a heterogeneous stack -/
def set : {n : Nat} → HyperArray α n → (i : Fin (WIDTH ^ n)) → α → HyperArray α n
| 0,   _, ⟨0,_⟩  , a => a
| n+1, A, ⟨i,h_i⟩, a =>
  let q := i / WIDTH^n
  let r := i % WIDTH^n
  have h_q : q < WIDTH := Nat.div_lt_of_lt_mul h_i
  have h_r : r < WIDTH^n :=
    Nat.mod_lt _ (Nat.pos_pow_of_pos _ (by simp))
  Indexed.update (C := NArray ..) A ⟨q, h_q⟩
  <| λ A' => set A' ⟨r, h_r⟩ a

theorem get_set {n : Nat} (A : HyperArray α n) (i x j)
  : (A.set i x |>.get j) = if i = j then x else A.get j
  := by
  induction n with
  | zero =>
    match i,j with
    | ⟨0,_⟩, ⟨0,_⟩ =>
    simp [set, get]
  | succ n ih =>
    generalize hqi : i / WIDTH^n = qi
    generalize hri : i % WIDTH^n = ri
    generalize hqj : j / WIDTH^n = qj
    generalize hqj : j % WIDTH^n = rj
    unfold set; unfold get
    simp [*]
    generalize hqif : Fin.mk qi _ = qif
    generalize hrif : Fin.mk ri _ = rif
    generalize hqjf : Fin.mk qj _ = qjf
    generalize hrjf : Fin.mk rj _ = rjf
    rw [LawfulIndexed.get_update]
    split
    next h =>
      rw [ih]
      cases h
      congr 1
      subst_vars
      rcases i with ⟨i,hi⟩; rcases j with ⟨j,hj⟩
      simp at hqjf ⊢
      refine ⟨?_, fun | rfl => rfl⟩
      intro h
      have := (Nat.div_mod_unique ?_).mp ⟨hqjf.symm, h⟩
      · rw [Nat.add_comm, Nat.div_add_mod] at this
        exact this.1.symm
      simp
    next h =>
      suffices i ≠ j by simp [this]
      intro contra
      subst_vars
      simp at h

instance : Indexed (HyperArray α n) (Fin (WIDTH ^ n)) α := {
  ofFn := ofFn
  get := get
  set := set
  update := fun A i f => set A i (f (get A i))
  toMembership := sorry
  toToMultiset := sorry
  toFold := sorry
}

instance : LawfulIndexed (HyperArray α n) (Fin (WIDTH ^ n)) α where
  get_ofFn := get_ofFn
  get_set := get_set
  get_update := by simp [Indexed.update, Indexed.get, get_set]

end HyperArray

structure HyperRect (α : Type u) (n : Nat) : Type u where
  (backing : Array (HyperArray α n))
  (size : Cached (size backing * WIDTH ^ n))

namespace HyperRect

@[simp] def width (A : HyperRect α n) := A.backing.size

def ofArray (backing : Array (HyperArray α n)) : HyperRect α n :=
  ⟨backing, cached _⟩

def empty : HyperRect α n := ofArray (Array.empty)

@[simp] theorem size_empty : Array.size (@empty α n).backing = 0 := rfl

def singleton (A : HyperArray α n) : HyperRect α n :=
  ⟨Array.singleton A, cached _⟩

def fullToHyperArray : (r : HyperRect α n) → r.width = WIDTH → HyperArray α n.succ
| ⟨backing, _⟩, (h : backing.size = WIDTH) =>
  Seq.fixSize backing |>.cast h

def get : (A : HyperRect α n) → Fin (size A) → α
| ⟨A,_⟩, ⟨i,h_i⟩ =>
  let q := i / WIDTH^n
  let r := i % WIDTH^n
  have h_q := by
    simp at h_i
    convert Nat.div_lt_div_of_lt_of_dvd _ h_i
    · simp
    · simp
  have h_r := Nat.mod_lt _ (Nat.pos_pow_of_pos _ $ by simp)
  Seq.get A ⟨q, h_q⟩
  |>.get ⟨r, h_r⟩

def set : (A : HyperRect α n) → Fin A.size → α → HyperRect α n
| ⟨A,size⟩, ⟨i,h_i⟩, a =>
  let q := i / WIDTH^n
  let r := i % WIDTH^n
  have h_q := by
    simp at h_i
    convert Nat.div_lt_div_of_lt_of_dvd _ h_i
    · simp
    · simp
  have h_r := Nat.mod_lt _ (Nat.pos_pow_of_pos _ $ by simp)
  ⟨ Seq.update A ⟨q, h_q⟩ <| λ A' => A'.set ⟨r, h_r⟩ a,
    cached' size (by simp)⟩

def cons : HyperArray α n → HyperRect α n → HyperRect α n
| x, ⟨A,size⟩ =>
  ⟨Seq.cons x A,
    cached' (size.val + WIDTH ^ n) (by simp [Nat.succ_mul])⟩

def snoc : HyperRect α n → HyperArray α n → HyperRect α n
| ⟨A,size⟩, x =>
  ⟨Seq.snoc A x,
    cached' (size.val + WIDTH ^ n) (by simp [Nat.succ_mul])⟩

def cons? : HyperRect α n → Option (HyperArray α n × HyperRect α n)
| ⟨A,size⟩ =>
  match h : Seq.cons? A with
  | none => none
  | some (x, A') =>
    some (x, ⟨A', cached' (size - WIDTH^n) (by
      have := congrArg Size.size <| Seq.cons?_eq_some _ _ _ h
      simp [Seq.size_toList]
      simp [Nat.mul_sub_right_distrib])⟩)

def snoc? : HyperRect α n → Option (HyperRect α n × HyperArray α n)
| ⟨A, size⟩ =>
  if h : A.size > 0 then
    let (A', x) := NArray.ofArray A
      |>.cast (Nat.sub_add_cancel h).symm |>.back
    some (⟨A'.data, cached' (size - WIDTH^n) (by
      simp [A'.hsize, Nat.mul_sub_right_distrib])⟩, x)
  else
    none

end HyperRect


/--
## FingerList

A linked-list-like representation of the prefix/suffix fingers.
A `FingerList τ n m` is a list of `HyperRect τ i`s for `m ≤ i < n`.
-/
inductive FingerList (τ : Type u) (n : Nat) : Nat → Type u
| base  : FingerList τ n n
| joint : (hd : HyperRect τ m) → (tl : FingerList τ n m.succ)
          → FingerList τ n m

namespace FingerList

theorem upperBound (L : FingerList τ n m) : m ≤ n := by
  induction L
  apply Nat.le_refl
  apply Nat.le_of_lt
  assumption

theorem upperBound_zero_base (L : FingerList τ 0 0) : L = base := by
  match L with
  | base => rfl
  | joint hd tl =>
    have := upperBound tl
    contradiction

def size : FingerList τ n m → Nat
| base => 0
| joint hd tl => hd.size + tl.size

def validList : FingerList τ n m → Bool
| base => true
| joint hd tl =>
  hd.width ≤ WIDTH && validList tl

def isFull : FingerList τ n m → Bool
| base => true
| joint hd tl =>
  hd.width = WIDTH && isFull tl

def extend (new : HyperRect τ n) : FingerList τ n m → FingerList τ n.succ m
| base => joint new base
| joint hd tl => joint hd (extend new tl)

def unextend : {n m : Nat} → m ≤ n → FingerList τ n.succ m → HyperRect τ n × FingerList τ n m
| _, _, h, base => False.elim (Nat.ne_of_lt h rfl)
| _, _, _h, joint hd base => (hd, base)
| n, m, _h, joint hd (joint hd' tl') =>
  have : m.succ ≤ n := Nat.le_of_succ_le_succ (upperBound tl')
  let (x, tl) := unextend this (joint hd' tl')
  (x, joint hd tl)

/--
getL
Indexes into L from the left; e.g. 0 is the top-left
element, and `L.size - 1` is the bottom right's last element.
-/
def getL : (L : FingerList τ n m) → (h_L : L.validList)
          → (i : Nat) → (h_i : i < L.size)
          → τ
| base, _, _, h_i =>
  by exfalso; simp [size] at h_i
| joint hd tl, h_L, i, h_i =>
  if h : i < hd.size then
    hd.get ⟨i, h⟩
  else
    getL tl
      (by simp [validList] at h_L; exact h_L.right)
      (i - hd.size)
      (by
        simp [size] at h_i h ⊢
        exact Nat.sub_lt_left_of_lt_add h h_i)

/-- See `getL` -/
def setL : (L : FingerList τ n m) → (h_L : L.validList)
          → (i : Nat) → (h_i : i < L.size)
          → τ → FingerList τ n m
| base, _, _, h_i, a =>
  by exfalso; simp [size] at h_i
| joint hd tl, h_L, i, h_i, a =>
  if h : i < hd.size then
    joint (hd.set ⟨i, h⟩ a) tl
  else
    joint hd <|
      setL tl (by
        simp [validList] at h_L
        exact h_L.right)
        (i - hd.size)
        (by
          simp [size] at h_i h ⊢
          apply Nat.sub_lt_left_of_lt_add h h_i)
        a

theorem valid_setL_of_valid (L : FingerList τ n m) (h_L : L.validList)
          (i : Nat) (h_i : i < L.size) (x : τ)
  : validList (setL L h_L i h_i x)
  := by
  induction L generalizing i with
  | base =>
    simp [size] at h_i
  | joint hd tl ih =>
    simp [setL]
    split <;> (
      simp [validList, HyperRect.set] at h_L ⊢
      simp [h_L, ih]
    )

def size_setL (L : FingerList τ n m) (h_L : L.validList)
          (i : Nat) (h_i : i < L.size) (x : τ)
  : size (setL L h_L i h_i x) = size L
  := by
  induction L generalizing i with
  | base =>
    simp [size] at h_i
  | joint hd tl ih =>
    simp [setL]
    split <;> (
      simp_all [HyperRect.set, size, ih]
    )

/-- getR
Indexes into `L` from the right, e.g. 0 is the top-right
element and `L.size-1` is the bottom-left's first element.
-/
def getR : (L : FingerList τ n m) → (h_L : L.validList)
          → (i : Nat) → (h_i : i < L.size)
          → τ
| base, _, _, h_i =>
  by simp [size] at h_i
| joint hd tl, h_L, i, h_i =>
  if h : i < hd.size then
    hd.get ⟨hd.size - i.succ, by
      simp at *; apply Nat.sub_lt; apply Nat.lt_of_le_of_lt ?_ h; simp; simp⟩
  else
    getR tl
      (by simp [validList] at h_L; exact h_L.right)
      (i - hd.size)
      (by
        simp [size] at h_i h ⊢
        apply Nat.sub_lt_left_of_lt_add h h_i)

/-- See `getR` -/
def setR : (L : FingerList τ n m) → (h_L : L.validList)
          → (i : Nat) → (h_i : i < L.size)
          → τ → FingerList τ n m
| base, _, _, h_i, a =>
  by simp [size] at h_i
| joint hd tl, h_L, i, h_i, a =>
  if h : i < hd.size then
    let hd' := hd.set ⟨hd.size - i.succ, by
      simp at *
      apply Nat.sub_lt
      apply Nat.lt_of_le_of_lt ?_ h
      simp
      simp⟩
      a
    joint hd' tl
  else
    joint hd <|
      setR tl
        (by
          simp [validList] at h_L
          exact h_L.right)
        (i - hd.size)
        (by
          simp [size] at h_i h ⊢
          apply Nat.sub_lt_left_of_lt_add h h_i)
        a

theorem valid_setR_of_valid (L : FingerList τ n m) (h_L : L.validList)
          (i : Nat) (h_i : i < L.size) (x : τ)
  : validList (setR L h_L i h_i x)
  := by
  induction L generalizing i with
  | base =>
    simp [size] at h_i
  | joint hd tl ih =>
    simp [setR]
    split <;> (
      simp [validList, HyperRect.set] at h_L ⊢
      simp [h_L, ih]
    )

def size_setR (L : FingerList τ n m) (h_L : L.validList)
          (i : Nat) (h_i : i < L.size) (x : τ)
  : size (setR L h_L i h_i x) = size L
  := by
  induction L generalizing i with
  | base =>
    simp [size] at h_i
  | joint hd tl ih =>
    simp [setR]
    split <;> (
      simp_all [size, ih, HyperRect.set]
    )


/- Pushes `x` onto `L` from the left at the top joint (small element).
If `L` is full, returns the (full) bottom joint as a `HyperArray τ n`
and shifts everything else down to accommodate `x`.
-/
def consL (x : HyperArray τ m) : (L : FingerList τ n m) → L.validList →
    FingerList τ n m × Option (HyperArray τ n)
| base, _ => (base, some x)
| joint hd tl, h_L =>
    if h : hd.width < WIDTH then
      (joint (hd.cons x) tl, none)
    else
      have ⟨h_w, h_tl⟩ : hd.width ≤ WIDTH ∧ tl.validList := by
        simpa [validList] using h_L
      have h_w : hd.width = WIDTH := by
        apply Nat.le_antisymm
        exact h_w
        exact Nat.ge_of_not_lt h
      let newSlice : HyperArray τ (m + 1) :=
        hd
        |>.fullToHyperArray h_w
      let (fl, excess) := consL newSlice tl h_tl
      (joint ⟨Array.singleton x, cached' (WIDTH ^ m) (by simp)⟩ fl,
        excess)

theorem valid_consL (x : HyperArray τ m) (L : FingerList τ n m) (h_L : L.validList)
  : let ⟨L',_⟩ := L.consL x h_L
    L'.validList
  := by
  induction L with
  | base =>
    simp [consL, h_L]
  | joint hd tl ih =>
    simp [consL]
    simp [validList] at h_L
    split
    case inl m' h =>
      simp [validList]
      simp [HyperRect.cons, h_L]
      exact h
    case inr m' h =>
      split
      case _ _ h_w h_tl _ =>
      simp [validList]
      constructor
      case left  => exact WIDTH_pos
      case right =>
      apply ih

theorem size_consL (x : HyperArray τ m) (L : FingerList τ n m) (h_L : L.validList)
  {L' excess} (h_L' : L.consL x h_L = (L', excess))
  : L'.size + (match excess with
      | none => 0
      | some e => HyperArray.size e
    ) = L.size + x.size
  := by
  induction L generalizing excess with
  | base =>
    simp [consL] at h_L'
    rcases h_L' with ⟨rfl,rfl⟩
    simp
  | joint hd tl ih =>
    simp [consL] at h_L'
    if h : hd.width < WIDTH then
      simp_all
      rcases h_L' with ⟨rfl,rfl⟩
      simp [size]
      rw [← (HyperRect.size _).property]
      simp; ring
    else
      simp [validList] at h_L
      have hhd : hd.backing.size = WIDTH := by simp at h; linarith
      let new := hd.fullToHyperArray hhd
      simp_all
      split at h_L'
      generalize hblah : consL (hd.fullToHyperArray _) _ _ = blah at h_L'
      rcases blah with ⟨LLL,exc⟩
      have := ih new hblah
      simp at h_L'; rcases h_L' with ⟨rfl,rfl⟩
      cases exc <;> simp [size] at this ⊢
      · rw [this, hhd, Nat.pow_succ]; ring
      · rw [hhd, Nat.add_assoc, this, Nat.pow_succ]; ring

/- Pushes `x` onto `L` from the right at the top joint (small elements).
If `L` is full, returns the (full) bottom joint as a `HyperArray τ n`
and shifts everything else up to accommodate `x`.
-/
def consR (x : HyperArray τ m) : (L : FingerList τ n m) → L.validList →
    FingerList τ n m × Option (HyperArray τ n)
| base, _ => (base, some x)
| joint hd tl, h_L =>
    if h : hd.width < WIDTH then
      (joint (hd.cons x) tl, none)
    else
      have ⟨h_w, h_tl⟩ : hd.width ≤ WIDTH ∧ tl.validList := by
        simpa [validList] using h_L
      have h_w : hd.width = WIDTH := by
        apply Nat.le_antisymm
        exact h_w
        exact Nat.ge_of_not_lt h
      let newSlice : HyperArray τ (m + 1) :=
        hd.fullToHyperArray h_w
      match consR newSlice tl h_tl with
      | (fl, excess) =>
      (joint ⟨Array.singleton x, cached' (WIDTH ^ m) (by simp)⟩ fl, excess)

theorem valid_consR (x : HyperArray τ m) (L : FingerList τ n m) (h_R : L.validList)
  : let ⟨L',_⟩ := L.consR x h_R
    L'.validList
  := by
  induction L with
  | base =>
    simp [consR, h_R]
  | joint hd tl ih =>
    simp [consR]
    simp [validList] at h_R
    split
    case inl m' h =>
      simp [validList]
      simp [HyperRect.cons, h_R]
      exact h
    case inr m' h =>
      split
      case _ _ h_w h_tl _ =>
      simp [validList]
      constructor
      case left  => exact WIDTH_pos
      case right =>
      apply ih

theorem size_consR (x : HyperArray τ m) (L : FingerList τ n m) (h_L : L.validList)
  : let ⟨L', excess⟩ := L.consR x h_L
    L'.size + (match excess with
      | none => 0
      | some e => HyperArray.size e
    ) = L.size + x.size
  := by
  induction L with
  | base =>
    simp [size, consR]
  | joint hd tl ih =>
    clear m; rename Nat => m
    simp [validList] at h_L
    simp [h_L] at ih
    generalize hblah : consR _ _ _ = blah
    rcases blah with ⟨L', exc⟩
    simp
    unfold consR at hblah
    split at hblah
    · simp at hblah; rcases hblah with ⟨rfl,rfl⟩
      simp [size, Nat.add_mul]; ring
    split at hblah
    simp at hblah
    generalize hblahh : consR _ tl _ = blahh at hblah
    rcases blahh with ⟨LL, excess⟩
    simp at hblah; rcases hblah with ⟨rfl,rfl⟩
    generalize hx : hd.fullToHyperArray _ = x at hblahh
    have : HyperRect.width hd = WIDTH := @consR.proof_2 τ m hd ‹_› ‹_›
    have := ih x
    simp [hblahh] at this
    cases excess <;> simp_all [size, Nat.pow_succ]
    · ring
    · linarith

/- Pops a single element from the left at the top joint (small elements).
  If `L` is empty, returns none.
-/
def frontL? : FingerList τ n m → Option (HyperArray τ m × FingerList τ n m)
| base => none
| joint hd tl =>
  match hd.front? with
  | some (A, hd') => some (A, joint hd' tl)
  | none =>
  match tl.frontL? with
  | none => none
  | some (A, tl') =>
    match A.front with
    | (A', hd') =>
      some (A', joint (.ofArray hd'.data) tl')

theorem size_frontL?_none (L : FingerList τ n m)
  : frontL? L = none → size L = 0
  := by
    intro h
    induction L with
    | base => simp [size]
    | joint hd tl ih =>
      simp [frontL?] at h
      split at h
      simp [size]; contradiction
      case h_2 h_hd =>
      split at h
      case h_1 h_tl =>
        simp [size, ih h_tl]
        simp [HyperRect.front?] at h_hd
        sorry
      case h_2 h_tl =>
        contradiction


/- Pops a single element from the right at the top joint (small elements).
  If `L` is empty, returns none.
-/
def frontR? : FingerList τ n m → Option (FingerList τ n m × HyperArray τ m)
| base => none
| joint hd tl =>
  match hd.back? with
  | some (hd', A) => some (joint hd' tl, A)
  | none =>
  match tl.frontR? with
  | none => none
  | some (tl', A) =>
    match A.back with
    | (hd', A') =>
      some (joint (.ofArray hd'.data) tl', A')

def splitHyperArrayL : {m : Nat} → HyperArray τ m → FingerList τ n m → τ × FingerList τ n 0
| 0, x, L => (x, L)
| _m+1, A, L =>
  match A.front with
  | (hd, tl) =>
  let tl := joint
    ⟨tl.data, cached _⟩
    L
  splitHyperArrayL hd tl

def splitHyperArrayR : {m : Nat} → HyperArray τ m → FingerList τ n m → τ × FingerList τ n 0
| 0, x, L => (x, L)
| _m+1, A, L =>
  match A.back with
  | (tl, hd) =>
  let tl := joint
    ⟨tl.data, cached _⟩
    L
  splitHyperArrayR hd tl

end RBFT.FingerList

open RBFT

/-- Radix-balanced finger tree.

Cost bounds:
- cons/snoc/front?/back?: O(1) amortized, O(log n) worst case
- get/set: O(log n) worst case
- append: O(log n) worst case

-/
structure RBFT (τ : Type u) : Type u where
  depth : Nat
  pre : FingerList τ depth 0 -- "L" fingerlist
  mid : HyperRect τ depth
  suf : FingerList τ depth 0 -- "R" fingerlist
  mid_idx : Cached pre.size
  suf_idx : Cached (pre.size + mid.size)
  size : Cached (pre.size + mid.size + suf.size)
  h_pre : pre.validList
  h_mid : mid.width ≤ WIDTH
  h_suf : suf.validList

namespace RBFT

def empty : RBFT τ := {
  depth := 0
  pre := .base
  mid := .empty
  suf := .base
  mid_idx := cached' 0 (by simp [FingerList.size])
  suf_idx := cached' 0 (by simp [FingerList.size])
  size := cached' 0 (by simp [FingerList.size])
  h_pre := by simp [FingerList.validList]
  h_mid := by simp
  h_suf := by simp [FingerList.validList]
}

def get : (A : RBFT τ) → Fin A.size → τ
| ⟨_, pre, mid, suf, mid_idx, suf_idx, size, h_pre, h_mid, h_suf⟩, ⟨i,h_i⟩ =>
  if h : i < mid_idx then
    pre.getL h_pre i (by simp at h; assumption)
  else if h' : i < suf_idx then
    have h_i := by
      rw [Cached.cached_val] at h h' ⊢
      apply Nat.le_of_add_le_add_right
      rw [Nat.succ_add, Nat.sub_add_cancel (Nat.ge_of_not_lt h)]
      rw [Nat.add_comm] at h'
      assumption
    mid.get ⟨i - mid_idx, h_i⟩
  else
    have h := by
      simp_all
      apply Nat.sub_lt_left_of_lt_add h_i
      linarith
    suf.getR h_suf (size - (i+1)) h

def set : (A : RBFT τ) → Fin A.size → τ → RBFT τ
| A, ⟨i,h_i⟩, a =>
  if h : i < A.mid_idx then
    {A with
      pre := A.pre.setL A.h_pre i (by simp at h; assumption) a
      h_pre := by simp [FingerList.valid_setL_of_valid]
      mid_idx := cast (by rw [FingerList.size_setL]) A.mid_idx
      suf_idx := cast (by rw [FingerList.size_setL]) A.suf_idx
      h_suf := by sorry
      size := cast (by rw [FingerList.size_setL]) A.size
      }
  else if h' : i < A.suf_idx then
    have h_i := by
      rw [Cached.cached_val] at h h' ⊢
      simp at h h' ⊢
      apply Nat.sub_lt_left_of_lt_add h h'
    {A with
      mid := A.mid.set ⟨i - A.mid_idx, h_i⟩ a
      h_mid := sorry
      }
  else
    have h := by
      apply Nat.sub_lt_left_of_lt_add (Nat.ge_of_not_lt h')
      simp at h_i ⊢
      exact h_i
    {A with
      suf := A.suf.setR A.h_suf (i - A.suf_idx) h a
      h_suf := by simp [FingerList.valid_setR_of_valid]
      size := cast (by rw [FingerList.size_setR]) A.size
      }

def cons (x : τ) (A : RBFT τ) : RBFT τ :=
  -- Try putting x in the prefix finger
  match h_preCons : A.pre.consL x A.h_pre with
  | (pre, none) =>
    have h_pre := by
      have := FingerList.valid_consL x A.pre A.h_pre
      rw [h_preCons] at this
      exact this
    have size_pre : pre.size = A.pre.size + 1 := by
      have := A.pre.size_consL x
      sorry
    {A with
      pre := pre
      h_pre := h_pre
      mid_idx := cached' (A.mid_idx.val + 1) (by sorry)
      suf_idx := cached' (A.suf_idx.val + 1) (by sorry)
      size := cached' (A.size.val + 1) (by sorry)
    }
  | (pre, some excess) =>
    /- The finger was full! Now we have a new (full) slice
      to put somewhere -/
    if h : A.mid.width < WIDTH then
    -- We can put the slice here!
    { pre := pre
      mid := A.mid.cons excess
      suf := A.suf
      h_pre := by sorry
      h_mid := by sorry
      h_suf := A.h_suf
      mid_idx := cached' 1 (by sorry)
      suf_idx := cached' (A.suf_idx.val + 1) (by sorry)
      size := cached' (A.size.val + 1) (by sorry)
      }
    else
    have h : A.mid.width = WIDTH := by
      apply Nat.le_antisymm
      exact A.h_mid
      exact Nat.ge_of_not_lt h
    -- We need a new level!
    { depth := A.depth.succ,
      pre := pre.extend (.singleton excess)
      mid := .singleton (A.mid.fullToHyperArray h)
      suf := A.suf.extend .empty
      h_pre := by sorry
      h_mid := by simp [HyperRect.singleton]; exact WIDTH_pos
      h_suf := by sorry
      mid_idx := cached' (A.mid_idx.val + 1) (by sorry)
      suf_idx := cached' (A.mid_idx.val + 1) (by sorry)
      size := cached' (A.size.val + 1) (by sorry)
      }

def front? : RBFT τ → Option (τ × RBFT τ)
| ⟨depth, pre, mid, suf, mid_idx, suf_idx, size, h_pre, h_mid, h_suf⟩ =>
  if h : size.val = 0 then none else (
    match h_preFront : pre.frontL? with
    | some (x, pre') => some (x, {
      pre := pre', mid, suf,
      mid_idx := cached' (mid_idx - 1) (by sorry)
      suf_idx := cached' (suf_idx - 1) (by sorry)
      size := cached' (size - 1) (by sorry)
      h_pre := by sorry, h_mid, h_suf
      })
    | none =>
    match h_midFront : mid.front? with
    | some (slice, mid') =>
      match FingerList.splitHyperArrayL slice .base with
      | (x, pre') => some (x, {
        pre := pre',
        mid := mid',
        suf,
        mid_idx := cached' (mid_idx - 1) (by sorry)
        suf_idx := cached' (suf_idx - 1) (by sorry)
        size := cached' (size - 1) (by sorry)
        h_pre := by sorry
        h_mid := by sorry,
        h_suf
      })
    | none =>
    -- Time to yeet a level
    match h_depth : depth with
    | 0 => by
      simp at h_depth; cases h_depth
      simp at *
      cases pre.upperBound_zero_base
      cases suf.upperBound_zero_base
      sorry
    | depth+1 =>
    match suf.unextend (Nat.zero_le _) with
    | (x, suf') =>
    front? {
      depth,
      pre := pre.unextend (Nat.zero_le _) |>.snd,
      mid := x,
      suf := suf',
      mid_idx := cached' 0 (by sorry),
      suf_idx := cached' x.size (by sorry),
      size := cached' size (by sorry),
      h_pre := by sorry
      h_mid := by sorry
      h_suf := by sorry
    }
  )
termination_by _ r => r.depth

example : Nat := 0

#eval show IO Unit from timeit "woo" do
  let mut A : RBFT Nat := .empty
  for i in [0:1000000] do
    A := A.cons i
  IO.println A.depth
  for h:i in [0:1000000] do
  --  assert! (A.get ⟨i,sorry⟩ < 1000000)
