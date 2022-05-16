/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.AuxLemmas
import LeanColls.Array
import LeanColls.IndexedOps

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

namespace LeanColls.RadixBalancedFT

@[inline] def WIDTH := 32

/- A hypercube array thing with `n` dimensions, each
  `WIDTH` wide, e.g. a total capacity of `WIDTH ^ n`
-/
def HyperArray (α : Type u) : Nat → Type u
| 0   => α
| n+1 => COWArray (HyperArray α n) WIDTH

namespace HyperArray

@[inline, simp]
def size (_ : HyperArray α n) : Nat := WIDTH ^ n

def get : {n : Nat} → HyperArray α n → (i : Fin (WIDTH ^ n)) → α
| 0,   a, ⟨0,_⟩   => a
| n+1, A, ⟨i,h_i⟩ =>
  let q := i / WIDTH^n
  let r := i % WIDTH^n
  have h_q : q < WIDTH := by
    apply Nat.lt_of_mul_lt $ Nat.pos_pow_of_pos _ (by decide)
    rw [Nat.pow_succ, Nat.mul_comm] at h_i
    assumption
  have h_r : r < WIDTH^n :=
    Nat.mod_lt _ (Nat.pos_pow_of_pos _ (by decide))
  COWArray.get A ⟨q, h_q⟩
  |>.get ⟨r, h_r⟩

def set : {n : Nat} → HyperArray α n → (i : Fin (WIDTH ^ n)) → α → HyperArray α n
| 0,   _, ⟨0,_⟩  , a => a
| n+1, A, ⟨i,h_i⟩, a =>
  let q := i / WIDTH^n
  let r := i % WIDTH^n
  have h_q : q < WIDTH := by
    apply Nat.lt_of_mul_lt $ Nat.pos_pow_of_pos _ (by decide)
    rw [Nat.pow_succ, Nat.mul_comm] at h_i
    assumption
  have h_r : r < WIDTH^n :=
    Nat.mod_lt _ (Nat.pos_pow_of_pos _ (by decide))
  COWArray.update A ⟨q, h_q⟩
  <| λ A' => set A' ⟨r, h_r⟩ a

theorem get_of_set (A : HyperArray α n) (i j : Fin (WIDTH ^ n)) (x : α)
  : (A.set i x |>.get j) = if i = j then x else A.get j
  := by
  induction n with
  | zero =>
    simp [HyperArray, Nat.pow_zero] at A i j
    cases i; case mk i h_i =>
    cases j; case mk j h_j =>
    have : i = 0 := Nat.eq_zero_of_le_zero <| Nat.le_of_succ_le_succ h_i
    cases this
    have : j = 0 := Nat.eq_zero_of_le_zero <| Nat.le_of_succ_le_succ h_j
    cases this
    simp [set, get]
  | succ n ih =>
    simp [HyperArray, Nat.pow_zero] at A i j
    cases i; case mk i h_i =>
    cases j; case mk j h_j =>
    by_cases i = j
    case inl h =>
      simp [h, set, get, COWArray.update, COWArray.get, COWArray.set, ih]
    case inr h =>
      simp [h]
      by_cases i / WIDTH ^ n = j / WIDTH ^ n
      case inl h' =>
        simp [h', set, get, COWArray.update, COWArray.get, COWArray.set, ih]
        have : i % WIDTH ^ n ≠ j % WIDTH ^ n := by
          clear A x ih
          rw [←Nat.div_add_mod i (WIDTH ^ n), ←Nat.div_add_mod j (WIDTH ^ n)] at h
          rw [h'] at h
          clear h'
          exact h ∘ (congrArg _)
        simp [this]
      case inr h' =>
        simp [h', set, get, COWArray.update, COWArray.get, COWArray.set]
        simp [Array.copy, Array.init_eq_mk, Array.get, Array.set]

def repr [R : Repr α] : {n : Nat} → Repr (HyperArray α n)
| 0 => R
| n+1 => @COWArray.instReprCOWArray _ _ (repr)

instance [Repr α] : Repr (HyperArray α n) := repr

end HyperArray

structure HyperRect (α : Type u) (n : Nat) : Type u where
  (w : Nat)
  (backing : COWArray (HyperArray α n) w)
  (size : Cached (w * WIDTH ^ n))
deriving Repr

namespace HyperRect

def ofArray {w} (backing : COWArray (HyperArray α n) w) : HyperRect α n :=
  ⟨w, backing, cached _⟩

def empty : HyperRect α n := ofArray (COWArray.empty)

def singleton (A : HyperArray α n) : HyperRect α n :=
  ⟨1, COWArray.singleton A, cached _⟩

def fullToHyperArray : (r : HyperRect α n) → r.w = WIDTH → HyperArray α n.succ
| ⟨_, backing, _⟩, h =>
  backing |> cast (by simp at h; simp [HyperArray, h])

theorem size_eq_sum_sizes (F : HyperRect α n)
  : Foldable.fold (λ x acc => x.size + acc) 0 F.backing = F.size
  := by
  match F with
  | ⟨w, ⟨backing⟩, _⟩ =>
  simp
  unfold Foldable.fold
  simp [COWArray.instFoldableCOWArray]
  unfold Foldable.fold
  simp [instFoldable]
  simp [Indexed.size, Indexed.nth]
  apply Range.fold_ind (motive := λ w res => res = w * WIDTH ^ n)
  case init => simp
  case step =>
  intro i acc h_i h_acc
  simp [h_acc, Nat.succ_mul, Nat.add_comm]

def get : (A : HyperRect α n) → Fin A.size → α
| ⟨w,A,_⟩, ⟨i,h_i⟩ =>
  let q := i / WIDTH^n
  let r := i % WIDTH^n
  have h_q := by
    simp at h_i
    apply Nat.lt_of_mul_lt $ Nat.pos_pow_of_pos _ (by decide)
    assumption
  have h_r := Nat.mod_lt _ (Nat.pos_pow_of_pos _ $ by decide)
  COWArray.get A ⟨q, h_q⟩
  |>.get ⟨r, h_r⟩

def set : (A : HyperRect α n) → Fin A.size → α → HyperRect α n
| ⟨w,A,size⟩, ⟨i,h_i⟩, a =>
  let q := i / WIDTH^n
  let r := i % WIDTH^n
  have h_q := by
    simp at h_i
    apply Nat.lt_of_mul_lt $ Nat.pos_pow_of_pos _ (by decide)
    assumption
  have h_r := Nat.mod_lt _ (Nat.pos_pow_of_pos _ $ by decide)
  ⟨w,
    COWArray.update A ⟨q, h_q⟩ <| λ A' => A'.set ⟨r, h_r⟩ a,
    size⟩

def cons : HyperArray α n → HyperRect α n → HyperRect α n
| x, ⟨w,A,size⟩ =>
  ⟨w.succ, A.cons x,
    cached' (size.val + WIDTH ^ n) (by simp [Nat.succ_mul])⟩

def snoc : HyperRect α n → HyperArray α n → HyperRect α n
| ⟨w,A,size⟩, x =>
  ⟨w.succ, A.snoc x,
    cached' (size.val + WIDTH ^ n) (by simp [Nat.succ_mul])⟩

def front? : HyperRect α n → Option (HyperArray α n × HyperRect α n)
| ⟨0,_,_⟩ => none
| ⟨w+1, A, size⟩ =>
  match A.front with
  | (x, A') =>
  some (x, ⟨w, A',
      cached' (size.val - WIDTH ^ n) (by
        simp [Nat.succ_mul, Nat.add_sub_cancel])⟩
  )

theorem size_front?_none : (r : HyperRect τ n) → front? r = none → r.size.val = 0
| ⟨w, A, _⟩, h => by
  simp [front?] at *
  split at h
  case h_1 h_r =>
    simp at h_r
    simp [h_r.left]
  case h_2 =>
    contradiction

def back? : HyperRect α n → Option (HyperRect α n × HyperArray α n)
| ⟨0,_,_⟩ => none
| ⟨w+1, A, size⟩ =>
  match A.back with
  | (A', x) =>
  some (
    ⟨w, A',
      cached' (size.val - WIDTH ^ n) (by
        simp [Nat.succ_mul, Nat.add_sub_cancel])⟩,
    x
  )

end HyperRect

/-!
## FingerList

A linked-list-like representation of the prefix/suffix fingers.
A `FingerList τ n m` is a list of `HyperRect τ i`s for `m ≤ i < n`.
-/
inductive FingerList (τ : Type u) (n : Nat) : Nat → Type u
| base  : FingerList τ n n
| joint : (hd : HyperRect τ m) → (tl : FingerList τ n m.succ)
          → FingerList τ n m
deriving Repr

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
  hd.w ≤ WIDTH && validList tl

def isFull : FingerList τ n m → Bool
| base => true
| joint hd tl =>
  hd.w = WIDTH && isFull tl

def extend : FingerList τ n m → FingerList τ n.succ m
| base => joint (HyperRect.empty) base
| joint hd tl => joint hd (extend tl)

def unextend : {n m : Nat} → m ≤ n → FingerList τ n.succ m → HyperRect τ n × FingerList τ n m
| _, _, h, base => False.elim (Nat.ne_of_lt h rfl)
| _, _, h, joint hd base => (hd, base)
| n, m, h, joint hd (joint hd' tl') =>
  have : m.succ ≤ n := Nat.le_of_succ_le_succ (upperBound tl')
  let (x, tl) := unextend this (joint hd' tl')
  (x, joint hd tl)

/-!
getL
Indexes into L from the left; e.g. 0 is the top-left
element, and `L.size - 1` is the bottom right's last element.
-/
def getL : (L : FingerList τ n m) → (h_L : L.validList)
          → (i : Nat) → (h_i : i < L.size)
          → τ
| base, _, _, h_i =>
  False.elim <| by
    simp [size] at h_i
    exact Nat.not_lt_zero _ h_i
| joint hd tl, h_L, i, h_i =>
  if h : i < hd.size then
    hd.get ⟨i, h⟩
  else
    getL tl
      (by simp [validList] at h_L; exact h_L.right)
      (i - hd.size)
      (by
        simp [size] at h_i ⊢
        apply Nat.sub_lt_of_lt_add
        rw [Nat.add_comm]
        simp [h_i]
        simp at h
        exact Nat.ge_of_not_lt h)

/-! See `getL` -/
def setL : (L : FingerList τ n m) → (h_L : L.validList)
          → (i : Nat) → (h_i : i < L.size)
          → τ → FingerList τ n m 
| base, _, _, h_i, a =>
  False.elim <| by
    simp [size] at h_i
    exact Nat.not_lt_zero _ h_i
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
          simp [size] at h_i ⊢
          apply Nat.sub_lt_of_lt_add
          rw [Nat.add_comm]
          simp [h_i]
          simp at h
          exact Nat.ge_of_not_lt h)
        a

theorem valid_setL_of_valid (L : FingerList τ n m) (h_L : L.validList)
          (i : Nat) (h_i : i < L.size) (x : τ)
  : validList (setL L h_L i h_i x)
  := by
  induction L generalizing i with
  | base =>
    apply False.elim
    simp [size] at h_i
    exact Nat.not_lt_zero _ h_i
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
    apply False.elim
    simp [size] at h_i
    exact Nat.not_lt_zero _ h_i
  | joint hd tl ih =>
    simp [setL]
    split <;> (
      simp [set, HyperRect.set] at h_L ⊢
      simp [size, ih]
    )

/-! getR
Indexes into `L` from the right, e.g. 0 is the top-right
element and `L.size-1` is the bottom-left's first element.
-/
def getR : (L : FingerList τ n m) → (h_L : L.validList)
          → (i : Nat) → (h_i : i < L.size)
          → τ
| base, _, _, h_i =>
  False.elim <| by
    simp [size] at h_i
    exact Nat.not_lt_zero _ h_i
| joint hd tl, h_L, i, h_i =>
  if h : i < hd.size then
    hd.get ⟨hd.size - i.succ,
      Nat.sub_lt_of_lt_add (Nat.add_lt_add_left (Nat.zero_lt_succ _) _) h⟩
  else
    getR tl
      (by simp [validList] at h_L; exact h_L.right)
      (i - hd.size)
      (by
        simp [size] at h_i ⊢
        apply Nat.sub_lt_of_lt_add
        rw [Nat.add_comm]
        simp [h_i]
        simp at h
        exact Nat.ge_of_not_lt h)

/-! See `getR` -/
def setR : (L : FingerList τ n m) → (h_L : L.validList)
          → (i : Nat) → (h_i : i < L.size)
          → τ → FingerList τ n m 
| base, _, _, h_i, a =>
  False.elim <| by
    simp [size] at h_i
    exact Nat.not_lt_zero _ h_i
| joint hd tl, h_L, i, h_i, a =>
  if h : i < hd.size then
    let hd' := hd.set ⟨hd.size - i.succ,
      Nat.sub_lt_of_lt_add (Nat.add_lt_add_left (Nat.zero_lt_succ _) _) h⟩
      a
    joint hd' tl
  else
    joint hd <|
      setR tl (by
        simp [validList] at h_L
        exact h_L.right)
        (i - hd.size)
        (by
          simp [size] at h_i ⊢
          apply Nat.sub_lt_of_lt_add
          rw [Nat.add_comm]
          simp [h_i]
          simp at h
          exact Nat.ge_of_not_lt h)
        a

theorem valid_setR_of_valid (L : FingerList τ n m) (h_L : L.validList)
          (i : Nat) (h_i : i < L.size) (x : τ)
  : validList (setR L h_L i h_i x)
  := by
  induction L generalizing i with
  | base =>
    apply False.elim
    simp [size] at h_i
    exact Nat.not_lt_zero _ h_i
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
    apply False.elim
    simp [size] at h_i
    exact Nat.not_lt_zero _ h_i
  | joint hd tl ih =>
    simp [setR]
    split <;> (
      simp [set, HyperRect.set] at h_L ⊢
      simp [size, ih]
    )


/- Pushes `x` onto `L` from the left at the top joint (small element).
If `L` is full, returns the (full) bottom joint as a `HyperArray τ n`
and shifts everything else up to accommodate `x`.
-/
def consL (x : HyperArray τ m) : (L : FingerList τ n m) → L.validList →
    FingerList τ n m × Option (HyperArray τ n)
| base, _ => (base, some x)
| joint hd tl, h_L =>
    if h : hd.w < WIDTH then
      (joint (hd.cons x) tl, none)
    else
      have ⟨h_w, h_tl⟩ : hd.w ≤ WIDTH ∧ tl.validList := by
        simp [validList] at h_L
        simp at h_L
        simp [h_L]
      have h_w : hd.w = WIDTH := by
        apply Nat.le_antisymm
        exact h_w
        exact Nat.ge_of_not_lt h
      let newSlice : HyperArray τ (m + 1) :=
        hd.backing
        |> cast (by simp [h_w, HyperArray, WIDTH])
      match consL newSlice tl h_tl with
      | (fl, excess) =>
      (joint ⟨0, COWArray.empty, cached' 0 (by simp)⟩ fl, excess)

/- Pushes `x` onto `L` from the right at the top joint (small elements).
If `L` is full, returns the (full) bottom joint as a `HyperArray τ n`
and shifts everything else up to accommodate `x`.
-/
def consR (x : HyperArray τ m) : (L : FingerList τ n m) → L.validList →
    FingerList τ n m × Option (HyperArray τ n)
| base, _ => (base, some x)
| joint hd tl, h_L =>
    if h : hd.w < WIDTH then
      (joint (hd.cons x) tl, none)
    else
      have ⟨h_w, h_tl⟩ : hd.w ≤ WIDTH ∧ tl.validList := by
        simp [validList] at h_L
        simp at h_L
        simp [h_L]
      have h_w : hd.w = WIDTH := by
        apply Nat.le_antisymm
        exact h_w
        exact Nat.ge_of_not_lt h
      let newSlice : HyperArray τ (m + 1) :=
        hd.backing
        |> cast (by simp [h_w, HyperArray, WIDTH])
      match consR newSlice tl h_tl with
      | (fl, excess) =>
      (joint ⟨0, COWArray.empty, cached' 0 (by simp)⟩ fl, excess)

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
      some (A', joint (.ofArray hd') tl')

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
        split at h_hd <;> simp
        contradiction
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
      some (joint (.ofArray hd') tl', A')

def splitHyperArrayL : {m : Nat} → HyperArray τ m → FingerList τ n m → τ × FingerList τ n 0
| 0, x, L => (x, L)
| m+1, A, L =>
  match A.front with
  | (hd, tl) =>
  let tl := joint
    ⟨WIDTH-1, tl, cached _⟩
    L
  splitHyperArrayL hd tl

def splitHyperArrayR : {m : Nat} → HyperArray τ m → FingerList τ n m → τ × FingerList τ n 0
| 0, x, L => (x, L)
| m+1, A, L =>
  match A.back with
  | (tl, hd) =>
  let tl := joint
    ⟨WIDTH-1, tl, cached _⟩
    L
  splitHyperArrayR hd tl

end RadixBalancedFT.FingerList

open RadixBalancedFT

structure RadixBalancedFT (τ : Type u) : Type u where
  depth : Nat
  pre : FingerList τ depth 0 -- "L" fingerlist
  mid : HyperRect τ depth
  suf : FingerList τ depth 0 -- "R" fingerlist
  mid_idx : Cached pre.size
  suf_idx : Cached (pre.size + mid.size)
  size : Cached (pre.size + mid.size + suf.size)
  h_pre : pre.validList
  h_mid : mid.w ≤ WIDTH
  h_suf : suf.validList
deriving Repr

namespace RadixBalancedFT

abbrev RBFT := RadixBalancedFT

def empty : RBFT τ := {
  depth := 0
  pre := .base
  mid := ⟨0, COWArray.empty, cached' 0 (by simp)⟩
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
      apply Nat.sub_lt_of_lt_add
      rw [←Nat.add_assoc, Nat.add_one]
      apply Nat.succ_le_succ
      have h := Nat.ge_of_not_lt h'
      simp at h ⊢
      rw [Nat.add_comm]
      apply Nat.add_le_add
      apply Nat.le_refl
      assumption
      simp at h_i ⊢
      assumption
    suf.getR h_suf (size - (i+1)) h

def set : (A : RBFT τ) → Fin A.size → τ → RBFT τ
| A, ⟨i,h_i⟩, a =>
  if h : i < A.mid_idx then
    {A with
      pre := A.pre.setL A.h_pre i (by simp at h; assumption) a
      h_pre := by simp [FingerList.valid_setL_of_valid]
      mid_idx := cast (by rw [FingerList.size_setL]) A.mid_idx
      suf_idx := cast (by rw [FingerList.size_setL]) A.suf_idx
      h_suf := by simp [FingerList.valid_setL_of_valid, FingerList.size_setL]; exact A.h_suf
      size := cast (by rw [FingerList.size_setL]) A.size
      }
  else if h' : i < A.suf_idx then
    have h_i := by
      rw [Cached.cached_val] at h h' ⊢
      simp at h h' ⊢
      apply Nat.sub_lt_of_lt_add
      rw [Nat.add_comm]
      assumption
      exact Nat.ge_of_not_lt h
    {A with
      mid := A.mid.set ⟨i - A.mid_idx, h_i⟩ a
      }
  else
    have h := by
      apply Nat.sub_lt_of_lt_add _ (Nat.ge_of_not_lt h')
      simp at h_i ⊢
      rw [Nat.add_comm]
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
    {A with
      pre := pre
      h_pre := by sorry
      mid_idx := cached' (A.mid_idx.val + 1) (by sorry)
      suf_idx := cached' (A.suf_idx.val + 1) (by sorry)
      size := cached' (A.size.val + 1) (by sorry)
    }
  | (pre, some excess) =>
    /- The finger was full! Now we have a new (full) slice
      to put somewhere -/
    if h : A.mid.w < WIDTH then
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
    have h : A.mid.w = 32 := by
      apply Nat.le_antisymm
      exact A.h_mid
      exact Nat.ge_of_not_lt h
    -- We need a new level!
    { depth := A.depth.succ,
      pre := pre.extend
      mid := .singleton (A.mid.fullToHyperArray h)
      suf := A.suf.extend
      h_pre := by sorry
      h_mid := by simp [HyperRect.singleton]
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
      have := HyperRect.size_front?_none _ h_midFront
      simp at this
      simp [FingerList.size] at h
      contradiction
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
