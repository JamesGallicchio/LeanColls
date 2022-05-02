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

namespace LeanColls

namespace RadixBalancedFT

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
        simp [h', set, get, COWArray.update, COWArray.get, COWArray.set,
          Array.copy]

end HyperArray

structure FingerArray (α : Type u) (n : Nat) : Type u where
  (w : Nat)
  (h_w : w < WIDTH)
  (backing : COWArray (HyperArray α n) w)

namespace FingerArray

@[simp]
def size : FingerArray α n → Nat
| ⟨w, _, _⟩ => w * WIDTH ^ n

theorem size_eq_sum_sizes (F : FingerArray α n)
  : Foldable.fold (λ x acc => x.size + acc) 0 F.backing = F.size
  := by
  match F with
  | ⟨w, _, ⟨backing⟩⟩ =>
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

def get : (A : FingerArray α n) → Fin A.size → α
| ⟨w,h_w,A⟩, ⟨i,h_i⟩ =>
  let q := i / WIDTH^n
  let r := i % WIDTH^n
  have h_q := by
    apply Nat.lt_of_mul_lt $ Nat.pos_pow_of_pos _ (by decide)
    assumption
  have h_r := Nat.mod_lt _ (Nat.pos_pow_of_pos _ $ by decide)
  COWArray.get A ⟨q, h_q⟩
  |>.get ⟨r, h_r⟩

def set : (A : FingerArray α n) → Fin A.size → α → FingerArray α n
| ⟨w,h_w,A⟩, ⟨i,h_i⟩, a =>
  let q := i / WIDTH^n
  let r := i % WIDTH^n
  have h_q := by
    apply Nat.lt_of_mul_lt $ Nat.pos_pow_of_pos _ (by decide)
    assumption
  have h_r := Nat.mod_lt _ (Nat.pos_pow_of_pos _ $ by decide)
  ⟨w, h_w,
    COWArray.update A ⟨q, h_q⟩
    <| λ A' => A'.set ⟨r, h_r⟩ a⟩

end FingerArray

inductive FingerList (τ : Type u) (n : Nat) : Nat → Type u
| single : FingerArray τ n → (endIdx : Nat) → FingerList τ n n
| cons : FingerArray τ m → (endIdx : Nat) → FingerList τ n m.succ
          → FingerList τ n m

namespace FingerList

def validList (startIdx : Nat) : FingerList τ n m → Prop
| single A idx => idx = startIdx + A.size
| cons hd tlIdx tl =>
  tlIdx = startIdx + hd.size ∧ validList tlIdx tl

def endIdx : FingerList τ n m → Nat
| single _ idx => idx
| cons _ _ tl => tl.endIdx

def get : (L : FingerList τ n m) → (h_L : L.validList startIdx)
          → (i : Nat) → (h_low : startIdx ≤ i) → (h_high : i < L.endIdx)
          → τ
| single A _, h_L, i, h_low, h_high =>
  A.get ⟨i - startIdx, by
    simp [validList] at h_L
    cases h_L; case refl =>
    simp [endIdx] at h_high
    simp
    apply Nat.le_of_add_le_add_right (b := startIdx)
    rw [Nat.succ_add, Nat.sub_add_cancel h_low]
    rw [Nat.add_comm] at h_high
    assumption
  ⟩
| cons hd tlIdx tl, h_L, i, h_low, h_high =>
  if h : i < tlIdx then
    hd.get ⟨i - startIdx, by
    simp [validList] at h_L
    cases h_L with
    | intro h_tlIdx h_L =>
    cases h_tlIdx; case refl =>
    simp
    apply Nat.le_of_add_le_add_right (b := startIdx)
    rw [Nat.succ_add, Nat.sub_add_cancel h_low]
    rw [Nat.add_comm] at h
    assumption
    ⟩
  else
    get tl h_L.right i (Nat.ge_of_not_lt h) h_high

def set : (L : FingerList τ n m) → (h_L : L.validList startIdx)
          → (i : Nat) → (h_low : startIdx ≤ i) → (h_high : i < L.endIdx)
          → τ → FingerList τ n m 
| single A endIdx, h_L, i, h_low, h_high, a =>
  have h_i := by
    simp [validList] at h_L
    cases h_L; case refl =>
    simp [endIdx] at h_high
    simp
    apply Nat.le_of_add_le_add_right (b := startIdx)
    rw [Nat.succ_add, Nat.sub_add_cancel h_low]
    rw [Nat.add_comm] at h_high
    assumption
  single (A.set ⟨i - startIdx, h_i⟩ a) endIdx
| cons hd tlIdx tl, h_L, i, h_low, h_high, a =>
  if h : i < tlIdx then
    have h_i := by
      simp [validList] at h_L
      cases h_L with
      | intro h_tlIdx h_L =>
      cases h_tlIdx; case refl =>
      simp
      apply Nat.le_of_add_le_add_right (b := startIdx)
      rw [Nat.succ_add, Nat.sub_add_cancel h_low]
      rw [Nat.add_comm] at h
      assumption
    cons (hd.set ⟨i - startIdx, h_i⟩ a) tlIdx tl
  else
    cons hd tlIdx (set tl h_L.right i (Nat.ge_of_not_lt h) h_high a)

theorem valid_set_of_valid (L : FingerList τ n m) (h_L : L.validList startIdx)
          (i : Nat) (h_low : startIdx ≤ i) (h_high : i < L.endIdx) (x : τ)
  : validList startIdx (set L h_L i h_low h_high x)
  := by
  induction L generalizing startIdx with
  | single a endIdx =>
    simp [validList, FingerArray.set] at h_L ⊢
    assumption
  | cons hd tlIdx tl ih =>
    simp [set]
    split <;> (
      simp [validList, FingerArray.set] at h_L ⊢
      simp [h_L] at h_L ⊢
      simp [h_L, ih]
    )

theorem endIdx_set (L : FingerList τ n m) (h_L : L.validList startIdx)
          (i : Nat) (h_low : startIdx ≤ i) (h_high : i < L.endIdx) (x : τ)
  : endIdx (set L h_L i h_low h_high x) = endIdx L
  := by
  induction L generalizing startIdx with
  | single a ei =>
    simp [endIdx]
  | cons hd tlIdx tl ih =>
    simp [set]
    split <;>
      simp [endIdx, ih]

end FingerList

end RadixBalancedFT

open RadixBalancedFT

structure RadixBalancedFT (τ : Type u) : Type u where
  depth : Nat
  pre : FingerList τ depth 0
  h_pre : pre.validList 0
  mid_idx : Cached pre.endIdx
  mid : HyperArray τ depth
  suf_idx : Cached (pre.endIdx + mid.size)
  suf : FingerList τ depth 0
  h_suf : suf.validList (pre.endIdx + mid.size)
  size : Cached suf.endIdx

namespace RadixBalancedFT

abbrev RBFT := RadixBalancedFT

def get : (A : RBFT τ) → Fin A.size → τ
| ⟨_, pre, h_pre, mid_idx, mid, suf_idx, suf, h_suf, _⟩, ⟨i,h_i⟩ =>
  if h : i < mid_idx then
    have h_low := Nat.zero_le _
    have h_high := by
      rw [Cached.cached_val] at h; assumption
    pre.get h_pre i h_low h_high
  else if h' : i < suf_idx then
    have h_i := by
      rw [Cached.cached_val] at h h' ⊢
      simp at h h'
      apply Nat.le_of_add_le_add_right
      rw [Nat.succ_add, Nat.sub_add_cancel (Nat.ge_of_not_lt h)]
      rw [Nat.add_comm] at h'
      assumption
    mid.get ⟨i - mid_idx, h_i⟩
  else
    have h_low := by
      apply Nat.ge_of_not_lt
      rw [Cached.cached_val] at h'
      assumption
    have h_high := by
      rw [Cached.cached_val] at h_i
      assumption
    suf.get h_suf i h_low h_high

def set : (A : RBFT τ) → Fin A.size → τ → RBFT τ
| A, ⟨i,h_i⟩, a =>
  if h : i < A.mid_idx then
    have h_low := Nat.zero_le _
    have h_high := by
      rw [Cached.cached_val] at h; assumption
    {A with
      pre := A.pre.set A.h_pre i h_low h_high a
      h_pre := by simp [FingerList.valid_set_of_valid]
      mid_idx := cast (by rw [FingerList.endIdx_set]) A.mid_idx
      suf_idx := cast (by rw [FingerList.endIdx_set]) A.suf_idx
      h_suf := by simp [FingerList.valid_set_of_valid, FingerList.endIdx_set]; exact A.h_suf
      }
  else if h' : i < A.suf_idx then
    have h_i := by
      rw [Cached.cached_val] at h h' ⊢
      simp at h h'
      apply Nat.le_of_add_le_add_right
      rw [Nat.succ_add, Nat.sub_add_cancel (Nat.ge_of_not_lt h)]
      rw [Nat.add_comm] at h'
      assumption
    {A with
      mid := A.mid.set ⟨i - A.mid_idx, h_i⟩ a
      }
  else
    have h_low := by
      apply Nat.ge_of_not_lt
      rw [Cached.cached_val] at h'
      assumption
    have h_high := by
      rw [Cached.cached_val] at h_i
      assumption
    {A with
      suf := A.suf.set A.h_suf i h_low h_high a
      h_suf := by simp [FingerList.valid_set_of_valid]
      size := cast (by rw [FingerList.endIdx_set]) A.size
      }

end RadixBalancedFT
