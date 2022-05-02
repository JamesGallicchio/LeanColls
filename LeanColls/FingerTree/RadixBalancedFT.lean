/-
Copyright (c) 2021 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.AuxLemmas
import LeanColls.Array
import LeanColls.IndexedOps

/-!
# Radix Balanced Finger Trees

Represents a sequence as an N-dimensional hypercube where all sides
are `WIDTH` wide. The highest dimension can be less wide than `WIDTH`,
and the first and last element of the highest dimension can be
incomplete.

However, all interior layers of the hypercube are completely full.
This allows for rapid index calculations, essentially a trie on the
indices.

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

@[inline]
def get : {n : Nat} → HyperArray α n → (i : Fin (WIDTH ^ n)) → α
| 0,   a, ⟨0,_⟩   => a
| n+1, A, ⟨i,h_i⟩ =>
  let q := i / WIDTH^n
  let r := i % WIDTH^n
  get (COWArray.get A ⟨q, by
    apply Nat.lt_of_mul_lt $ Nat.pos_pow_of_pos _ (by decide)
    rw [Nat.pow_succ, Nat.mul_comm] at h_i
    assumption⟩)
    ⟨r, Nat.mod_lt _ (Nat.pos_pow_of_pos _ (by decide))⟩

def get? (A : HyperArray α n) (i : Nat) : Option α :=
  if h : i < WIDTH ^ n then
    some $ A.get ⟨i,h⟩
  else
    none

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
  COWArray.get A ⟨q, by
    apply Nat.lt_of_mul_lt $ Nat.pos_pow_of_pos _ (by decide)
    assumption⟩
  |>.get ⟨r, Nat.mod_lt _ (Nat.pos_pow_of_pos _ $ by decide)⟩

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
| neRbft, ⟨i,h_i⟩ =>
  if h : i < neRbft.mid_idx then
    neRbft.pre.get neRbft.h_pre i (Nat.zero_le _) (by
      rw [Cached.cached_val] at h; assumption)
  else if h' : i < neRbft.suf_idx then
    neRbft.mid.get ⟨i - neRbft.mid_idx, by
      rw [Cached.cached_val] at h h' ⊢
      simp at h h'
      apply Nat.le_of_add_le_add_right
      rw [Nat.succ_add, Nat.sub_add_cancel (Nat.ge_of_not_lt h)]
      rw [Nat.add_comm] at h'
      assumption⟩
  else
    neRbft.suf.get neRbft.h_suf i (by
      apply Nat.ge_of_not_lt
      rw [Cached.cached_val] at h'
      assumption) (by
      rw [Cached.cached_val] at h_i
      assumption)

end RadixBalancedFT
