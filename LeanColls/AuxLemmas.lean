/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Init.Data.Int.Basic
import Mathlib.Order.Basic
import Mathlib.Data.UInt
import Mathlib.Data.Nat.Sqrt

namespace Nat
  @[deprecated sub_add_eq]
  theorem sub_dist (x y z : Nat) : x - (y + z) = x - y - z :=
    sub_add_eq x y z

  @[deprecated Nat.sub_lt_right_of_lt_add]
  theorem sub_lt_of_lt_add {x y z : Nat}
    : x < y + z → x ≥ z → x - z < y
    := fun a a_1 => Nat.sub_lt_right_of_lt_add a_1 a

  theorem add_mul_div {x y z : Nat} (h_x : 0 < x)
    : (x * y + z) / x = y + z / x
    := by
    rw [Nat.add_div_of_dvd_right, Nat.mul_comm] <;> simp
    apply Nat.mul_div_cancel _ h_x

  theorem mul_div_with_rem_cancel (x : Nat) {q r : Nat} (h_r : r < q)
    : (x * q + r) / q = x
    := by
    induction x with
    | zero =>
      rw [div_eq]
      have : 0 < q := zero_lt_of_lt h_r
      simp [this, Nat.not_le_of_gt h_r]
    | succ x ih =>
      rw [div_eq]
      simp [zero_lt_of_lt h_r]
      have : q ≤ (x + 1) * q + r := by
        simp [succ_mul]
        rw [Nat.add_comm _ q, Nat.add_assoc]
        apply Nat.le_add_right
      simp [this]
      rw [succ_mul, Nat.add_assoc, Nat.add_comm q,
          ←Nat.add_assoc, Nat.add_sub_cancel]
      assumption
  
  @[deprecated mul_div_le]
  theorem le_of_mul_of_div { x y : Nat }
    : x * (y / x) ≤ y
    := mul_div_le y x

  @[deprecated Nat.lt_of_lt_of_le]
  theorem lt_of_lt_le {x y z : Nat} : x < y → y ≤ z → x < z :=
    fun a a_1 => Nat.lt_of_lt_of_le a a_1

  @[deprecated min_comm]
  theorem min_symm (x y : Nat) : min x y = min y x :=
    Nat.min_comm x y

  @[deprecated zero_min]
  theorem min_zero_left {x} : min 0 x = 0 := Nat.zero_min x

  @[deprecated min_zero]
  theorem min_zero_right {x} : min x 0 = 0 := Nat.min_zero x

  def toUSize! (n : Nat) : USize :=
    if n < USize.size then
      n.toUSize
    else
      panic! s!"Integer {n} is to larget for usize"

  theorem mod_lt_of_lt {x y z : Nat}
    : x < y → z > 0 → x % z < y
    := by
    intro h h_z
    match h_y : decide (y ≤ z) with
    | true =>
      have := of_decide_eq_true h_y
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h this)]
      assumption
    | false =>
      have := of_decide_eq_false h_y
      apply Nat.lt_trans _ (Nat.gt_of_not_le this)
      apply Nat.mod_lt
      assumption

  @[inline, reducible]
  def square (n : Nat) := n * n

  @[deprecated sqrt_le]
  theorem square_sqrt_le (n) : square (sqrt n) ≤ n := sqrt_le n

  @[deprecated lt_succ_sqrt]
  theorem square_succ_sqrt_gt (n) : n < square ((sqrt n)+1) := lt_succ_sqrt n

end Nat

namespace Fin

@[simp]
def embed_add_right : Fin n → Fin (n+m)
| ⟨i, h⟩ => ⟨i, Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)⟩

@[simp]
def embed_add_left : Fin n → Fin (m+n)
| ⟨i, h⟩ => ⟨i, Nat.lt_of_lt_of_le h (Nat.le_add_left _ _)⟩

@[simp]
def embed_succ : Fin n → Fin n.succ
| ⟨i, h⟩ => ⟨i, Nat.lt_of_lt_of_le h (Nat.le_step $ Nat.le_refl _)⟩

end Fin

namespace Int

theorem ofNat_natAbs_eq_neg_of_nonpos (a : Int) (h : a ≤ 0)
  : ofNat (natAbs a) = -a
  := by
  rw [←Int.natAbs_neg]
  apply Int.ofNat_natAbs_eq_of_nonneg
  apply Int.neg_le_neg h

end Int

namespace USize

theorem usize_bounded : USize.size ≤ UInt64.size := by
  cases usize_size_eq <;> (
    rw [(by assumption : USize.size = _)]
    decide
  )

end USize

namespace List
  def front? : List τ → Option (τ × List τ)
  | [] => none
  | t::ts => some (t,ts)

  @[simp]
  theorem front_cons (ts : List τ)
    : (ts.cons t).front? = some (t,ts)
    := by
    cases ts
    repeat {simp [front?]}

  def back? : List τ → Option (List τ × τ)
  | [] => none
  | t::ts => some (match ts.back? with | none => ([],t) | some (ts',t') => (t::ts',t'))

  @[simp]
  theorem back_concat (ts : List τ)
    : (ts.concat t).back? = some (ts,t)
    := by
    induction ts
    simp [back?]
    case cons t' ts' ih =>
    simp at ih ⊢
    simp [back?, ih]

  theorem concat_nonempty (L : List τ)
    : L.concat x ≠ []
    := by
    induction L
    simp [concat]
    simp [concat]

  theorem back_some_iff_concat (L : List τ)
    : L.back? = some (ts,t) ↔ L = ts.concat t
    := by
    apply Iff.intro
    case mpr =>
      intro h; rw [h, back_concat]
    case mp =>
    induction ts generalizing L
    case nil =>
      simp [concat]
      intro h
      match L with
      | [] => contradiction
      | [t] => simp [back?] at h; simp [h]
      | _::_::_ => simp [back?] at h
    case cons head tail ih =>
      simp [concat]
      intro h
      match L with
      | [] => contradiction
      | [x] => simp [back?] at h
      | x::y::z =>
        have ihh : back? (y::z) = some (tail, t) := by
          simp [back?] at h
          cases h; case intro l r =>
          simp [back?]
          match h:back? z with
          | none =>
            simp [h] at l r
            simp [l,r]
          | some (ts',t') =>
            simp [h] at l r ⊢
            simp [l,r]
        have := ih _ ihh
        rw [this]; simp; clear this
        unfold back? at h
        simp [ihh] at h
        assumption

  @[simp]
  theorem get_of_set_eq (L : List τ) (i : Fin L.length) (x : τ)
    : (L.set i x).get ⟨i, by rw [length_set]; exact i.isLt⟩ = x
    := by
      induction L
      simp at i; exact Fin.elim0 i
      case cons hd tl ih =>
      cases i; case mk i h_i =>
      cases i
      simp [set,get]
      case succ i =>
      simp at h_i
      have h_i := Nat.lt_of_succ_lt_succ h_i
      have := ih ⟨i,h_i⟩
      simp at this
      simp [set,get]
  
  @[simp]
  theorem get_of_set_ne (L : List τ) (i : Nat) (x : τ) (j : Fin L.length)
    : i ≠ j → (L.set i x).get ⟨j, by rw [length_set]; exact j.isLt⟩ = L.get j
    := by
      intro h
      induction L generalizing i
      simp at j; exact Fin.elim0 j
      case cons hd tl ih =>
      cases j; case mk j h_j =>
      cases j
      simp at h
      cases i; contradiction
      simp [set,get]
      case succ j =>
      simp at h_j
      simp
      cases i
      simp [set,get]
      case succ i =>
      simp [set,get]
      simp at h
      have h_j := Nat.lt_of_succ_lt_succ h_j
      have := ih i ⟨j,h_j⟩ h
      exact this
  
  theorem set_of_ge_length (L : List α) (i x) (h : ¬i < L.length)
    : L.set i x = L
    := by
    induction L generalizing i
    simp
    case cons hd tl ih =>
    cases i
    simp at h
    simp at h
    simp
    apply ih
    apply Nat.not_lt_of_le
    apply Nat.le_of_succ_le_succ h
  
  theorem set_append_left (L1 L2 : List α) (i x) (h : i < L1.length)
    : (L1 ++ L2).set i x = L1.set i x ++ L2
    := by
    induction L1 generalizing i with
    | nil => simp at h
    | cons hd tl ih =>
    match i with
    | 0 =>
      simp at h
      simp [set]
    | i+1 =>
      simp at h
      simp [set]
      apply ih
      apply Nat.le_of_succ_le_succ h

  theorem set_append_right (L1 L2 : List α) (i x) (h : L1.length ≤ i)
    : (L1 ++ L2).set i x = L1 ++ L2.set (i - L1.length) x
    := by
    induction L1 generalizing i with
    | nil => simp [set]
    | cons hd tl ih =>
    match i with
    | 0 =>
      simp at h
    | i+1 =>
      simp at h
      simp [set]
      apply ih
      apply Nat.le_of_succ_le_succ h
  
  theorem map_set {L : List τ} {i x} {f : τ → τ'}
    : (L.set i x).map f = (L.map f).set i (f x)
    := by
    induction L generalizing i with
    | nil => simp
    | cons y ys ih =>
      cases i
      simp [set]
      simp [ih]
  
  theorem set_map {L : List τ} (x') (h : x = f x')
    : (L.map f).set i x = (L.set i x').map f
    := by
    induction L generalizing i with
    | nil => simp
    | cons y ys ih =>
      cases i
      simp [set]; assumption
      simp [set, ih]

  @[deprecated attach]
  def subtypeByMem (L : List α) : List {a // a ∈ L} := attach L

  @[simp]
  theorem length_subtypeByMem (L : List α)
    : L.subtypeByMem.length = L.length
    := by unfold subtypeByMem; simp

  @[simp]
  theorem get_subtypeByMem (L : List α) (i : Fin L.subtypeByMem.length)
    : L.subtypeByMem.get i = L.get ⟨i, by cases i; case mk _ h => simp at h; assumption⟩
    := by unfold subtypeByMem; simp

  @[deprecated get_of_mem]
  def index_of_mem (L : List α) (x) (h : x ∈ L) : ∃ i, L.get i = x
    := get_of_mem h
  
  @[deprecated get_take]
  theorem get_of_take (L : List α) (n i) (_h : n ≤ L.length)
    : (L.take n).get i = L.get (i.castLE (by simp))
    := by
    apply (get_take ..).symm
    have := i.isLt
    simp at this
    exact this.1

  @[deprecated get_map_rev]
  theorem get_map_reverse (f : α → β) {l n}
    : f (get l n) = get (map f l) ⟨n, by simp [n.isLt]⟩
    := get_map_rev f

  theorem foldl_acc_cons (L : List τ) (f : _ → _) (x') (acc : List τ')
    : L.foldl (fun acc x => acc ++ f x) (x' :: acc)
      = x' :: L.foldl (fun acc x => acc ++ f x) acc
    := by
    induction L generalizing acc with
    | nil => simp [foldl]
    | cons x xs ih =>
      unfold foldl
      rw [List.cons_append, ih]

  theorem foldl_eq_reverseAux (L : List τ) (acc)
    : L.foldl (fun acc x => x :: acc) acc = L.reverseAux acc
    := by
    induction L generalizing acc with
    | nil => simp [foldl]
    | cons x xs ih =>
      unfold foldl
      apply ih

  theorem foldl_eq_map (L : List τ) (f : τ → τ')
    : L.foldl (fun acc x => acc ++ [f x]) [] = L.map f
    := by
    induction L with
    | nil => simp [foldl]
    | cons x xs ih =>
      unfold foldl
      simp [foldl_acc_cons]
      apply ih

  theorem foldl_filter (L : List τ) (f : τ → Bool) (foldF) (foldAcc : β)
    : (L.filter f).foldl foldF foldAcc =
      L.foldl (fun acc x => if f x then foldF acc x else acc) foldAcc
    := by
    induction L generalizing foldAcc with
    | nil => simp [foldl]
    | cons x xs ih =>
      unfold filter
      split
      case cons.h_1 h =>
        simp [h, foldl, ih]
      case cons.h_2 h =>
        simp [h, foldl, ih]
  
  theorem foldr_eq_map (L : List τ) (f : τ → τ')
    : L.foldr (f · :: ·) [] = L.map f
    := by induction L <;> simp; assumption
  
  theorem foldr_eq_filter (L : List τ) (f : τ → Bool)
    : L.foldr (fun x acc => if f x then x :: acc else acc) [] = L.filter f
    := by rw [filter_eq_foldr f L]; congr; funext; rw [Bool.cond_eq_ite]

  theorem foldr_cons_eq_foldl_append (L : List τ) (f : _ → β)
    : L.foldr (f · :: ·) [] = L.foldl (· ++ [f ·]) []
    := by rw [foldr_eq_map, foldl_eq_map]

  @[deprecated filter_eq_foldr]
  theorem foldl_eq_filter (L : List τ) (f : τ → Bool)
    : L.foldl (fun acc x => acc ++ if f x then [x] else []) [] = L.filter f
    := sorry

  @[deprecated mem_map]
  theorem mem_of_map_iff (L : List τ) (f : τ → τ')
    : ∀ y, y ∈ L.map f ↔ ∃ x, x ∈ L ∧ f x = y
    := fun _ => mem_map

end List

namespace Function  
  def update' {α α' : Sort u} {β : α → Sort u} (f : (a : α) → β a) (i : α) (x : α') [D : DecidableEq α]
    : (a : α) → update β i α' a
    := λ a =>
    if h:a = i
    then cast (by simp [h, update]) x
    else cast (by simp [h]) (f a)
end Function

def Cached {α : Type _} (a : α) := { b // b = a }

namespace Cached

instance {a : α} : DecidableEq (Cached a) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ => Decidable.isTrue (by cases hx; cases hy; rfl)

instance {a : α} [Repr α] : Repr (Cached a) where
  reprPrec x := Repr.addAppParen <| "cached " ++ repr x.val

instance {a : α} : Subsingleton (Cached a) :=
  ⟨by intro ⟨x, h⟩; cases h; intro ⟨y, h⟩; cases h; rfl⟩

instance {a : α} : CoeHead (Cached a) α where
  coe x := x.1

def cached (a : α) : Cached a :=
  ⟨a, rfl⟩

def cached' (a : α) (h : a = b) : Cached b :=
  ⟨a, h⟩

instance {a : α} : Inhabited (Cached a) where
  default := cached a

@[simp] theorem cached_val (a : α) (b : Cached a) : (b : α) = a := b.2

end Cached

export Cached (cached)
export Cached (cached')

def time (f : IO α) : IO (Nat × α) := do
  let pre ← IO.monoMsNow
  let ret ← f
  let post ← IO.monoMsNow
  pure (post-pre, ret)
