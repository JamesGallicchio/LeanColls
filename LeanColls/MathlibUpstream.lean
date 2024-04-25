/- Copyright (c) 2023 James Gallicchio.

Authors: James Gallicchio
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.ProdSigma
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

def Fin.foldl' (n : Nat) {β : (i : Nat) → i ≤ n → Sort u}
      (init : β 0 (Nat.zero_le _))
      (f : (i : Nat) → (h : i < n) → β i (Nat.le_of_lt h) → β (i+1) h)
      : β n (Nat.le_refl _) :=
  aux _ _ init
where
  aux (i : Nat) (h : i ≤ n) (acc : β i h) : β n (Nat.le_refl _) :=
    if h' : i < n then
      aux (i+1) h' (f i h' acc)
    else
      have : i = n := Nat.le_antisymm h (Nat.not_lt.mp h')
      this ▸ acc
termination_by n-i

theorem Fin.foldl_eq_foldl' (n : Nat) (f : α → Fin n → α) (init : α)
  : Fin.foldl n f init = Fin.foldl' (n := n) (β := fun _ _ => α) init (fun i h acc => f acc ⟨i,h⟩)
  := by
  simp [foldl, foldl']
  suffices ∀ i j (hj : i + j = n) acc,
    foldl.loop n f acc i =
      foldl'.aux (n := n) (β := fun _ _ => α)
        init (fun i h acc => f acc ⟨i, h⟩)
        i (hj ▸ Nat.le_add_right i j) acc
    from this 0 n (by simp) init
  intro i j hj
  induction j generalizing i with
  | zero =>
    intro acc
    simp at hj; cases hj
    unfold foldl.loop; unfold foldl'.aux
    simp
  | succ j' ih =>
    intro acc
    simp_all
    rw [Nat.add_succ, ← Nat.succ_add] at hj
    have hi : i < n := by calc
      _ ≤ Nat.succ i + j' := Nat.le_add_right _ _
      _ = n := hj
    have := ih (i+1) hj (f acc ⟨i,hi⟩)
    clear ih
    unfold foldl.loop; unfold foldl'.aux
    simp [*]

def Fin.foldlM [Monad m] (n : Nat) {β : Type u}
      (init : β)
      (f : Fin n → β → m β)
      : m β :=
  aux 0 init
where
  aux (i : Nat) (acc : β) : m β :=
    if h' : i < n then
      f ⟨i, h'⟩ acc >>= fun acc => aux (i+1) acc
    else
      pure acc
termination_by n-i

theorem Fin.foldlM_eq_foldl [Monad m] [LawfulMonad m] (n : Nat) {β : Type u} (init : β)
    (f : Fin n → β → m β)
  : Fin.foldlM n init f = Fin.foldl n (fun macc i => macc >>= fun acc => f i acc) (pure init)
  := by
  simp [foldl, foldlM]
  suffices ∀ i j (hj : i + j = n) macc,
    (macc >>= fun acc => foldlM.aux n f i acc) =
      foldl.loop n _ macc i
    by
    have := this 0 n (by simp) (pure init)
    simp at this
    exact this
  intro i j hj
  induction j generalizing i with
  | zero =>
    intro macc
    simp at hj; cases hj
    unfold foldl.loop; unfold foldlM.aux
    simp
  | succ j' ih =>
    intro macc
    rw [Nat.add_succ, ← Nat.succ_add] at hj
    have hi : i < n := by calc
      _ ≤ Nat.succ i + j' := Nat.le_add_right _ _
      _ = n := hj
    have := ih (i+1) hj (macc >>= fun acc => f ⟨i,hi⟩ acc)
    clear ih
    unfold foldl.loop; unfold foldlM.aux
    simp_all

theorem Fin.foldl_eq_foldl_ofFn (n) (f : α → Fin n → α) (init : α)
  : Fin.foldl n f init = List.foldl f init (List.ofFn id) := by
  unfold foldl
  suffices ∀ init i j (h : i + j = n),
    foldl.loop n f init i =
      List.foldl f init (List.ofFn (n := j) (fun x => Fin.natAdd i x |>.cast h))
    by
      have := this init 0 n (by simp)
      simp at this; rw [this]; rfl
  intro init i j h
  induction j generalizing init i with
  | zero =>
    unfold foldl.loop
    simp at h
    simp [List.drop_eq_nil_of_le, h]
  | succ j ih =>
    unfold foldl.loop
    have : i < n := by omega
    simp [this, cast]
    generalize f init _ = init'
    have : (i+1) + j = n := by omega
    specialize ih init' (i+1) this
    rw [ih]; clear ih
    congr
    funext ⟨x,hx⟩; simp; omega

@[inline]
def Fin.pair (x : Fin m) (y : Fin n) : Fin (m * n) :=
  ⟨ x * n + y, by
    rcases x with ⟨x,hx⟩; rcases y with ⟨y,hy⟩
    simp
    calc
      _ < x * n + n := by simp [hx,hy]
      _ ≤ (x+1) * n := by rw [Nat.succ_mul]
      _ ≤ m * n := Nat.mul_le_mul_right _ hx⟩

@[inline]
def Fin.pair_left : Fin (m * n) → Fin m
| ⟨p,h⟩ =>
  ⟨ p / n, by
    rw [Nat.div_lt_iff_lt_mul]
    · exact h
    · by_contra; simp_all
  ⟩

@[inline]
def Fin.pair_right : Fin (m * n) → Fin n
| ⟨p,h⟩ =>
  ⟨ p % n, by
    apply Nat.mod_lt
    by_contra; simp_all
  ⟩

@[simp]
theorem Fin.pair_left_pair (x : Fin m) (y : Fin n) : Fin.pair_left (Fin.pair x y) = x := by
  rcases x with ⟨x,hx⟩; rcases y with ⟨y,hy⟩
  simp [pair_left, pair]
  have : n > 0 := by by_contra; simp_all
  rw [Nat.mul_comm, Nat.mul_add_div this, (Nat.div_eq_zero_iff this).mpr hy]
  simp

@[simp]
theorem Fin.pair_right_pair (x : Fin m) (y : Fin n) : Fin.pair_right (Fin.pair x y) = y := by
  rcases x with ⟨x,hx⟩; rcases y with ⟨y,hy⟩
  simp [pair_right, pair]
  have : n > 0 := by by_contra; simp_all
  rw [Nat.mul_comm, Nat.mul_add_mod _ _ _]
  apply Nat.mod_eq_of_lt hy

@[simp]
theorem Fin.pair_left_right (p : Fin (m * n)) : Fin.pair (Fin.pair_left p) (Fin.pair_right p) = p := by
  rcases p with ⟨p,hp⟩
  simp [pair, pair_left, pair_right]
  exact Nat.div_add_mod' p n

theorem Fin.pair_succ_left (x : Fin m) (y : Fin n) : (Fin.pair (x.succ) y).val = Fin.pair x y + n := by
  simp [pair, Nat.add_mul]; ring

theorem Fin.pair_ge_left (x : Fin m) (y : Fin n) : Fin.pair x y ≥ x.val * n := by simp [pair]

/-- `Fin.pair` is the "natural" way to index into `List.product`. -/
theorem List.get_product_fin_pair (L1 : List α) (L2 : List β)
    {i : Fin L1.length} {j : Fin L2.length} {p} (hp : p.val = (Fin.pair i j).val)
  : List.get (L1 ×ˢ L2) p =
      (List.get L1 i, List.get L2 j) := by
  generalize hLL : L1 ×ˢ L2 = LL at p
  induction L1 generalizing LL p with
  | nil =>
    exact i.elim0
  | cons hd tl ih =>
    dsimp at i
    induction i using Fin.cases
    case zero =>
      rcases p with ⟨p,_⟩
      simp [Fin.pair] at hp
      have : p < L2.length := by rw [hp]; exact j.isLt
      simp [product_cons] at hLL
      subst LL
      rw [get_append_left]
      case h => simp [this]
      simp; congr
    case succ i =>
      specialize @ih i (tl ×ˢ L2) rfl (Fin.pair i j |>.cast (List.length_product ..).symm) rfl
      simp; rw [← ih]; clear ih
      rcases p with ⟨p,h⟩
      simp at hp hLL
      subst p LL
      simp [Nat.add_mul, length_product] at h ⊢
      rw [get_append_right]
      case h =>
        simp
        trans i.succ * L2.length
        · simp [Nat.add_mul]
        · apply Fin.pair_ge_left
      case h'' =>
        simp [length_product, Fin.pair_succ_left]
      congr
      simp [Fin.pair_succ_left]

theorem List.get_product_eq_get_pair (L1 : List α) (L2 : List β) (i : Fin ((List.product L1 L2).length))
  : List.get (L1 ×ˢ L2) i =
    ( List.get L1 (Fin.pair_left <| i.cast (by apply List.length_product))
    , List.get L2 (Fin.pair_right <| i.cast (by apply List.length_product))) := by
  generalize hleft : Fin.pair_left _ = left
  generalize hright : Fin.pair_right _ = right
  have : i = (Fin.pair left right).cast (by apply (List.length_product ..).symm) := by
    simp [← hleft, ← hright]
  clear hleft hright
  subst i
  rw [List.get_product_fin_pair]
  simp

theorem List.foldl_product (f : γ → α × β → γ) (init : γ)
  : List.foldl f init (L1 ×ˢ L2) =
      List.foldl (fun acc a =>
        List.foldl (fun acc b => f acc (a,b)) acc L2
        ) init L1 := by
  induction L1 generalizing init <;> simp
  case cons hd tl ih =>
  rw [ih]; simp [foldl_map]

section UIntFacts

theorem UInt8.add_def (i j : UInt8) : i + j = ⟨i.val + j.val⟩ := rfl
theorem UInt16.add_def (i j : UInt16) : i + j = ⟨i.val + j.val⟩ := rfl
theorem UInt32.add_def (i j : UInt32) : i + j = ⟨i.val + j.val⟩ := rfl
theorem UInt64.add_def (i j : UInt64) : i + j = ⟨i.val + j.val⟩ := rfl

theorem UInt8.toNat_ofNat (n : Nat) : (OfNat.ofNat n : UInt8).toNat = n % UInt8.size := rfl

end UIntFacts

section LinearOrders

instance : LinearOrder UInt8 where
  decidableLE := inferInstance
  le_refl := by
    simp [LE.le]; unfold UInt8.le; simp
  le_trans := by
    simp [LE.le]; unfold UInt8.le
    intro a b c; apply Preorder.le_trans
  le_antisymm := by
    simp [LE.le]; unfold UInt8.le
    intro a b hab hba; apply UInt8.ext; apply PartialOrder.le_antisymm <;> assumption
  le_total := by
    simp [LE.le]; unfold UInt8.le
    intro a b; apply LinearOrder.le_total
  lt_iff_le_not_le := by
    simp [LE.le, LT.lt]; unfold UInt8.le UInt8.lt
    intro a b; apply Preorder.lt_iff_le_not_le

instance : LinearOrder UInt16 where
  decidableLE := inferInstance
  le_refl := by
    simp [LE.le]; unfold UInt16.le
    simp
  le_trans := by
    simp [LE.le]; unfold UInt16.le
    intro a b c; apply Preorder.le_trans
  le_antisymm := by
    simp [LE.le]; unfold UInt16.le
    intro a b hab hba; apply UInt16.ext; apply PartialOrder.le_antisymm <;> assumption
  le_total := by
    simp [LE.le]; unfold UInt16.le
    intro a b; apply LinearOrder.le_total
  lt_iff_le_not_le := by
    simp [LE.le, LT.lt]; unfold UInt16.le UInt16.lt
    intro a b; apply Preorder.lt_iff_le_not_le

instance : LinearOrder UInt32 where
  decidableLE := inferInstance
  le_refl := by
    unfold LE.le; simp [instLEUInt32]
  le_trans := by
    unfold LE.le; simp [instLEUInt32]
    intro a b c; apply Preorder.le_trans
  le_antisymm := by
    unfold LE.le; simp [instLEUInt32]
    intro a b hab hba; apply UInt32.ext; apply PartialOrder.le_antisymm <;> assumption
  le_total := by
    unfold LE.le; simp [instLEUInt32]
    intro a b; apply LinearOrder.le_total
  lt_iff_le_not_le := by
    unfold LE.le LT.lt; simp only [instLEUInt32, instLTUInt32]
    intro a b; apply Preorder.lt_iff_le_not_le

instance : LinearOrder UInt64 where
  decidableLE := inferInstance
  le_refl := by
    simp [LE.le]; unfold UInt64.le; simp
  le_trans := by
    simp [LE.le]; unfold UInt64.le
    intro a b c; apply Preorder.le_trans
  le_antisymm := by
    simp [LE.le]; unfold UInt64.le
    intro a b hab hba; apply UInt64.ext; apply PartialOrder.le_antisymm <;> assumption
  le_total := by
    simp [LE.le]; unfold UInt64.le
    intro a b; apply LinearOrder.le_total
  lt_iff_le_not_le := by
    simp [LE.le, LT.lt]; unfold UInt64.le UInt64.lt
    intro a b; apply Preorder.lt_iff_le_not_le

instance : BoundedOrder UInt8 where
  top := ⟨⊤⟩
  le_top := by rintro ⟨x⟩; simp [instLEUInt8, UInt8.le]
  bot := ⟨⊥⟩
  bot_le := by rintro ⟨x⟩; simp [instLEUInt8, UInt8.le]

instance : BoundedOrder UInt16 where
  top := ⟨⊤⟩
  le_top := by rintro ⟨x⟩; simp [instLEUInt16, UInt16.le]
  bot := ⟨⊥⟩
  bot_le := by rintro ⟨x⟩; simp [instLEUInt16, UInt16.le]

instance : BoundedOrder UInt32 where
  top := ⟨⊤⟩
  le_top := by rintro ⟨x⟩; simp [instLEUInt32]
  bot := ⟨⊥⟩
  bot_le := by rintro ⟨x⟩; simp [instLEUInt32]

instance : BoundedOrder UInt64 where
  top := ⟨⊤⟩
  le_top := by rintro ⟨x⟩; simp [instLEUInt64, UInt64.le]
  bot := ⟨⊥⟩
  bot_le := by rintro ⟨x⟩; simp [instLEUInt64, UInt64.le]

end LinearOrders
