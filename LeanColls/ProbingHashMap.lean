import LeanColls.Classes.Dict
import LeanColls.Data.Array

import Mathlib

namespace LeanColls

namespace LHashMap

@[simp]
theorem Fin.val_zero [NeZero n] : (0 : Fin n).val = 0 := rfl

def Mod (n) := Fin n
namespace Mod
instance : HAdd (Mod n) Nat (Mod n) where
  hAdd := fun x y => (show Fin n from x) + (Fin.ofNat' y x.pos)
instance : DecidableEq (Mod n) := inferInstanceAs (DecidableEq (Fin n))
instance : HSub (Mod n) (Mod n) Nat where
  hSub := fun x y => Fin.sub x y

@[simp]
theorem add_zero (x : Mod n) : x + 0 = x := by
  rw [Fin.ext_iff]; cases x
  simp [instHAddNat, Fin.ofNat', Fin.val_add]
  apply Nat.mod_eq_of_lt; assumption

theorem add_assoc (x : Mod n) (y z : Nat) : x + y + z = x + (y + z) := by
  cases x; rw [Fin.ext_iff]; simp [instHAddNat, Nat.add_assoc]

@[simp]
theorem sub_self (x : Mod n) : x - x = (0 : Nat) := by
  cases x; simp [instHSubNat, Fin.sub]
  convert Nat.mod_self _
  omega

@[simp]
theorem sub_lt (x y : Mod n) : x - y < n := by
  have := x.pos
  cases x; cases y; simp [instHSubNat, Fin.sub]
  apply Nat.mod_lt _ _
  assumption

theorem add_one_sub (x y : Mod n) (h : x + 1 ≠ y) : (x + 1) - y = x - y + 1 := by
  have := x.pos
  rcases x with ⟨x,hx⟩; rcases y with ⟨y,hy⟩
  simp [instHSubNat, Fin.sub, Fin.add]
  simp at h; rw [Fin.ext_iff] at h; simp [instHAddNat] at h
  rw [Nat.add_comm _ 1, Nat.add_assoc]
  if h' : x < y then
    have : x + 1 ≠ y := by
      intro h''; rw [h''] at h; apply h; apply Nat.mod_eq_of_lt; assumption
    rw [Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  else
    simp at h'
    replace h : ¬ (y = 0 ∧ x+1 = n) := by rintro ⟨rfl,rfl⟩; simp at h
    rw [Decidable.not_and_iff_or_not_not] at h
    zify; rw [Int.ofNat_sub (by omega)]
    conv => lhs; lhs; rw [show (1 : Int) + (x + (n-y)) = n + (x - y + 1) by omega]
    conv => rhs; lhs; rw [show (x : Int) + (n - y) = n + (x - y) by omega]
    simp
    rw [Int.emod_eq_of_lt, Int.emod_eq_of_lt]
    all_goals omega

@[simp]
theorem sub_self_add_one (x : Mod n) : x - (x + 1) = n-1 := by
  rcases x with ⟨x,hx⟩
  simp [instHSubNat, Fin.sub, Fin.add]
  rw [Nat.mod_eq (x := _ + 1)]
  split
  · have : x + 1 = n := by omega
    simp [this, Nat.mod_eq_of_lt hx]
    omega
  · calc (x + (n - (x + 1))) % n
      _ = (x + n - (x + 1)) % n := by rw [← Nat.add_sub_assoc hx]
      _ = (n + x - (x + 1)) % n := by rw [Nat.add_comm]
      _ = (n + x - x - 1) % n   := by rw [Nat.sub_add_eq]
      _ = (n + (x - x) - 1) % n := by rw [Nat.add_sub_assoc]; simp
      _ = (n-1) % n             := by simp
      _ = n - 1                 := Nat.mod_eq_of_lt (by omega)

theorem sub_succ_lt_sub_iff_ne (x y : Mod n)
  : x - (y + 1) < x - y ↔ x ≠ y := by
  have : n > 0 := x.pos
  rcases x with ⟨x,hx⟩
  rcases y with ⟨y,hy⟩
  simp; rw [Fin.ext_iff]
  simp [instHSubNat, Fin.sub, Fin.add]
  zify
  rw [Int.ofNat_sub (Nat.le_of_lt hy)
    , Int.ofNat_sub (n := n) (Nat.le_of_lt (Nat.mod_lt _ (by omega)))
    , Nat.mod_eq]
  simp [*]
  split
  next h =>
    replace h : n = y + 1 := by omega
    subst n
    simp
    if x = y then
      simp [*]
    else
      rw [Int.emod_eq_of_lt, Int.emod_eq_of_lt]
      simp [*]
      all_goals omega
  next h =>
    simp at h; clear hy
    by_cases (↑x : Int) - y < 0
    · rw [Int.emod_eq_of_lt (by omega) (by omega)]
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      omega
    · conv =>
        lhs; rhs
        rw [← Int.add_sub_assoc, Int.add_comm x n, Int.add_sub_assoc]
        simp
        rw [Int.emod_eq_of_lt (by omega) (by omega)]
      rw [← Int.add_sub_assoc, Int.add_comm, Int.add_sub_assoc]
      if x = y then
        simp [*]
        rw [← Int.add_emod_self, Int.emod_eq_of_lt (by omega) (by omega)]
        omega
      else
        simp [*]
        rw [Int.emod_eq_of_lt (by omega) (by omega)]
        simp

end Mod

/--
Iterator over linear indices:
`start`, `start+1`, ..., `cap-2`, `cap-1`, `0`, `1`, ..., `start-1`.
-/
structure IdxsFrom (cap : Nat) (start : Mod cap)

namespace IdxsFrom

instance : ToList (IdxsFrom cap start) (Mod cap) where
  toList := fun ⟨⟩ => List.ofFn (n := cap) (fun i => start + i.val)

@[inline]
def fold {β} (_c : IdxsFrom cap start) (f : β → Mod cap → β) (acc : β) : β :=
  aux start acc
where aux (i : Mod cap) (acc) : β :=
  let acc := f acc i
  let next : Mod cap := i + 1
  if next = start then
    acc
  else
    aux next acc
termination_by start - (i+1)
decreasing_by (
  simp_wf; simp [Mod.sub_succ_lt_sub_iff_ne]
  apply Ne.symm; assumption
)

@[inline]
def foldM [Monad m] {β} (_c : IdxsFrom cap start) (f : β → Mod cap → m β) (acc : β) : m β :=
  aux start acc
where aux (i : Mod cap) (acc) : m β := do
  let acc ← f acc i
  let next : Mod cap := i + 1
  if next = start then
    pure acc
  else
    do aux next acc
termination_by start - (i+1)
decreasing_by (
  simp_wf; simp [Mod.sub_succ_lt_sub_iff_ne]
  apply Ne.symm; assumption
)

instance : Fold (IdxsFrom cap start) (Mod cap) where
  fold := fold
  foldM := foldM

theorem fold.aux_eq_foldl_ofFn (f : β → Mod cap → β) (i) (init : β)
  : fold.aux (cap := cap) (start := start) f i init =
        List.foldl f init (List.ofFn (n := cap - (i-start)) fun j => i + j.val)
  := by
    have : cap > 0 := start.pos
    induction i, init
      using fold.aux.induct (start := start) (f := f)
    case case1 i acc next h =>
      simp [next] at h; clear next
      have : i - start = cap-1 := by
        rw [← h]; simp
      have : cap - (cap - 1) = 1 := by clear! start; omega
      unfold fold.aux
      simp [*]
    case case2 i acc acc' next h ih =>
      simp [next] at h ih; clear next
      simp [acc'] at ih; clear acc'
      unfold fold.aux
      simp [h, ih]; clear ih
      have : cap - (i - start) = cap - (i+1 - start) + 1 := by
        calc
          _ = cap - (i - start + 1) + 1 := by
            have : i - start < cap := Mod.sub_lt _ _
            rw [Nat.sub_add_eq, Nat.sub_add_cancel (by omega)]
          _ = cap - (i+1 - start) + 1 := by rw [Mod.add_one_sub _ _ h]
      simp [this]; clear this
      congr; funext; rw [Mod.add_assoc, Nat.add_comm]

theorem fold_eq_fold_toList (c : IdxsFrom cap start) (f : β → Mod cap → β) (init : β)
  : fold c f init = List.foldl f init (toList c)
  := by simp [fold, toList, fold.aux_eq_foldl_ofFn]

theorem fold.aux_bind_pure [Monad m] [LawfulMonad m] (f : β → Mod cap → m β) (i) (ma : m β)
  : ma >>= (fold.aux (start := start) (fun ma x => ma >>= (f · x)) i <| pure ·)
      = fold.aux (start := start) (fun ma x => ma >>= (f · x)) i ma := by
  simp [fold.aux_eq_foldl_ofFn]
  rw [← List.foldr_reverse]
  conv => lhs; arg 2; ext; rw [← List.foldr_reverse]
  generalize List.reverse _ = L
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp; rw [← ih]
    simp

instance : Fold.ToList (IdxsFrom cap start) (Mod cap) where
  fold_eq_fold_toList := by
    intro c; use (toList c); simp [LeanColls.fold, fold_eq_fold_toList]
  foldM_eq_fold := by
    rintro m β M LM ⟨⟩ f init
    simp [LeanColls.fold, LeanColls.foldM, foldM]
    suffices ∀ i,
      foldM.aux f i init = fold.aux _ i (pure init)
      from this start;
    intro i
    induction i, init
      using foldM.aux.induct (start := start) (f := f)
    case case1 i acc ih =>
      unfold foldM.aux fold.aux
      simp [*]
      split
      · simp [*]
      · rw [← fold.aux_bind_pure]
        congr; funext acc'
        apply ih
        assumption

end IdxsFrom

/-- TODO: replace with custom type that inlines the product -/
def Bucket (κ ν : Type u) := Option (κ × ν)

structure Data (κ ν : Type u) where
  capacity : Nat
  cap_pos : capacity > 0
  data : ArrayN (Bucket κ ν) capacity
  size : Nat


variable [Hashable κ]

def Data.startIndexOf (k : κ) (d : Data κ ν) : Mod d.capacity :=
  ⟨ (Hashable.hash k).toNat % d.capacity
  , by exact Nat.mod_lt (UInt64.toNat (hash k)) d.cap_pos⟩

def Data.idxBetween (d : Data κ ν) (lo hi : Fin d.capacity) (i : Nat) : Prop :=
  if lo ≤ hi then lo ≤ i ∧ i < hi
  else lo ≤ i ∧ i < d.capacity ∨ i < hi

theorem Data.idxBetween.lt_capacity {d : Data κ ν} {lo hi i}
  : idxBetween d lo hi i → i < d.capacity := by
  unfold idxBetween; intro h; split at h <;> omega

def Data.canIntercedeKey (b : Bucket κ ν) (k : κ) : Prop :=
  match b with
  | .none => False
  | .some (k', _) => k ≠ k'

def Data.elemValidAt (d : Data κ ν) (i : Fin d.capacity) : Prop :=
  match Indexed.get d.data i with
  | .none => True
  | .some (k, _) =>
    let start := startIndexOf k d
    ∀ j (h : d.idxBetween start i j),
      canIntercedeKey (Indexed.get d.data ⟨j, h.lt_capacity⟩) k

structure WF (d : Data κ ν) : Prop where
  size_lt_cap : d.size < d.capacity
  size_eq_nonempty : d.size = Fold.count (·.isSome) d.data
  each_elem_place_valid : ∀ i, d.elemValidAt i

end LHashMap

structure LHashMap (κ ν : Type u) [Hashable κ] where
  data : LHashMap.Data κ ν
  wf : LHashMap.WF data

namespace LHashMap

variable {κ : Type u} [Hashable κ] [BEq κ] {ν : Type u}

def findIdxOf (k : κ) (m : LHashMap κ ν) : Option (Mod m.data.capacity) :=
  let start := m.data.startIndexOf k
  Fold.first (fun i =>
      match Indexed.get m.data.data i with
      | .none => some none
      | .some (k', _) =>
        if hash k = hash k' then
          some (some i)
        else none
    )
    (⟨⟩ : IdxsFrom m.data.capacity start)
  |>.bind id

def empty (cap : Nat := 16) (cap_pos : cap > 0 := by decide) : LHashMap κ ν where
  data := {
    capacity := cap
    cap_pos := cap_pos
    data := ⟨Array.mkArray cap none, by simp [size, IndexType.card]⟩
    size := 0
  }
  wf := {
    size_lt_cap := by simp; apply cap_pos
    size_eq_nonempty := by simp; sorry
    each_elem_place_valid := sorry
  }

def get (k : κ) (m : LHashMap κ ν) : Option ν :=
  let start := m.data.startIndexOf k
  Fold.first (β := Option ν) (fun i =>
      match Indexed.get m.data.data i with
      | .none => some none
      | .some (k', v) =>
        if hash k = hash k' then
          some (some v)
        else none
    )
    (⟨⟩ : IdxsFrom m.data.capacity start)
  |>.join

def set (k : κ) (v : ν) (m : LHashMap κ ν) : LHashMap κ ν :=
  let {data,wf} := m
  let start := data.startIndexOf k
  match data, start with
  | {capacity,cap_pos,data,size}, start =>
  let idx := Fold.first (fun i =>
      match Indexed.get data i with
      | .none => some i
      | .some (k', v) =>
        if k == k' then
          some i
        else none
    )
    (⟨⟩ : IdxsFrom capacity start)
  let idx :=
    have : Inhabited (Fin capacity) := ⟨⟨0,cap_pos⟩⟩
    idx.get!
  let (old, data) := Indexed.swap data idx (some (k,v))
  let size := if old.isSome then size else size + 1
  { data := {capacity,cap_pos,data,size}
  , wf := sorry}

def delete (k : κ) (v : ν) (m : LHashMap κ ν) : LHashMap κ ν :=
  let {data,wf} := m
  let start := data.startIndexOf k
  match data, start with
  | {capacity,cap_pos,data,size}, start =>
  have res := Fold.foldM
    (m := Except (ArrayN (Bucket κ ν) capacity))
    (⟨⟩ : IdxsFrom capacity start)
    (fun (data, (lastIdx : Option (Mod capacity))) i =>
      match Indexed.get data i with
      | .none => .error data
      | .some (k', v) =>
        if k == k' then
          let data :=
            match lastIdx with
            | none => Indexed.set data i .none
            | some i' =>
              let (old,data) := Indexed.swap data i .none
              Indexed.set data i' old
          return (data, some i)
        else
          return (data, lastIdx)
    )
    (data, none)
  match res with
  | .error data =>
    -- TODO: size-1 isn't correct
    {data := {data,capacity,cap_pos,size := size-1}, wf := sorry}
  | .ok (data,_) =>
    -- TODO: size-1 isn't correct
    {data := {data,capacity,cap_pos,size := size-1}, wf := sorry}
