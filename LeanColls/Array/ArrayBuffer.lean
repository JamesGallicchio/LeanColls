import LeanColls.Array.Basic

namespace LeanColls

structure ArrayBuffer (α) where
  cap : Nat
  h_cap : 1 ≤ cap
  size : Fin cap.succ
  backing : Array (Uninit α) cap
  h_filled : ∀ i, (h : i < size.val) →
    backing.get ⟨i, Nat.lt_of_lt_le h <| Nat.le_of_succ_le_succ size.isLt⟩
    |>.isInit

namespace ArrayBuffer

def empty (_ : Unit) (initCap : Nat := 16) (h_cap : 1 ≤ initCap := by decide) : ArrayBuffer α := ⟨
  initCap,
  h_cap,
  ⟨0, Nat.le_step h_cap⟩,
  Array.new (Uninit.uninit) initCap,
  by intro i h; simp [Fin.val] at h; contradiction
  ⟩

@[inline] def full (A : ArrayBuffer α) : Bool := A.size.val = A.cap

def grow : ArrayBuffer α → ArrayBuffer α :=
λ ⟨cap, h_cap, size, backing, h_backing⟩ =>
  let newCap := 2 * cap
  have : cap < newCap := by
    have := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self 1) h_cap
    simp at this ⊢
    assumption
  ⟨newCap, Nat.le_trans h_cap <| Nat.le_of_lt this,
    ⟨size, Nat.lt_trans size.isLt $ Nat.succ_lt_succ this⟩,
    backing.resize (Uninit.uninit) newCap,
    by
      intro i h
      simp at h
      have : i < cap := Nat.lt_of_lt_le h (Nat.le_of_succ_le_succ size.isLt)
      simp [Array.get, Array.resize, this]
      apply h_backing
      assumption
      ⟩

theorem grow_notfull (A : ArrayBuffer α)
  : ¬A.grow.full
  := by
    simp [full,grow]
    apply (decide_eq_false_iff_not _).mpr
    suffices A.size.val < 2 * A.cap from
      Nat.ne_of_lt this
    have := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self 1) A.h_cap
    simp at this ⊢
    apply Nat.lt_of_le_of_lt (Nat.le_of_succ_le_succ A.size.isLt)
    assumption

@[inline] def push_notfull (A : ArrayBuffer α) (h : ¬A.full) (a : α) : ArrayBuffer α
  :=
    match A with
    | ⟨cap, h_cap, size, backing, h_backing⟩ =>
    have h_size :=
      Nat.le_of_lt_succ $
      Nat.lt_of_le_of_ne size.isLt (by
      simp [full] at h; intro h'; apply h; injection h'; assumption)
    ⟨ cap, h_cap, ⟨size.val + 1, Nat.succ_le_succ h_size⟩,
      backing.set ⟨size,h_size⟩ (Uninit.init a),
      by
        intro i h_i
        cases size; case mk size _ =>
        by_cases h : i = size
        cases h
        rw [backing.get_of_set_eq]
        exact Uninit.isInit_init
        simp [Fin.eq_of_val_eq]
        rw [backing.get_of_set_ne _ _ _ (by simp; exact h ∘ Eq.symm)]
        have h_i : i < size := Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ h_i) h
        exact h_backing i h_i⟩

def push (A : ArrayBuffer α) (a : α) : ArrayBuffer α :=
  if h:A.size.val = A.cap then
    A.grow.push_notfull (A.grow_notfull) a
  else
    A.push_notfull (by simp [full,h]) a


def toArray (A : ArrayBuffer α) : Array α A.size :=
  A.backing.resize (unreachable!) A.size
  |>.allInit <| by
    intro ⟨i,h_i⟩
    have : i < A.cap := Nat.lt_of_lt_le h_i <| Nat.le_of_succ_le_succ A.size.isLt
    simp [Array.resize, Array.get, this]
    exact A.h_filled _ h_i

end ArrayBuffer

instance : Enumerable (Σ n, Array α n) α where
  ρ := ArrayBuffer α
  insert A :=
    match A with
    | some ⟨a,A⟩ => A.push a
    | none => ArrayBuffer.empty ()
  fromEnumerator A := ⟨A.size, A.toArray⟩
