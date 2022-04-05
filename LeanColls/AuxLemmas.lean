/-
Copyright (c) 2021 James Gallicchio.

Authors: James Gallicchio
-/

namespace Nat
  theorem sub_dist (x y z : Nat) : x - (y + z) = x - y - z := by
    induction z
    simp
    case succ z z_ih =>
    simp [Nat.sub_succ, Nat.add_succ, z_ih]

  theorem lt_of_lt_le {x y z : Nat} : x < y → y ≤ z → x < z := by
    intro h h'
    induction h'
    assumption
    apply Nat.le_step
    assumption

  theorem min_le_left {x y : Nat} : min x y ≤ x := by
    simp [min]
    split
    simp
    case inr h =>
    rw [Nat.not_le_eq] at h
    exact Nat.le_of_succ_le h

  theorem min_le_right {x y : Nat} : min x y ≤ y := by
    simp [min]
    split
    assumption
    simp

  theorem min_succ_succ {x y : Nat} : min x.succ y.succ = (min x y).succ := by
    simp [min]
    split <;> split
    rfl
    case inl.inr h h' =>
      exact False.elim (h' (Nat.le_of_succ_le_succ h))
    case inr.inl h h' =>
      exact False.elim (h (Nat.succ_le_succ h'))
    rfl

  @[simp]
  theorem min_zero_left {x} : min 0 x = 0 := by
    rw [←Nat.le_zero_eq]
    exact min_le_left

  @[simp]
  theorem min_zero_right {x} : min x 0 = 0 := by
    rw [←Nat.le_zero_eq]
    exact min_le_right

end Nat

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
        have : back? (y::z) = some (tail, t) := by
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
        have := ih _ this
        rw [this] at h
        simp [back?] at h
        rw [this,h]

  @[simp]
  theorem concat_append (L₁ L₂ : List τ)
    : (L₁ ++ L₂).concat x = L₁ ++ L₂.concat x
    := by
    induction L₁
    simp
    case cons h t ih =>
    simp [concat]
    exact ih

  @[simp]
  theorem map_concat (L : List τ) (f : τ → α)
    : (L.concat x).map f = (L.map f).concat (f x)
    := by
    induction L
    simp [concat,map]
    case cons h t ih =>
    simp [concat,map]
    exact ih

  @[simp]
  theorem join_concat (L : List (List τ))
    : (L.concat x).join = L.join ++ x
    := by
    induction L
    simp [concat,join]
    case cons h t ih =>
    simp [ih,concat,join,List.append_assoc]
  
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
      exact this
  
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
  
  def length_take (L : List τ) (n : Nat)
    : (L.take n).length = min L.length n
    := by
      induction L generalizing n
      cases n <;> simp [length, take, min]
      case cons h t ih =>
      cases n
      simp [take, min]
      case succ n =>
      simp [take, ih n]
      exact Nat.min_succ_succ.symm
  
  def subtypeByMem (L : List α) : List {a // a ∈ L} :=
    let rec aux (rest : List α) (h : ∀ a, a ∈ rest → a ∈ L)
      : List {a // a ∈ L} :=
      match rest with
      | [] => []
      | (x::xs) =>
        ⟨x, h _ (List.Mem.head _ _)⟩ ::
        aux xs (by intros; apply h; apply List.Mem.tail; assumption)
    aux L (by intros; assumption)

  theorem length_subtypeByMemAux (L rest : List α) (h)
    : (List.subtypeByMem.aux L rest h).length = rest.length
    := by
      induction rest
      simp [subtypeByMem.aux]
      case cons hd tl ih =>
      simp [subtypeByMem.aux]
      apply ih

  @[simp]
  theorem length_subtypeByMem (L : List α)
    : L.subtypeByMem.length = L.length
    := by apply length_subtypeByMemAux

  def index_of_mem (L : List α) (x) (h : x ∈ L) : ∃ i, L.get i = x := by
    induction L
    cases h <;> contradiction
    case cons hd tl ih =>
    cases h
    apply Exists.intro ⟨0,by apply Nat.succ_le_succ; exact Nat.zero_le _⟩
    simp [get]
    cases ih (by assumption)
    case intro w h =>
    apply Exists.intro w.succ
    simp [get]
    exact h

  theorem get_of_take (L : List α) (n i) (h : n ≤ L.length)
    : (L.take n).get i = L.get ⟨i.val, by
        apply Nat.le_trans i.isLt
        simp [length_take]
        exact Nat.min_le_left
      ⟩
    := by
    induction L generalizing n
    case nil =>
      cases n <;> (
        simp [length, take] at i
        exact Fin.elim0 i
      )
    case cons hd tl ih =>
    cases n
    case zero =>
      simp [length, take] at i
      exact Fin.elim0 i
    case succ n =>
      cases i; case mk i h_i =>
      cases i
      case zero =>
        simp [get, take]
      case succ i =>
        simp [get, take]
        apply ih
        simp [length] at h
        exact Nat.le_of_succ_le_succ h

end List

def Nat.toUSize! (n : Nat) : USize :=
  if n < USize.size then
    n.toUSize
  else
    panic! s!"Integer {n} is to larget for usize"

namespace Option

def get : (o : Option α) → o.isSome → α
| none, h => by contradiction
| some a, _ => a

end Option

class Monoid (M) where
  mId : M
  mApp : M → M → M
  h_idl : ∀ v, mApp mId v = v
  h_idr : ∀ v, mApp v mId = v
  h_assoc : ∀ v1 v2 v3, mApp (mApp v1 v2) v3 = mApp v1 (mApp v2 v3)

namespace Monoid

instance [Monoid M] : Append M where
  append := Monoid.mApp

@[simp]
theorem mApp_assoc [Monoid M] : ∀ (v1 v2 v3 : M), v1 ++ v2 ++ v3 = v1 ++ (v2 ++ v3) := Monoid.h_assoc

instance : Monoid Nat where
  mId := 0
  mApp := Nat.add
  h_idl := by simp
  h_idr := by simp
  h_assoc := Nat.add_assoc

end Monoid


def Cached {α : Type _} (a : α) := { b // b = a }

namespace Cached

instance {a : α} : DecidableEq (Cached a) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ => Decidable.isTrue (by cases hx; cases hy; rfl)

instance {a : α} : Repr (Cached a) where
  reprPrec x := Repr.addAppParen "cached _"

instance {a : α} : Subsingleton (Cached a) :=
  ⟨by intro ⟨x, h⟩; cases h; intro ⟨y, h⟩; cases h; rfl⟩

instance {a : α} : CoeHead (Cached a) α where
  coe x := x.1

def cached (a : α) : Cached a :=
  ⟨a, rfl⟩

instance {a : α} : Inhabited (Cached a) where
  default := cached a

@[simp] theorem cached_val (a : α) (b : Cached a) : (b : α) = a := b.2

end Cached

export Cached (cached)

def time (f : IO α) : IO (Nat × α) := do
  let pre ← IO.monoMsNow
  let ret ← f
  let post ← IO.monoMsNow
  pure (post-pre, ret)
