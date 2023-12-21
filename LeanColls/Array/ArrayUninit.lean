/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Range

namespace LeanColls

@[extern "leancolls_array_initialize"] private opaque arrayInit : IO Unit

builtin_initialize arrayInit

opaque ArrayUninit.Pointed (α : Type u) (n m : Nat) (h : m ≤ n): NonemptyType.{u}

def ArrayUninit (α) (n m : Nat) (h : m ≤ n) := (ArrayUninit.Pointed α n m h).type

namespace ArrayUninit

instance : Nonempty (ArrayUninit α n m h) := (ArrayUninit.Pointed α n m h).property

axiom partiallyInit_inhabited {α n m h} (A : ArrayUninit α n (.succ m) h) : Inhabited α

@[extern "leancolls_array_new"]
opaque new (n : @& Nat) : ArrayUninit α n 0 (Nat.zero_le _)

@[extern "leancolls_array_get"]
opaque get {n m : @& Nat} {h} (A : @& ArrayUninit α n m h) (i : @& Nat) (h_im : i < m) : α
  := match m with
  | 0 => by contradiction
  | m+1 => (partiallyInit_inhabited A).default

@[extern "leancolls_array_push"]
opaque push {n m : @& Nat} {h} (A : ArrayUninit α n m h) (x : α) (h' : m < n) : ArrayUninit α n m.succ h'

@[extern "leancolls_array_pop"]
opaque pop {n m : @& Nat} {h} (A : ArrayUninit α n m.succ h) : ArrayUninit α n m (Nat.le_of_succ_le h)

@[extern "leancolls_array_set"]
opaque set {n m : @& Nat} {h} (A : ArrayUninit α n m h) (i : @& Nat) (h_i : i < m) (x : α) : ArrayUninit α n m h

@[extern "leancolls_array_resize"]
opaque resize {n m : @& Nat} {h} (A : ArrayUninit α n m h) (n' : @& Nat) (h' : m <= n') : ArrayUninit α n' m h'

@[extern "leancolls_array_isexclusive"]
opaque isExclusive (a : @& ArrayUninit α n m h) : Bool

@[simp]
axiom get_push {α n m h} {A : ArrayUninit α n m h} {x h' i hm}
  : get (push A x h') i hm =
    if h_i : i = m then x
    else get A i (Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ hm) h_i)

@[simp]
axiom get_pop {α n m h} {A : ArrayUninit α n (.succ m) h} {i hm}
  : get (pop A) i hm = get A i (Nat.le_step hm)

@[simp]
axiom get_set {α n m h} {A : ArrayUninit α n m h} {i hi x j hm}
  : get (set A i hi x) j hm =
    if i = j then x
    else get A j hm

@[simp]
axiom get_resize {α n m h} {A : ArrayUninit α n m h} {n' h' i hm}
  : get (resize A n' h') i hm = get A i hm

axiom ext {α n m h} {A B : ArrayUninit α n m h} : A.get = B.get → A = B

@[simp]
theorem ext_iff {α n m h} {A B : ArrayUninit α n m h}
  : A = B ↔ A.get = B.get := by
  constructor
  intro eq; rw [eq]
  exact ext

def init {α : Type u} {n m : Nat} (hn : m ≤ n) (f : Fin m → α) : ArrayUninit α n m hn :=
  have res := Range.foldl'' ⟨m⟩
    (motive := fun i => Σ' h, Σ' (A : ArrayUninit α n i (Nat.le_trans h hn)),
      ∀ j hm, A.get j hm =
              f ⟨j, (Nat.lt_of_lt_of_le hm h)⟩)
    (fun i h_i ⟨_, A, h⟩ =>
      ⟨h_i, A.push (f ⟨i,h_i⟩) (Nat.lt_of_lt_of_le h_i hn), by
        intro j hj
        simp
        have := Nat.lt_or_eq_of_le <| Nat.le_of_succ_le_succ hj
        cases this
        case inr hj => simp [hj]
        case inl hj =>
          simp [Nat.ne_of_lt hj]
          apply h⟩
    ) ⟨Nat.zero_le _, ArrayUninit.new n, by intro _ hj; contradiction⟩
  res.2.1

@[simp]
theorem get_init {α : Type u} (hm : m ≤ n) (f : Fin m → α) (i hi)
  : get (init hm f) i hi = f ⟨i,hi⟩
  := by
  simp [init]
  generalize Range.foldl'' _ _ _ _ = res
  apply res.2.2
