/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

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
opaque get {n m : @& Nat} {h} (A : @& ArrayUninit α n m h) (i : @& Nat) (h_in : i < n) (h_im : i < m) : α
  := match m with
  | 0 => by contradiction
  | m+1 => (partiallyInit_inhabited A).default

@[extern "leancolls_array_push"]
opaque push {n m : @& Nat} {h} (A : ArrayUninit α n m h) (x : α) (h' : m < n) : ArrayUninit α n m.succ h'

@[extern "leancolls_array_pop"]
opaque pop {n m : @& Nat} {h} (A : ArrayUninit α n m.succ h) : ArrayUninit α n m (Nat.le_of_succ_le h)

@[extern "leancolls_array_set"]
opaque set {n m : @& Nat} {h} (A : ArrayUninit α n m h) (i : @& Nat) (h_i : i < n) (x : α) : ArrayUninit α n m h

@[extern "leancolls_array_resize"]
opaque resize {n m : @& Nat} {h} (A : ArrayUninit α n m h) (n' : @& Nat) (h' : m <= n') : ArrayUninit α n' m h'

@[extern "leancolls_array_isexclusive"]
opaque isExclusive {n m : @& Nat} {h} (A : @& ArrayUninit α n m h) : Bool

@[simp]
axiom get_push {α n m h} {A : ArrayUninit α n m h} {x h' i hn hm}
  : get (push A x h') i hn hm =
    if h_i : i = m then x
    else get A i hn (Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ hm) h_i)

@[simp]
axiom get_pop {α n m h} {A : ArrayUninit α n (.succ m) h} {i hn hm}
  : get (pop A) i hn hm = get A i hn (Nat.le_step hm)

@[simp]
axiom get_set {α n m h} {A : ArrayUninit α n m h} {i hi x j hn hm}
  : get (set A i hi x) j hn hm =
    if i = j then x
    else get A j hn hm

@[simp]
axiom get_resize {α n m h} {A : ArrayUninit α n m h} {n' h' i hn hm}
  : get (resize A n' h') i hn hm = get A i (Nat.lt_of_lt_of_le hm h) hm

axiom ext {α n m h} {A B : ArrayUninit α n m h} : A.get = B.get → A = B

@[simp]
theorem ext_iff {α n m h} {A B : ArrayUninit α n m h}
  : A = B ↔ A.get = B.get := by
  constructor
  intro eq; rw [eq]
  exact ext
