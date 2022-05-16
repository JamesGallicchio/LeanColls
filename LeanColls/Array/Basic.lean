/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Classes
import LeanColls.Range
import LeanColls.IndexedOps
import LeanColls.Uninit
import LeanColls.AuxLemmas
import LeanColls.View

namespace LeanColls

@[extern "leancolls_array_initialize"] private constant arrayInit : IO Unit

builtin_initialize arrayInit

structure Array (α : Type u) (n : Nat) : Type u where
  data : (i : Fin n) → α

namespace Array

-- External functions

@[extern "leancolls_array_new"]
def new (x : @&α) (n : @& Nat) : Array α n
  := ⟨λ _ => x⟩

@[extern "leancolls_array_get"]
def get {α} {n : @& Nat}
        (A : @& Array α n) (i : @& Fin n) : α
  := A.data i

@[extern "leancolls_array_set"]
def set {α} {n : @& Nat}
        (A : Array α n) (i : @& Fin n) (x : α)
  : Array α n
  := ⟨λ a => if a = i then x  else A.data a⟩

@[extern "leancolls_array_resize"]
def resize {α} {n : @& Nat} (A : Array α n)
          (x : @&α) (m : @& Nat)
  : Array α m
  := ⟨λ i => if h:i < n
    then A.data ⟨i,h⟩
    else x⟩

unsafe def allInitUnsafe (A : Array (Uninit α) n)
  (h : ∀ i, (A.get i).isInit) : Array α n
  := unsafeCast A
@[implementedBy allInitUnsafe]
def allInit (A : Array (Uninit α) n)
  (h : ∀ i, (A.get i).isInit) : Array α n
  := ⟨λ i => Uninit.getValue (A.get i) (h i)⟩

-- Preliminary theorems
@[simp]
theorem get_of_set_eq (f : Array α n) (i : Fin n) (x : α) {i' : Fin n} (h_i : i = i')
  : (f.set i x).get i' = x
  := by unfold get; unfold set; simp [h_i, Function.update, cast]

@[simp]
theorem get_of_set_ne (f : Array α n) (i : Fin n) (x : α) (j : Fin n) (h : i ≠ j)
  : (f.set i x).get j = f.get j
  := by
    unfold get; unfold set
    simp [Function.update]
    split
    exact False.elim $ h (by apply Eq.symm; assumption)
    rfl

/-!
### Array.init

Utility function necessary to provide a runtime implementation
for `Array.mk`.
-/
@[inline]
def init {α : Type u} {n : Nat} (f : Fin n → α) : Array α n
  :=
  @Range.mk n
  |>.fold (λ i A' => A'.set i (.init $ f i)) (new Uninit.uninit n)
  |>.allInit (by
    intro i
    simp [forIn, Foldable.fold, Id.run]
    refine Range.fold_ind (motive := λ i A' =>
      ∀ j : Fin n, j < i → Uninit.isInit (get A' j))
      ?init ?step i i.isLt
    case init =>
      intro j h; contradiction
    case step =>
      intro i A' h_i ih j h_j
      match Nat.eq_or_lt_of_le h_j with
      | .inl h =>
        cases h
        simp
      | .inr h =>
        have h := Nat.lt_of_succ_lt_succ h
        rw [get_of_set_ne]
        exact ih j h
        exact (Nat.ne_of_lt h).symm ∘ Fin.val_eq_of_eq
    )

/-!
Implement the auto-generated `mk` and `data` functions with
actually-correct implementations above. This seals up all
routes to interact with the `Array`, ensuring safety.
-/
attribute [implementedBy init] Array.mk
def dataImpl {α : Type u} {n : Nat}
        (A : Array α n) (i : Fin n) : α
  := A.get i
attribute [implementedBy dataImpl] Array.data

theorem init_eq_mk {f : Fin n → α}
  : init f = Array.mk f
  := by
    simp [init, forIn, Foldable.fold, Id.run, allInit]
    apply funext; intro i
    suffices Uninit.getValue? (get (Range.fold (fun i A' => set A' i (Uninit.init (f i))) (new Uninit.uninit n) {  }) i)
      = some (f i) by
      apply Uninit.getValue_of_getValue?_some
      exact this
    refine Range.fold_ind (motive := λ i A =>
      ∀ j : Fin n, j < i → Uninit.getValue? (get A j) = some (f j))
      ?init ?step i i.isLt
    case init =>
      intro j h; contradiction
    case step =>
      intro i A h_i ih j h_j
      cases j; case mk j _ =>
      match Nat.eq_or_lt_of_le h_j with
      | .inl h_j =>
        simp at h_j
        cases h_j
        simp [get_of_set_eq, Uninit.getValue?_init]
      | .inr h_j =>
        simp at h_j; have h_j := Nat.lt_of_succ_lt_succ h_j
        rw [get_of_set_ne]
        apply ih
        simp [h_j]
        simp [Fin.val_eq_of_eq, (Nat.ne_of_lt h_j).symm]

def empty : Array α 0 := init (Fin.elim0)

def copy {n : Nat} (A : Array α n) : Array α n
  := init A.get

instance : Indexed (Array α n) α where
  size _ := n
  nth := Array.get

instance : IndexedOps (Array α n) α := default

def toList (A : Array α n) : List α :=
  (@Range.mk n)
  |> View.of
  |>.map (λ i => A.get i)
  |>.toList

instance [Repr α] : Repr (Array α n) where
  reprPrec A := reprPrec (A.toList)

end Array

instance : Indexed (Array α n) α where
  size _ := n
  nth a i := a.get i

structure COWArray (α n) where
  backing : Array α n
deriving Repr

namespace COWArray
variable (A : COWArray α n)

def new (x : α) (n : Nat) := Array.new x n |> COWArray.mk
def empty : COWArray α 0 := ⟨Array.empty⟩
def singleton (x : α) : COWArray α 1 := ⟨Array.init (λ _ => x)⟩

@[inline] def get : Fin n → α := A.backing.get
@[inline] def set (i : Fin n) (x : α) : COWArray α n :=
  A.backing.copy |>.set i x |> COWArray.mk

@[inline] def update (i : Fin n) (f : α → α) : COWArray α n :=
  A.set i (f <| A.get i)

@[inline] def cons (x : α) : COWArray α n.succ :=
  ⟨Array.init (λ i => match i with
    | ⟨0,_⟩ => x
    | ⟨i+1,h⟩ => A.get ⟨i, Nat.lt_of_succ_lt_succ h⟩)⟩

@[inline] def snoc (x : α) : COWArray α n.succ :=
  ⟨Array.init (λ i =>
    if h:i < n then
      A.get ⟨i, h⟩
    else x)⟩

@[inline] def front (A : COWArray α n.succ) : α × COWArray α n :=
  (A.get ⟨0, Nat.zero_lt_succ _⟩,
  ⟨Array.init (λ i => A.get i.succ)⟩)

@[inline] def back (A : COWArray α n.succ) : COWArray α n × α :=
  (⟨Array.init (λ i => A.get i.embed_succ)⟩,
  A.get ⟨n, Nat.lt_succ_self _⟩)

instance : Foldable (COWArray α n) α where
  fold f acc A := Foldable.fold f acc A.backing

instance [Repr α] : Repr (COWArray α n) := inferInstance

end COWArray