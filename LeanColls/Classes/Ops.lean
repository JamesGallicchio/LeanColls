/- Copyright (c) 2023 James Gallicchio

Authors: James Gallicchio
-/

import LeanColls.MathlibUpstream

/-! ## Collection operations

This file defines various classes of operations over collections.
- [Fold]: internal iteration
- [Iterate]: external iteration
- [Insert]: empty, insert
- [Size]: some notion of collection size
- [ToFinset]: modeled by finset
- [ToMultiset]: modeled by multiset

TODO: consider adding these?
- [Contains]: decidable membership
- [FilterMap]: conditional map

Related classes which are defined elsewhere but used here:
- [Membership]: Prop-level membership
- [Append]: Disjoint union
- [Functor]: map function
- [Bind]: bind and flatten
- (TODO) whatever the do notation guard class is called

-/

namespace LeanColls

-- TODO: docstrings

/-! ### Models -/

/-- `C` can be modeled as a finset of `τ`s -/
class ToFinset (C : Type u) (τ : outParam (Type v)) where
  toFinset : (cont : C) → Finset τ

/-- `C` can be modeled as a multiset of `τ`s -/
class ToMultiset (C : Type u) (τ : outParam (Type v)) where
  toMultiset : (cont : C) → Multiset τ

class LawfulToMultiset (C : Type u) (τ : outParam (Type v))
        [DecidableEq τ] [ToFinset C τ] [ToMultiset C τ] where
  toFinset_toMultiset : ∀ (cont : C),
    (ToMultiset.toMultiset cont).toFinset = ToFinset.toFinset cont

attribute [simp] LawfulToMultiset.toFinset_toMultiset

instance [DecidableEq τ] [ToMultiset C τ] : ToFinset C τ where
  toFinset c := (ToMultiset.toMultiset c).toFinset

instance [DecidableEq τ] [ToMultiset C τ] : LawfulToMultiset C τ where
  toFinset_toMultiset _ := rfl

class ToList (C : Type u) (τ : outParam (Type v)) where
  toList : (cont : C) → List τ
export ToList (toList)

class LawfulToList (C : Type u) (τ : outParam (Type v))
        [ToMultiset C τ] [ToList C τ] where
  toMultiset_toList : ∀ (cont : C), (toList cont) = ToMultiset.toMultiset cont

attribute [simp] LawfulToMultiset.toFinset_toMultiset

namespace ToList

instance [ToList C τ] : ToMultiset C τ where
  toMultiset c := (toList c)

instance [ToList C τ] : LawfulToList C τ where
  toMultiset_toList _ := rfl

def prod [ToList C₁ τ₁] [ToList C₂ τ₂] : ToList (C₁ × C₂) (τ₁ × τ₂) where
  toList := fun (c1,c2) => toList c1 ×ˢ toList c2

def sum [ToList C₁ τ₁] [ToList C₂ τ₂] : ToList (C₁ × C₂) (τ₁ ⊕ τ₂) where
  toList := fun (c1,c2) =>
    (toList c1).map Sum.inl ++ (toList c2).map Sum.inr

end ToList


/-! ### Operations Defined Elsewhere -/

namespace Mem
variable (C : Type u) (τ : outParam (Type v)) [Membership τ C]

class ToFinset [ToFinset C τ] : Prop where
  mem_iff_mem_toFinset : ∀ x (cont : C),
    x ∈ cont ↔ x ∈ ToFinset.toFinset cont

class ToMultiset [ToMultiset C τ] : Prop where
  mem_iff_mem_toMultiset : ∀ x (cont : C),
    x ∈ cont ↔ x ∈ ToMultiset.toMultiset cont

class ToList [ToList C τ] : Prop where
  mem_iff_mem_toList : ∀ x (cont : C),
    x ∈ cont ↔ x ∈ ToList.toList cont

end Mem

namespace Append
variable (C : Type u) (τ : outParam (Type v)) [Append C]

class ToList [ToList C τ] : Prop where
  toList_append : ∀ (c1 c2 : C),
    toList (c1 ++ c2) = toList c1 ++ toList c2

attribute [simp] ToList.toList_append

end Append

export Functor (map)

namespace Functor
variable (C : Type u → Type v) [Functor C] (τ τ')

class ToList [ToList (C τ) τ] [ToList (C τ') τ'] : Prop where
  toList_map : ∀ (c : C τ) (f : τ → τ'),
    toList (Functor.map f c) = Functor.map f (toList c)

attribute [simp] ToList.toList_map

end Functor


/-! ### Iteration -/

/-- `C` can be folded over, with element type `τ` -/
class Fold (C : Type u) (τ : outParam (Type v)) where
  /-- full (not early-terminating) fold over the elements of `C` -/
  fold : {β : Type w} → (cont : C) → (β → τ → β) → β → β
  /-- monadic fold over the elements of `C` -/
  foldM : {β : Type w} → {m : Type w → Type w} → [Monad m] →
      (cont : C) → (β → τ → m β) → β → m β
    := fun c f i => fold c (fun macc x => macc >>= fun acc => f acc x) (pure i)
export Fold (fold foldM)

namespace Fold

variable [Fold C τ] [LeanColls.ToList C τ]

/-- Correctness of `Fold` with respect to `ToList` -/
class ToList (C τ) [Fold C τ] [ToList C τ] : Prop where
  fold_eq_fold_toList : ∀ (c : C), ∃ L,
      List.Perm L (toList c) ∧
      ∀ {β} (f) (init : β), fold c f init = List.foldl f init L
  foldM_eq_fold : [Monad m] → [LawfulMonad m] → ∀ (c : C) (f) (init : β),
    foldM (m := m) c f init = fold c (fun acc x => acc >>= (f · x)) (pure init)

/-- A strange lemma. Analogous to `bind_pure` chained over the length of `c`. -/
theorem bind_fold_pure [ToList C τ] [Monad m] [LawfulMonad m] (ma : m α) (c : C) (f : _ → _ → _)
  : ma >>= (fun a => fold c (fun acc t => do let acc ← acc; f acc t) (pure a)) =
    fold c (fun acc t => do let acc ← acc; f acc t) ma := by
  have := ToList.fold_eq_fold_toList c
  rcases this with ⟨L,-,h⟩
  simp [h]; clear h
  rw [← List.foldr_reverse]
  conv => lhs; arg 2; ext; rw [← List.foldr_reverse]
  generalize L.reverse = L
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp; rw [← ih]
    simp

@[inline]
def map [Fold C τ] (fc : C' → C) (ft : τ → τ') : Fold C' τ' where
  fold  c h init := Fold.fold  (fc c) (fun acc x => h acc (ft x)) init
  foldM c h init := Fold.foldM (fc c) (fun acc x => h acc (ft x)) init

def map.ToList [F : Fold C τ] [LeanColls.ToList C τ] [ToList C τ]
              [L : LeanColls.ToList C' τ'] (fc : C' → C) (ft : τ → τ')
              (h : ∀ c', toList c' = List.map ft (toList (fc c')))
    : @ToList C' τ' (map fc ft) L :=
  @ToList.mk _ _ (map fc ft) L
    (by
      intro c'
      have ⟨L,hL,hfold⟩ := ToList.fold_eq_fold_toList (fc c')
      use L.map ft
      constructor
      · rw [h]; apply List.Perm.map; apply hL
      intro β g init
      specialize hfold (fun acc x => g acc (ft x)) init
      simp [map, hfold, List.foldl_map])
    (by
      intro m β M LM c' g init
      simp [map, ToList.foldM_eq_fold])

@[inline]
def prod [Fold C₁ τ₁] [Fold C₂ τ₂] : Fold (C₁ × C₂) (τ₁ × τ₂) where
  fold := fun (c1,c2) f init =>
    init |> fold c1 fun acc x1 =>
      acc |> fold c2 fun acc x2 => f acc (x1,x2)
  foldM := fun (c1,c2) f init =>
    init |> foldM c1 fun acc x1 =>
      acc |> foldM c2 fun acc x2 => f acc (x1,x2)

def prod.ToList [Fold C₁ τ₁] [L₁ : LeanColls.ToList C₁ τ₁] [Fold.ToList C₁ τ₁]
                [Fold C₂ τ₂] [L₂ : LeanColls.ToList C₂ τ₂] [Fold.ToList C₂ τ₂]
  : @ToList (C₁ × C₂) (τ₁ × τ₂) prod .prod :=
  @ToList.mk _ _ prod .prod
  (by
    rintro ⟨c1,c2⟩
    have ⟨L1,hL1,h1⟩ := Fold.ToList.fold_eq_fold_toList c1
    have ⟨L2,hL2,h2⟩ := Fold.ToList.fold_eq_fold_toList c2
    use L1 ×ˢ L2
    constructor
    · simp [ToList.prod]; apply List.Perm.product hL1 hL2
    intro β f init
    simp [prod, ToList.prod]
    simp_rw [h1, h2, List.foldl_product])
  (by
    rintro m γ _ _ ⟨c1,c2⟩ f init
    simp [prod, ToList.foldM_eq_fold]
    congr
    funext acc x
    rw [bind_fold_pure]
  )

@[inline]
def sum [Fold C₁ τ₁] [Fold C₂ τ₂] : Fold (C₁ × C₂) (τ₁ ⊕ τ₂) where
  fold := fun (c1,c2) f init =>
    init
    |> fold c1 (fun acc x => f acc (.inl x))
    |> fold c2 (fun acc x => f acc (.inr x))
  foldM := fun (c1,c2) f acc => do
    let acc ← foldM c1 (fun acc x => f acc (.inl x)) acc
    foldM c2 (fun acc x => f acc (.inr x)) acc

def sum.ToList [Fold C₁ τ₁] [L₁ : LeanColls.ToList C₁ τ₁] [Fold.ToList C₁ τ₁]
                [Fold C₂ τ₂] [L₂ : LeanColls.ToList C₂ τ₂] [Fold.ToList C₂ τ₂]
  : @ToList (C₁ × C₂) (τ₁ ⊕ τ₂) sum .sum :=
  @ToList.mk _ _ sum .sum
  (by
    rintro ⟨c1,c2⟩
    have ⟨L1,hL1,h1⟩ := Fold.ToList.fold_eq_fold_toList c1
    have ⟨L2,hL2,h2⟩ := Fold.ToList.fold_eq_fold_toList c2
    simp [ToList.sum, sum]
    use L1.map Sum.inl ++ L2.map Sum.inr
    constructor
    · apply List.Perm.append <;> (apply List.Perm.map; assumption)
    intro β f init
    rw [h1, h2]
    simp [List.foldl_map])
  (by
    rintro m γ _ _ ⟨c1,c2⟩ f init
    simp [sum, ToList.foldM_eq_fold]
    rw [bind_fold_pure]
  )

instance : ForIn m C τ where
  forIn := fun {β} _ c acc f => do
    let res ← Fold.foldM (m := ExceptT β m)
      c (fun x acc =>
        f acc x >>= fun
          | .done a => throw a
          | .yield a => pure a) acc
    match res with
    | .ok a => pure a
    | .error a => pure a

def find (f : τ → Bool) (cont : C) : Option τ :=
  match
    Fold.foldM cont (fun () x =>
      if f x then .error x else .ok ()
    ) ()
  with
  | Except.ok () => none
  | Except.error x => some x

def any (f : τ → Bool) (cont : C) : Bool :=
  match
    Fold.foldM cont (fun () x =>
      if f x then .error () else .ok ()
    ) ()
  with
  | Except.ok () => false
  | Except.error () => true

def all (f : τ → Bool) (cont : C) : Bool :=
  match
    Fold.foldM cont (fun () x =>
      if f x then .ok () else .error ()
    ) ()
  with
  | Except.ok () => true
  | Except.error () => false

theorem any_eq_any_toList [LeanColls.ToList C τ] [ToList C τ]
    (f : τ → Bool) (c : C)
  : any f c = List.any (toList c) f := by
  unfold any
  generalize hf' : (fun _ _ => _) = f'
  suffices foldM c f' () = Except.error () ↔ List.any (toList c) f by
    rw [eq_comm]; split
    · rw [Bool.eq_false_iff]; aesop
    · aesop
  rw [ToList.foldM_eq_fold]
  have ⟨L,perm,h⟩ := ToList.fold_eq_fold_toList c
  rw [h]; clear h
  simp_rw [List.any_eq_true, ← perm.mem_iff]; clear perm c
  subst hf'
  rw [← List.foldlM_eq_foldl]
  induction L with
  | nil => simp_all [pure, Except.pure]
  | cons hd tl ih =>
    simp [bind, Except.bind]
    by_cases f hd = true <;> simp_all

theorem all_eq_all_toList [LeanColls.ToList C τ] [ToList C τ]
    (f : τ → Bool) (c : C)
  : all f c = List.all (toList c) f := by
  unfold all
  generalize hf' : (fun _ _ => _) = f'
  suffices foldM c f' () = Except.ok () ↔ List.all (toList c) f by
    rw [eq_comm]; split
    · aesop
    · rw [Bool.eq_false_iff]; aesop
  rw [ToList.foldM_eq_fold]
  have ⟨L,perm,h⟩ := ToList.fold_eq_fold_toList c
  rw [h]; clear h
  simp_rw [List.all_eq_true, ← perm.mem_iff]; clear perm c
  subst hf'
  rw [← List.foldlM_eq_foldl]
  induction L with
  | nil => simp_all [pure, Except.pure]
  | cons hd tl ih =>
    simp [bind, Except.bind]
    by_cases f hd = true <;> simp_all

@[simp]
theorem any_iff_exists [Membership τ C] [LeanColls.ToList C τ] [ToList C τ] [Mem.ToList C τ]
    (f : τ → Bool) (c : C)
  : any f c ↔ ∃ x ∈ c, f x := by
  rw [any_eq_any_toList]
  simp [Mem.ToList.mem_iff_mem_toList]

@[simp]
theorem all_iff_exists [Membership τ C] [LeanColls.ToList C τ] [ToList C τ] [Mem.ToList C τ]
    (f : τ → Bool) (c : C)
  : all f c ↔ ∀ x ∈ c, f x := by
  rw [all_eq_all_toList]
  simp [Mem.ToList.mem_iff_mem_toList]

instance (priority := low) [Fold C τ] [BEq τ] : Membership τ C where
  mem x c := any (· == x) c

instance [Fold C τ] [BEq τ] [LeanColls.ToList C τ]
    [ToList C τ] [LawfulBEq τ] : Mem.ToList C τ where
  mem_iff_mem_toList := by
    intro x c
    conv => lhs; simp [Membership.mem]
    rw [any_eq_any_toList]
    simp only [List.any_eq_true, beq_iff_eq, exists_eq_right]

end Fold


/-- `C` with element type `τ` can be iterated using type `ρ`

**Note:** This is essentially a combination of Lean core's
[ToStream] and [Stream] classes.
By combining them we can avoid relying on distinct `ρ` types
to associate the `next?` and `iterate` functions.
-/
class Iterate (C : Type u) (τ : outParam (Type v)) (ρ : outParam (Type w)) where
  iterate : (cont : C) → ρ
  next? : ρ → Option (τ × ρ)
export Iterate (iterate next?)


/-! ### New Operations -/

/-- `C` has an empty collection, and a way to insert `τ`s -/
class Insert (C : Type u) (τ : outParam (Type v)) where
  empty : C
  insert : (cont : C) → τ → C
  singleton : τ → C := insert empty
export Insert (empty insert singleton)

namespace Insert

instance [_root_.Insert τ C] [EmptyCollection C] : Insert C τ where
  empty := EmptyCollection.emptyCollection
  insert c x := _root_.Insert.insert x c

variable  (C : Type u) (τ : outParam (Type v)) [Insert C τ]

class Mem [Membership τ C] : Prop where
  mem_empty : ∀ x, ¬ x ∈ empty (C := C)
  mem_insert : ∀ x (cont : C) y, x ∈ insert cont y ↔ x = y ∨ x ∈ cont
  mem_singleton : ∀ x y, x ∈ singleton (C := C) y ↔ x = y

class ToMultiset [ToMultiset C τ] : Prop where
  toMultiset_empty : ToMultiset.toMultiset (empty (C := C)) = {}
  toMultiset_insert : ∀ (cont : C) x,
    ToMultiset.toMultiset (insert cont x) = Multiset.cons x (ToMultiset.toMultiset cont)
  toMultiset_singleton : ∀ x,
    ToMultiset.toMultiset (singleton (C := C) x) = {x}

instance [Membership τ C] [LeanColls.ToMultiset C τ] [ToMultiset C τ] [Mem.ToMultiset C τ] : Mem C τ where
  mem_empty := by
    intro x
    simp [Mem.ToMultiset.mem_iff_mem_toMultiset, ToMultiset.toMultiset_empty]
  mem_insert := by
    intro x c y
    simp [Mem.ToMultiset.mem_iff_mem_toMultiset, ToMultiset.toMultiset_insert]
  mem_singleton := by
    intro x
    simp [Mem.ToMultiset.mem_iff_mem_toMultiset, ToMultiset.toMultiset_singleton]

@[simp] theorem toList_empty [Membership τ C] [Mem C τ] [ToList C τ] [Mem.ToList C τ]
  : toList (empty (C := C)) = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro x
  rw [← Mem.ToList.mem_iff_mem_toList]
  apply Mem.mem_empty

@[simp] theorem toList_singleton [ToList C τ] [LeanColls.ToMultiset C τ] [LawfulToList C τ] [ToMultiset C τ]
  : toList (singleton (C := C) x) = [x] := by
  apply Multiset.coe_eq_singleton.mp
  rw [LawfulToList.toMultiset_toList]
  rw [ToMultiset.toMultiset_singleton]

end Insert


class Size (C : Type u) where
  /-- Number of elements in the collection. -/
  size : (cont : C) → Nat
export Size (size)

instance (priority := low) Size.ofFold [Fold C τ] : Size C where
  size c := Fold.fold c (fun acc _x => acc+1) 0
