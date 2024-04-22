/- Copyright (c) 2024 James Gallicchio

Authors: James Gallicchio
-/

import LeanColls.MathlibUpstream
import LeanColls.Classes.Ops

import Mathlib.Data.Finset.Basic

namespace LeanColls.Fold

variable [Fold C τ]

/-- States that `foldM` is equivalent to `fold`. -/
class LawfulFold (C τ) [Fold C τ] : Prop where
  /-- `foldM` is equivalent to doing a fold and binding on each intermediary.

  This is generally not definitionally true.
  Most `foldM` implementations can "early exit" the fold by
  putting the next iteration/recursive call within the continuation to bind. -/
  foldM_eq_fold : [Monad m] → [LawfulMonad m] → ∀ (c : C) (f) (init : β),
    foldM (m := m) c f init = fold c (fun acc x => acc >>= (f · x)) (pure init)
export LawfulFold (foldM_eq_fold)

/-- Correctness of `Fold` with respect to `ToMultiset` -/
class AgreesWithToMultiset (C τ) [Fold C τ] [ToMultiset C τ] : Prop where
  /-- `fold` on `c` corresponds to a `List.foldl` on some list with all the elements in `c`.
    We only require `ToMultiset` because the fold already can occur in any order.

    Note: the list is determined wholly by `c : C`,
    to ensure the order of elements being folded is consistent
    regardless of the fold function/accumulator. -/
  exists_eq_list_foldl : ∀ (c : C),
    ∃ L : List τ, L = toMultiset c ∧
    ∀ {β} (f) (init : β), fold c f init = List.foldl f init L
export AgreesWithToMultiset (exists_eq_list_foldl)

section
variable [ToMultiset C τ] [AgreesWithToMultiset C τ]

theorem exists_eq_list_foldr (c : C)
  : ∃ L : List τ, L = toMultiset c ∧
    ∀ {β} (f) (init : β), fold c f init = List.foldr (Function.swap f) init L
  := by
  have ⟨L,hL,h⟩ := exists_eq_list_foldl c
  use L.reverse
  simp [hL, h]

/-- A strange lemma. Analogous to `bind_pure` chained over the length of `c`. -/
theorem bind_fold_pure [Monad m] [LawfulMonad m] (ma : m α) (c : C) (f : _ → _ → _)
  : ma >>= (fun a => fold c (fun acc t => do let acc ← acc; f acc t) (pure a)) =
    fold c (fun acc t => do let acc ← acc; f acc t) ma := by
  have := exists_eq_list_foldl c
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

theorem multisetInduction
    (c : C) {f acc} {motive : Multiset τ → β → Prop}
    (empty : motive ∅ acc)
    (cons : ∀ {m acc x}, m ⊆ toMultiset c → x ∈ toMultiset c → motive m acc → motive (x ::ₘ m) (f acc x))
  : motive (toMultiset c) (fold c f acc) := by
  have ⟨L,hL,h⟩ := exists_eq_list_foldr c
  rw [h]; clear h
  rw [← hL]
  have : ∀ x ∈ L, x ∈ toMultiset c := by
    intro x hx; rw [← Multiset.mem_coe, hL] at hx
    simpa [Membership.mem_iff_mem_toSet] using hx
  clear hL
  induction L with
  | nil =>
    simp; exact empty
  | cons hd tl ih =>
    simp [Function.swap]; rw [← Multiset.cons_coe]
    apply cons
    · aesop
    · aesop
    · apply ih
      aesop

variable [LawfulFold C τ]

theorem exists_eq_list_foldlM [Monad m] [LawfulMonad m] (c : C)
  : ∃ L : List τ, L = toMultiset c ∧
    ∀ {β} (f) (init : β), foldM (m := m) c f init = List.foldlM f init L
  := by
  have ⟨L,hL,h⟩ := exists_eq_list_foldl c
  use L; refine ⟨hL,?_⟩; clear hL
  intro β f init
  rw [foldM_eq_fold, h, List.foldlM_eq_foldl]

theorem exists_eq_list_foldrM [Monad m] [LawfulMonad m] (c : C)
  : ∃ L : List τ, L = toMultiset c ∧
    ∀ {β} (f) (init : β), foldM (m := m) c f init = List.foldrM (Function.swap f) init L
  := by
  have ⟨L,hL,h⟩ := exists_eq_list_foldr c
  use L; refine ⟨hL,?_⟩; clear hL
  intro β f init
  rw [foldM_eq_fold, h, List.foldrM_eq_foldr]

end


/-! #### Directed Folds -/

def AgreesWithToMultiset.instOfFoldr [ToMultiset C τ] (h : ∀ (c : C),
    ∃ L : List τ, L = toMultiset c ∧
    ∀ {β} (f) (init : β), fold c f init = List.foldr (Function.swap f) init L)
  : AgreesWithToMultiset C τ where
  exists_eq_list_foldl c := by
    have := h c; clear h
    rcases this with ⟨L,h⟩
    use L.reverse
    simp [h]

/-- Types `C` for which `fold` on `c : C` is the same as `foldl` on `toList c`. -/
class AgreesWithToList.Foldl (C τ) [Fold C τ] [ToList C τ] : Prop where
  /-- `fold c` is the same as `List.foldl` over `toList c` -/
  fold_eq_foldl_toList : ∀ (c : C) {β} (f) (init : β),
    fold c f init = List.foldl f init (toList c)
export AgreesWithToList.Foldl (fold_eq_foldl_toList)

instance [ToList C τ] [AgreesWithToList.Foldl C τ] : AgreesWithToMultiset C τ where
  exists_eq_list_foldl c := by
    use toList c
    constructor
    · simp
    · apply fold_eq_foldl_toList

/-- Types `C` for which `fold` on `c : C` is the same as `foldr` on `toList c`. -/
class AgreesWithToList.Foldr (C τ) [Fold C τ] [ToList C τ] : Prop where
  /-- `fold c` is the same as `List.foldr` over `toList c` -/
  fold_eq_foldr_toList : ∀ (c : C) {β} (f) (init : β),
    fold c f init = List.foldr (Function.swap f) init (toList c)
export AgreesWithToList.Foldr (fold_eq_foldr_toList)

instance [ToList C τ] [AgreesWithToList.Foldr C τ] : AgreesWithToMultiset C τ where
  exists_eq_list_foldl c := by
    use (toList c).reverse
    simp
    apply fold_eq_foldr_toList

/-! #### Constructing Fold instances -/

@[inline]
def instMap [Fold C τ] (fc : C' → C) (ft : τ → τ') : Fold C' τ' where
  fold  c h init := Fold.fold  (fc c) (fun acc x => h acc (ft x)) init
  foldM c h init := Fold.foldM (fc c) (fun acc x => h acc (ft x)) init

nonrec def LawfulFold.instMap [F : Fold C τ] [LF : LawfulFold C τ] (fc : C' → C) (ft : τ → τ')
    : @LawfulFold C' τ' (instMap fc ft) :=
  @LawfulFold.mk _ _ (instMap fc ft)
    (by
      intro m β M LM c' g init
      simp [instMap, foldM_eq_fold])

nonrec def AgreesWithToMultiset.instMap [Fold C τ] [ToMultiset C τ] [AgreesWithToMultiset C τ]
        (fc : C' → C) (ft : τ → τ')
    : @AgreesWithToMultiset C' τ' (instMap fc ft) (ToMultiset.instMap fc ft) :=
  @AgreesWithToMultiset.mk _ _ (instMap fc ft) (ToMultiset.instMap fc ft)
      (by
      intro c'
      have ⟨L,hL,hfold⟩ := AgreesWithToMultiset.exists_eq_list_foldl (fc c')
      use L.map ft
      constructor
      · rw [← Multiset.map_coe, hL]; simp [ToMultiset.instMap]
      · intro β g init
        specialize hfold (fun acc x => g acc (ft x)) init
        simp [instMap, hfold, List.foldl_map])



@[inline]
def instProd [Fold C₁ τ₁] [Fold C₂ τ₂] : Fold (C₁ × C₂) (τ₁ × τ₂) where
  fold := fun (c1,c2) f init =>
    init |> fold c1 fun acc x1 =>
      acc |> fold c2 fun acc x2 => f acc (x1,x2)
  foldM := fun (c1,c2) f init =>
    init |> foldM c1 fun acc x1 =>
      acc |> foldM c2 fun acc x2 => f acc (x1,x2)

nonrec def LawfulFold.instProd [Fold C₁ τ₁] [LawfulFold C₁ τ₁] [Fold C₂ τ₂] [LawfulFold C₂ τ₂]
    [ToMultiset C₂ τ₂] [AgreesWithToMultiset C₂ τ₂]
  : @LawfulFold (C₁ × C₂) (τ₁ × τ₂) instProd :=
  @LawfulFold.mk (C₁ × C₂) (τ₁ × τ₂) instProd
    (by
    rintro m β M LM ⟨c1,c2⟩ f acc
    simp [instProd]
    rw [LawfulFold.foldM_eq_fold]
    congr; funext acc x
    conv => lhs; rhs; ext; rw [LawfulFold.foldM_eq_fold]
    rw [bind_fold_pure]
    )

nonrec def AgreesWithToMultiset.instProd
    [Fold C₁ τ₁] [ToMultiset C₁ τ₁] [AgreesWithToMultiset C₁ τ₁]
    [Fold C₂ τ₂] [ToMultiset C₂ τ₂] [AgreesWithToMultiset C₂ τ₂]
  : @AgreesWithToMultiset (C₁ × C₂) (τ₁ × τ₂) instProd .instProd :=
  @AgreesWithToMultiset.mk _ _ instProd .instProd
  (by
    rintro ⟨c1,c2⟩
    have ⟨L1,hL1,h1⟩ := AgreesWithToMultiset.exists_eq_list_foldl c1
    have ⟨L2,hL2,h2⟩ := AgreesWithToMultiset.exists_eq_list_foldl c2
    use L1 ×ˢ L2
    constructor
    · simp [ToMultiset.instProd]; rw [← Multiset.coe_product, hL1, hL2]
    · intro β f init
      simp [instProd, ToMultiset.instProd]
      simp_rw [h1, h2, List.foldl_product])

@[inline]
def instSum [Fold C₁ τ₁] [Fold C₂ τ₂] : Fold (C₁ × C₂) (τ₁ ⊕ τ₂) where
  fold := fun (c1,c2) f init =>
    init
    |> fold c1 (fun acc x => f acc (.inl x))
    |> fold c2 (fun acc x => f acc (.inr x))
  foldM := fun (c1,c2) f acc => do
    let acc ← foldM c1 (fun acc x => f acc (.inl x)) acc
    foldM c2 (fun acc x => f acc (.inr x)) acc

nonrec def LawfulFold.instSum
    [Fold C₁ τ₁] [LawfulFold C₁ τ₁]
    [Fold C₂ τ₂] [LawfulFold C₂ τ₂]
    [ToMultiset C₂ τ₂] [AgreesWithToMultiset C₂ τ₂]
  : @LawfulFold (C₁ × C₂) (τ₁ ⊕ τ₂) instSum :=
  @LawfulFold.mk _ _ instSum
  (by
    rintro m γ _ _ ⟨c1,c2⟩ f init
    simp [instSum, LawfulFold.foldM_eq_fold]
    rw [bind_fold_pure]
  )

nonrec def AgreesWithToMultiset.instSum
    [Fold C₁ τ₁] [ToMultiset C₁ τ₁] [AgreesWithToMultiset C₁ τ₁]
    [Fold C₂ τ₂] [ToMultiset C₂ τ₂] [AgreesWithToMultiset C₂ τ₂]
  : @AgreesWithToMultiset (C₁ × C₂) (τ₁ ⊕ τ₂) instSum .instSum :=
  @AgreesWithToMultiset.mk _ _ instSum .instSum
  (by
    rintro ⟨c1,c2⟩
    have ⟨L1,hL1,h1⟩ := AgreesWithToMultiset.exists_eq_list_foldl c1
    have ⟨L2,hL2,h2⟩ := AgreesWithToMultiset.exists_eq_list_foldl c2
    simp [instSum, ToMultiset.instSum]
    use L1.map Sum.inl ++ L2.map Sum.inr
    constructor
    · rw [← hL1, ← hL2]; simp
    · intro β f init
      rw [h1, h2]
      simp [List.foldl_map])

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

theorem any_iff_exists_toMultiset [LawfulFold C τ]
    [ToMultiset C τ] [AgreesWithToMultiset C τ]
    (f : τ → Bool) (c : C)
  : any f c ↔ (∃ x ∈ toMultiset c, f x) := by
  unfold any
  generalize hf' : (fun _ _ => _) = f'
  suffices foldM c f' () = Except.error () ↔ ∃ x ∈ toMultiset c, f x by
    rw [eq_comm]; split
    · rw [Bool.eq_false_iff]; aesop
    · aesop
  rw [foldM_eq_fold]
  apply multisetInduction (motive := fun m acc => acc = Except.error () ↔ ∃ x ∈ m, f x)
  · simp [pure, Except.pure]
  · intro m acc x _ _ ih
    simp; rw [← ih]; clear ih
    cases acc
    case error =>
      simp [hf'.symm, bind, Except.bind]
    case ok =>
      simp [hf'.symm, bind, Except.bind]

theorem all_iff_exists_toMultiset [LawfulFold C τ]
    [ToMultiset C τ] [AgreesWithToMultiset C τ]
    (f : τ → Bool) (c : C)
  : all f c ↔ (∀ x ∈ toMultiset c, f x) := by
  unfold all
  generalize hf' : (fun _ _ => _) = f'
  suffices foldM c f' () = Except.ok () ↔ ∀ x ∈ toMultiset c, f x by
    rw [eq_comm]; split <;> aesop
  rw [foldM_eq_fold]
  apply multisetInduction (motive := fun m acc => acc = Except.ok () ↔ ∀ x ∈ m, f x)
  · simp [pure, Except.pure]
  · intro m acc x _ _ ih
    simp; rw [← ih]; clear ih
    cases acc
    case error =>
      simp [hf'.symm, bind, Except.bind]
    case ok =>
      simp [hf'.symm, bind, Except.bind]

@[simp]
theorem any_iff_exists [LawfulFold C τ] [Membership τ C]
    [ToMultiset C τ] [AgreesWithToMultiset C τ] [Membership.AgreesWithToSet C τ]
    (f : τ → Bool) (c : C)
  : any f c ↔ ∃ x ∈ c, f x := by
  rw [any_iff_exists_toMultiset]; simp

@[simp]
theorem all_iff_exists [LawfulFold C τ] [Membership τ C]
    [ToMultiset C τ] [AgreesWithToMultiset C τ] [Membership.AgreesWithToSet C τ]
    (f : τ → Bool) (c : C)
  : all f c ↔ ∀ x ∈ c, f x := by
  rw [all_iff_exists_toMultiset]; simp

def instMem : Membership τ C where
  mem x c := open Classical in any (decide <| · = x) c

def instMem.AgreesWithToSet [DecidableEq τ] [LawfulFold C τ]
      [ToMultiset C τ] [AgreesWithToMultiset C τ]
  : @Membership.AgreesWithToSet C τ instMem inferInstance :=
  @Membership.AgreesWithToSet.mk C τ instMem inferInstance
    (by
      intro x c
      simp [instMem]
      rw [any_iff_exists_toMultiset]
      simp [List.any_eq_true, beq_iff_eq, exists_eq_right]
      rfl)

end Fold
