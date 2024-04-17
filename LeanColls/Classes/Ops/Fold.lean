/- Copyright (c) 2023 James Gallicchio

Authors: James Gallicchio
-/

import LeanColls.MathlibUpstream
import LeanColls.Classes.Ops

namespace LeanColls.Fold

variable [Fold C τ] [LeanColls.ToList C τ]

/-- Correctness of `Fold` with respect to `ToList` -/
class ToList (C τ) [Fold C τ] [ToList C τ] : Prop where
  fold_eq_fold_toList : ∀ (c : C), ∃ L,
      List.Perm L (toList c) ∧
      ∀ {β} (f) (init : β), fold c f init = List.foldl f init L
  foldM_eq_fold : [Monad m] → [LawfulMonad m] → ∀ (c : C) (f) (init : β),
    foldM (m := m) c f init = fold c (fun acc x => acc >>= (f · x)) (pure init)

variable [ToList C τ]

theorem foldM_eq_foldM_toList [Monad m] [LawfulMonad m] (c : C)
  : ∃ L, List.Perm L (toList c) ∧
    ∀ {β} (f) (init : β), foldM (m := m) c f init = List.foldlM f init L
  := by
  have ⟨L,perm,h⟩ := ToList.fold_eq_fold_toList c
  use L; refine ⟨perm,?_⟩; clear perm
  intro β f init
  rw [ToList.foldM_eq_fold, h, List.foldlM_eq_foldl]

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

def toMem [Fold C τ] : Membership τ C where
  mem x c := open Classical in any (decide <| · = x) c

def toMem.ToList [Fold C τ] [LeanColls.ToList C τ] [ToList C τ]
    : @Mem.ToList C τ toMem inferInstance :=
  @Mem.ToList.mk C τ toMem inferInstance
    (by
      intro x c
      simp [toMem]
      rw [any_eq_any_toList]
      simp [List.any_eq_true, beq_iff_eq, exists_eq_right])

end Fold
