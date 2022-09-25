/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.AuxLemmas

namespace List

@[specialize]
def foldl' : (l : List τ) → (β → (x : τ) → x ∈ l → β) → β → β
| []   , _, acc => acc
| x::xs, f, acc =>
  have h' : ∀ {x'}, x' ∈ xs → x' ∈ x::xs := List.Mem.tail x
  foldl' xs (λ acc x h => f acc x (h' h)) (f acc x (List.Mem.head _ _))

def foldr' : (l : List τ) → ((x : τ) → x ∈ l → β → β) → β → β
| []   , _, acc => acc
| x::xs, f, acc =>
  have h' : ∀ {x'}, x' ∈ xs → x' ∈ x::xs := List.Mem.tail x
  f x (List.Mem.head _ _) (foldr' xs (λ x h acc => f x (h' h) acc) acc)

theorem foldl_eq_foldl' (c : List τ) (f : β → τ → β) (acc : β)
  : foldl f acc c = foldl' c (λ acc x _ => f acc x) acc
  := by
  induction c generalizing acc with
  | nil => simp [foldl, foldl']
  | cons x xs ih =>
    simp [foldl, foldl']
    apply ih (f acc x)

theorem foldr_eq_foldr' (c : List τ) (f : τ → β → β) (acc : β)
  : foldr f acc c = foldr' c (λ x _ acc => f x acc) acc
  := by
  induction c with
  | nil => simp [foldr, foldr']
  | cons x xs ih =>
    simp [foldr, foldr', ih]

lemma foldl'_eq_subtypeByMemAux_foldl (l : List τ)
  (f : β → (x : τ) → x ∈ l → β) (acc : β)
  (c : List τ) (h : ∀ x, x ∈ c → x ∈ l)
  : foldl' c (fun acc x h' => f acc x (h x h')) acc
    = foldl (fun acc ⟨x,h⟩ => f acc x h) acc (subtypeByMem.aux l c h)
  := by
  induction c generalizing acc with
  | nil =>
    simp [foldl', subtypeByMem.aux, foldl]
  | cons x xs ih =>
    conv =>
      lhs
      simp [foldl']
      rw [ih]

theorem foldl'_eq_subtypeByMem_foldl (l : List τ)
  (f : β → (x : τ) → x ∈ l → β) (acc : β)
  : foldl' l f acc = foldl (fun acc ⟨x,h⟩ => f acc x h) acc l.subtypeByMem
  := by
  apply foldl'_eq_subtypeByMemAux_foldl

lemma foldr'_eq_subtypeByMemAux_foldr (l : List τ)
  (f : (x : τ) → x ∈ l → β → β) (acc : β)
  (c : List τ) (h : ∀ x, x ∈ c → x ∈ l)
  : foldr' c (fun x h' acc => f x (h x h') acc) acc
    = foldr (fun ⟨x,h⟩ acc => f x h acc) acc (subtypeByMem.aux l c h)
  := by
  induction c generalizing acc with
  | nil =>
    simp [foldr', subtypeByMem.aux]
  | cons x xs ih =>
    conv =>
      lhs
      simp [foldr']
      rw [ih]

theorem foldr'_eq_subtypeByMem_foldr (l : List τ)
  (f : (x : τ) → x ∈ l → β → β) (acc : β)
  : foldr' l f acc = foldr (fun ⟨x,h⟩ acc => f x h acc) acc l.subtypeByMem
  := by
  apply foldr'_eq_subtypeByMemAux_foldr

def map' (L : List τ) (f : (x : τ) → x ∈ L → τ') :=
  L.subtypeByMem.map (fun ⟨x,h⟩ => f x h)

@[simp]
theorem length_map' (L : List τ) (f : (x : τ) → x ∈ L → τ')
  : (L.map' f).length = L.length
  := by simp [map']

theorem map_of_subtypeByMem_eq_map' (L : List τ) (f : {x // x ∈ L} → τ')
  : L.subtypeByMem.map f = L.map' (fun x h => f ⟨x,h⟩)
  := by
  rw [map']

theorem foldr_of_map' (L : List τ) (mapf : (x : _) → _ → τ')
  (f) (acc : β)
  : foldr f acc (map' L mapf) = foldr' L (fun x h acc => f (mapf x h) acc) acc
  := by
  simp [foldr'_eq_subtypeByMem_foldr, map', foldr_map]

theorem foldr'_eq_map' (L : List τ) (f : (x : _) → _ → τ')
  : foldr' L (fun x h acc => f x h :: acc) [] = map' L f
  := by
  rw [foldr'_eq_subtypeByMem_foldr]
  rw [map']
  rw [List.foldr_eq_map]

theorem foldl'_eq_map' (L : List τ) (f : (x : _) → _ → τ')
  : foldl' L (fun acc x h => acc ++ [f x h]) [] = map' L f
  := by
  rw [foldl'_eq_subtypeByMem_foldl]
  rw [map']
  rw [List.foldl_eq_map]

def subtypeByMem_rw {L : List τ} (L') (h : L = L')
  : L.subtypeByMem = L'.subtypeByMem.map (fun ⟨x,h'⟩ => ⟨x,h.symm.subst h'⟩)
  := by
  cases h
  conv => lhs; rw [←map_id (subtypeByMem L)] 

def map'_rw {L : List τ} {f : (x : τ) → x ∈ L → τ'} (L' : List τ) (h : L = L')
  : L.map' f = L'.map' (fun x h' => f x (h.symm.subst h'))
  := by
  cases h
  congr

def foldl'_rw (L : List τ) (f : β → (x : τ) → x ∈ L → β) (init) (L' : List τ) (h : L = L')
  : L.foldl' f init = L'.foldl' (fun acc x h' => f acc x (h.symm.subst h')) init
  := by
  cases h
  congr

def foldr'_rw (L : List τ) (f : (x : τ) → x ∈ L → β → β) (init) (L' : List τ) (h : L = L')
  : L.foldr' f init = L'.foldr' (fun x h' acc => f x (h.symm.subst h') acc) init
  := by
  cases h
  congr

lemma subtypeByMemAux_append {L : List τ} {L₁ L₂}
  (h : ∀ x, x ∈ L₁ ++ L₂ → x ∈ L)
  : subtypeByMem.aux L (L₁ ++ L₂) h
    = subtypeByMem.aux L L₁ (fun a ha =>
        h a (List.mem_append_left _ ha))
      ++ subtypeByMem.aux L L₂ (fun a ha =>
        h a (List.mem_append_right _ ha))
  := by
  induction L₁ with
  | nil => simp [subtypeByMem.aux]
  | cons x xs ih =>
    simp [subtypeByMem.aux]
    rw [ih]

lemma subtypeByMemAux_eq_map_subtypeByMem (L₁ L₂ : List τ) (h)
  : subtypeByMem.aux L₁ L₂ h =
    L₂.subtypeByMem.map (fun ⟨x,h'⟩ => ⟨x, h _ h'⟩)
  := by
  simp [subtypeByMem]
  suffices ∀ L hL,
    subtypeByMem.aux L₁ L (fun x h' => h _ (hL _ h'))
    = map _ (subtypeByMem.aux L₂ L hL)
    from this L₂ (by simp)
  intro L h
  induction L with
  | nil => simp [subtypeByMem.aux]
  | cons x xs ih =>
    simp [subtypeByMem.aux]
    rw [ih]

theorem subtypeByMem_append (L₁ L₂ : List τ)
  : subtypeByMem (L₁ ++ L₂) =
    L₁.subtypeByMem.map (fun ⟨x,h⟩ => ⟨x, List.mem_append_left _ h⟩)
    ++ L₂.subtypeByMem.map (fun ⟨x,h⟩ => ⟨x, List.mem_append_right _ h⟩)
  := by
  conv => lhs; simp [subtypeByMem]
  rw [subtypeByMemAux_append]
  simp [subtypeByMemAux_eq_map_subtypeByMem]

theorem mem_of_subtypeByMemAux (L : List τ) (L') (h)
  : ∀ x, x ∈ subtypeByMem.aux L L' h ↔ x.val ∈ L'
  := by
  intro x
  induction L' with
  | nil => cases x; simp [subtypeByMem.aux]
  | cons y ys ih =>
  cases x; case mk v vMem =>
  simp [subtypeByMem.aux]
  rw [ih]

theorem mem_of_subtypeByMem (L : List τ)
  : ∀ x h, ⟨x,h⟩ ∈ subtypeByMem L
  := by
  intro x h
  simp [subtypeByMem]
  rw [mem_of_subtypeByMemAux]
  exact h

theorem mem_of_map' (L : List τ) (f : (x : _) → _ → τ')
  : ∀ x, (h : x ∈ L) → f x h ∈ L.map' f
  := by
  intro x h
  simp [map', subtypeByMem]
  suffices ∀ rest h_rest, x ∈ rest → f x h ∈ map (fun ⟨x,h⟩ => f x h)
                  (subtypeByMem.aux L rest h_rest)
    from this L (by simp) h
  intro rest h_rest h_x
  induction rest with
  | nil => simp at h_x
  | cons y ys ih =>
  cases h_x
  case head =>
    simp [subtypeByMem.aux]
  case tail h_x =>
  simp [subtypeByMem.aux]
  apply Or.inr
  apply ih
  exact h_x

theorem subtypeByMem_map' (L : List τ) (f : (x : τ) → x ∈ L → τ')
  : subtypeByMem (L.map' f) = L.map' (fun x h => ⟨f x h, mem_of_map' _ _ _ h⟩)
  := by
  simp [map', subtypeByMem]
  suffices ∀ rest
    (h_rest : (x : τ) → x ∈ rest → x ∈ L)
    (h_one : (x : τ')
              → x ∈ map (fun ⟨x,h⟩ => f x h) (subtypeByMem.aux L rest h_rest)
              → x ∈ map' L f)
    (h' : (x : τ) → (h : x ∈ L) → _),
    subtypeByMem.aux (map' L f)
      (map (fun ⟨x,h⟩ => f x h) (subtypeByMem.aux L rest h_rest))
      (h_one) =
    map (fun ⟨x,h⟩ => { val := f x h, property := h' x h })
      (subtypeByMem.aux L rest h_rest)
    from this L (by simp)
      (by intro x h; simp [map', h, subtypeByMem])
      (by intro x h; simp [mem_of_map'])
  intro rest h_rest h_one h'
  induction rest with
  | nil => simp [subtypeByMem.aux]
  | cons x xs ih =>
    simp [subtypeByMem.aux, ih]

theorem foldl'_append {β : Type u} (L₁ L₂ : List τ) (f : β → (x : τ) → x ∈ L₁ ++ L₂ → β) (init)
  : foldl' (L₁ ++ L₂) f init =
    foldl' L₂ (fun acc x h => f acc x (List.mem_append_right _ h))
      (foldl' L₁ (fun acc x h => f acc x (List.mem_append_left _ h)) init)
  := by
  rw [foldl'_eq_subtypeByMem_foldl, foldl'_eq_subtypeByMem_foldl, foldl'_eq_subtypeByMem_foldl]
  simp
  rw [subtypeByMem_append]
  simp [foldl_map, foldl_append]

def sum [AddMonoid τ] : List τ → τ
| [] => 0
| x::xs => x + sum xs

theorem get_le_sum (L : List Nat) (i : Nat) (h_i : i < L.length)
  : L.get ⟨i,h_i⟩ ≤ L.sum
  := by
  induction L generalizing i with
  | nil =>
    contradiction
  | cons x xs ih =>
    match i with
    | 0 =>
      simp [get, sum]
      apply Nat.le_add_right
    | i+1 =>
      simp [get, sum]
      rw [←Nat.zero_add (get _ _)]
      apply Nat.add_le_add (Nat.zero_le x)
      apply ih

theorem sum_set (L : List Nat) (i : Nat) (w : Nat) (h_i : i < L.length)
  : sum (L.set i w) = sum L - (L.get ⟨i,h_i⟩) + w
  := by
  induction L generalizing i with
  | nil => contradiction
  | cons x xs ih =>
  match xs, i with
  | [], 0 =>
    simp [set, sum, get]
  | [], _+1 =>
    contradiction
  | y :: z, 0 =>
    simp [set, sum, get]
    rw [Nat.add_comm x, Nat.add_sub_cancel, Nat.add_comm w]
  | y :: z, i+1 =>
    simp [set, sum, get]
    rw [ih]
    generalize h : get _ _ = g
    have : g ≤ y + sum z := by
      rw [←h]
      apply get_le_sum
    clear h ih
    simp [sum]
    rw [Nat.add_sub_assoc this,
        Nat.add_assoc x]
