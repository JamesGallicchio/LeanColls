import LeanColls.AuxLemmas

namespace List

def fold {β} (c : List τ) (f a) := @List.foldl β _ f a c

@[specialize, inline]
def fold' : (l : List τ) → (β → (x : τ) → x ∈ l → β) → β → β :=
  let rec @[specialize,inline] go
    (l : List τ) (f : β → (x : τ) → x ∈ l → β) (acc : β)
    (rest : List τ) (h : ∀ x, x ∈ rest → x ∈ l) : β :=
    match rest with
    | [] => acc
    | x::xs => go l f (f acc x (h x (List.Mem.head _ _))) xs
      (by intros x hxs; exact h _ (List.Mem.tail _ hxs))
  λ l f acc => go l f acc l (by intros; trivial)

theorem fold_eq_fold' (c : List τ) (f : β → τ → β) (acc : β)
  : fold c f acc = fold' c (λ acc x _ => f acc x) acc
  := by
  simp [fold, fold']
  suffices ∀ l h, foldl f acc l = fold'.go c (fun acc x x_1 => f acc x) acc l h from
    this c _
  intro l h
  induction l generalizing acc with
  | nil =>
    simp [foldl, fold'.go]
  | cons x xs ih =>
    simp [foldl, fold'.go]
    apply ih (f acc x)

def map' (L : List τ) (f : (x : τ) → x ∈ L → τ') :=
  L.subtypeByMem.map (fun ⟨x,h⟩ => f x h)

def rw_map' {L1 L2 : List τ} (h_L : L1 = L2) (f : (x : τ) → x ∈ L1 → τ')
  : L1.map' f = L2.map' (fun x h => f x (h_L.substr h))
  := by cases h_L; rfl

def fold'_append_singleton_eq_map' (L : List τ) (f : (x : τ) → x ∈ L → τ')
  : L.fold' (fun acc x h => acc ++ [f x h]) []
    = L.map' (fun x h => f x h)
  := by
  simp [fold', subtypeByMem]
  suffices ∀ acc rem h, fold'.go L (fun acc x h => acc ++ [f x h]) acc rem h
    = acc ++ map _ (subtypeByMem.aux L rem h)
    by apply this
  intro acc rem h
  induction rem generalizing acc with
  | nil =>
    simp [fold'.go]
  | cons x xs ih =>
    simp [fold'.go]
    conv =>
      rhs
      rw [append_cons]
    apply ih

theorem fold'_cons_eq_map'_reverse (L : List τ) (f : (x : τ) → x ∈ L → τ')
  : List.fold' L (λ acc x h => (f x h) :: acc) []
    = (L.map' (fun x h => f x h)
      |>.reverse)
  := by
  simp [fold', map', subtypeByMem]
  rw [map_eq_mapTR]
  simp [mapTR]
  suffices ∀ acc rem h, fold'.go L (fun acc x h => (f x h) :: acc) acc rem h
    = reverse (mapTRAux _ (subtypeByMem.aux L rem h) acc)
    by apply this
  intro acc rem h
  induction rem generalizing acc with
  | nil =>
    simp [fold'.go, subtypeByMem.aux, mapTRAux]
  | cons x xs ih =>
    simp [fold'.go, subtypeByMem.aux, mapTRAux]
    apply ih

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
