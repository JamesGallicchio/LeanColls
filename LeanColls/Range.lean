import LeanColls.List
import LeanColls.AuxLemmas

namespace LeanColls

structure Range (n : Nat)

namespace Range

def fold_ind {motive : (i : Nat) → i ≤ n → Sort u}
  (zero : motive 0 (Nat.zero_le _))
  (succ : (i : Nat) → (h : i < n) → motive i (Nat.le_of_lt h) → motive i.succ h)
  (r : Range n)
  : motive n (Nat.le_refl _) :=
  let rec @[inline] loop {m} {α : (i : Nat) → i ≤ m → Sort u}
    (f : (i : Nat) → (h : i < m) → α i (Nat.le_of_lt h) → α i.succ h)
    i (h_i : i ≤ m) (acc : α i h_i) : α m (Nat.le_refl _) :=
    if h:i < m then
      loop f i.succ h (f i h acc)
    else
      have : i = m := (Nat.eq_or_lt_of_le h_i).elim (id) (False.elim ∘ h)
      cast (by simp [this]) acc
  loop succ 0 (Nat.zero_le _) zero
  termination_by loop _ _ _i => m - i

def fold : (Fin n → β → β) → β → Range n → β :=
  let rec @[inline] loop {m α} (f : Fin m → α → α) acc i : α :=
    if h:i < m then
      loop f (f ⟨i,h⟩ acc) (i+1)
    else
      acc
  λ f acc ⟨⟩ => loop f acc 0
  termination_by loop _ _ i => m - i

instance : Foldable (Range n) (Fin n) where
  fold := fold
  toIterable := ⟨Nat, λ i =>
    if h:i < n then some ⟨⟨i,h⟩,i.succ⟩ else none, λ _ => 0⟩

def toList : (Range n) → List (Fin n) := Unfoldable.unfold

instance : FoldableOps (Range n) (Fin n) where
  toList := toList
  h_toList := by rfl
  all := _
  h_all := by rfl
  contains _ i := i < n
  h_contains := by sorry

end Range

end LeanColls