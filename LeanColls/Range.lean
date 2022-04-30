import LeanColls.List
import LeanColls.AuxLemmas

namespace LeanColls

structure Range (n : Nat)

namespace Range

def fold : (Fin n → β → β) → β → Range n → β :=
  let rec @[inline] loop {m α} (f : Fin m → α → α) acc i : α :=
    if h:i < m then
      loop f (f ⟨i,h⟩ acc) (i+1)
    else
      acc
  λ f acc ⟨⟩ => loop f acc 0
  termination_by loop _ _ i => m - i

theorem fold_ind {f : Fin n → β → β} {acc : β} {motive : Nat → β → Prop}
  (init : motive 0 acc)
  (step : ∀ i acc, (h : i < n) → motive i acc → motive i.succ (f ⟨i,h⟩ acc))
  : motive n (fold f acc ⟨⟩)
  :=
  let rec loop i (acc : β) (h_i : i ≤ n) (h_acc : motive i acc)
    : motive n (fold.loop f acc i) :=
    if h:i < n then by
      unfold fold.loop
      simp [h]
      exact loop i.succ (f ⟨i,h⟩ acc) h (step i acc h h_acc)
    else by
      have : i = n := (Nat.eq_or_lt_of_le h_i).elim (id) (False.elim ∘ h)
      unfold fold.loop
      simp [h]
      rw [this] at h_acc
      exact h_acc
  loop 0 acc (Nat.zero_le _) init
  termination_by loop _ _ _i => n - i


instance : Foldable (Range n) (Fin n) where
  fold := fold

instance : Iterable (Range n) (Fin n) where
  ρ := Nat
  step := λ i => if h:i < n then some ⟨⟨i,h⟩,i.succ⟩ else none
  toIterator := λ _ => 0

def toList (r : Range n) : List (Fin n) := Unfoldable.unfold r

instance : FoldableOps (Range n) (Fin n) where
  toList := toList
  h_toList := by sorry
  all := _
  h_all := by rfl
  contains _ i := i < n
  h_contains := by sorry

end Range

end LeanColls