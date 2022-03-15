import LeanColls.Classes

namespace LeanColls

inductive Range (n : Nat)
| mk' : Range n

namespace Range

def mk (n) : Range n := ⟨⟩

def fold : (Fin n → β → β) → β → Range n → β :=
  let rec @[inline] loop {m α} (f : Fin m → α → α) acc i : α :=
    if h:i < m then
      loop f (f ⟨i,h⟩ acc) (i+1)
    else
      acc
  λ f acc ⟨⟩ => loop f acc 0
  termination_by loop _ _ r => m - r

instance : Foldable (Range n) (Fin n) where
  fold := fold

instance : Membership Nat (Range n) where
  mem i _ := i < n

end Range

end LeanColls