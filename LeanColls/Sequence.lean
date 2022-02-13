import LeanColls.Fold

class Indexed (C : Type u) (τ : outParam (Type v)) :=
  (size : C → Nat)
  (nth : (c : C) → Fin (size c) → τ)


namespace Indexed

instance {C} [S : Indexed C τ] : FoldUntil C τ where
  foldUntil := sorry

end Indexed


namespace Array

instance : Indexed (Array τ) τ := ⟨Array.size, Array.get⟩

end Array
