/-
Copyright (c) 2021 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Fold

class Indexed (C : Type u) (τ : outParam (Type v)) :=
  (size : C → Nat)
  (nth : (c : C) → Fin (size c) → τ)


namespace Indexed



instance [S : Indexed C τ] [Monad m] : FoldUntil C τ where
  foldUntil f acc c := sorry

end Indexed


namespace Array

instance : Indexed (Array τ) τ := ⟨Array.size, Array.get⟩

end Array
