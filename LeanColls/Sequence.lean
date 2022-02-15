import LeanColls.Fold

class Indexed (C : Type u) (τ : outParam (Type v)) :=
  (size : C → Nat)
  (nth : (c : C) → Fin (size c) → τ)


namespace Indexed

instance {C} [S : Indexed C τ] : FoldUntil C τ where
  foldUntil f acc c := FoldUntil.foldUntil
    (λ acc i => f acc (S.nth c i))
    acc
    (⟨[:S.size c],by simp⟩ : {r : Std.Range // 0 < r.step})


end Indexed


namespace Array

instance : Indexed (Array τ) τ := ⟨Array.size, Array.get⟩

end Array
