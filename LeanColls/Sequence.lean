import LeanColls.Iterable

class Sequence (C : Type) :=
  (τ : Type)
  (size : C → Nat)
  (nth : (c : C) → Fin (size c) → τ)


namespace Sequence

instance {C} [S : Sequence C] : Iterable C :=
  {τ := S.τ, fold_until := sorry}

end Sequence


namespace Array

instance {τ} : Sequence (Array τ) :=
  {τ, size := Array.size, nth := Array.get}

end Array
