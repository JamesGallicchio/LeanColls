import LeanColls.FoldableOps

namespace List

open LeanColls

instance : Foldable (List τ) τ where
  fold f := List.foldl (λ x y => f y x)
  toIterable := ⟨List τ, List.front?, id⟩

instance [BEq τ] : FoldableOps (List τ) τ := default

instance : Enumerable (List τ) τ where
  ρ := List τ
  fromEnumerator := id
  insert := λ
    | none => []
    | some ⟨x,xs⟩ => x::xs

end List