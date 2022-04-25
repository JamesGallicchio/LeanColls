import LeanColls.FoldableOps

namespace List

open LeanColls

instance : Foldable (List τ) τ where
  fold := List.foldr
  toIterable := ⟨List τ, List.front?, id⟩

instance [BEq τ] : FoldableOps (List τ) τ := default

instance : Enumerable (List τ) τ where
  ρ := List τ
  fromEnumerator := id
  insert := λ o => match o with
    | none => []
    | some ⟨x,xs⟩ => x::xs

end List