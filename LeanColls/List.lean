import LeanColls.FoldableOps
open LeanColls

namespace List

instance : Foldable (List τ) τ where
  fold := List.foldl

instance : Iterable (List τ) τ where
  ρ := List τ
  step := List.front?
  toIterator := id

instance [BEq τ] : FoldableOps (List τ) τ := default

instance : Enumerable (List τ) τ where
  ρ := List τ
  fromEnumerator := id
  insert := λ
    | none => []
    | some ⟨x,xs⟩ => x::xs
end List

/-! ## Association Lists -/
def AList (κ τ) := List (κ × τ)

namespace AList

instance [DecidableEq κ] : MapLike (AList κ τ) κ τ where
  fold := List.foldl
  get? L k := L.find? (fun (k',_) => k' = k) |>.map Prod.snd

end AList