/-
Copyright (c) 2021 James Gallicchio

Authors: James Gallicchio
-/

import LeanColls.Fold
import LeanColls.Indexed


inductive NTree (τ : Type)
| Leaf : Array τ → NTree τ
| Node : Array (NTree τ) → NTree τ


namespace NTree

noncomputable def height : NTree τ → Nat :=
  @NTree.rec τ (λ _ => Nat) (λ _ => Nat) (λ _ => Nat)
    (λ _ => 1)
    (λ _ ih => ih+1)
    (λ _ ih => ih)
    (0)
    (λ _ _ h t => max h t)

def foldUntil (f : α → τ → ContOrDone φ α) (init : α) (t : NTree τ)
  : ContOrDone φ α
  :=match h:t with
    | Leaf x => FoldUntil.foldUntil f init x
    | Node children =>
      have h_children : Array {c : NTree τ // c.height < t.height}
        := Array.map (λ c => ⟨c, by sorry⟩) children
      FoldUntil.foldUntil (λ acc ⟨c,h⟩ => foldUntil f acc c) init h_children
  termination_by _ => height

instance : FoldUntil (NTree r τ) τ := ⟨foldUntil⟩

end NTree
