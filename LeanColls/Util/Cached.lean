/- Copyright (c) 2023 James Gallicchio

Authors: James Gallicchio
-/

namespace LeanColls.Util

/-- A static expression which is eagerly computed and stored at runtime.
Useful in certain data structures where we want to have pre-computed values. -/
def Cached {α : Type _} (a : α) := { b // b = a }

namespace Cached

instance {a : α} : DecidableEq (Cached a) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ => Decidable.isTrue (by cases hx; cases hy; rfl)

instance {a : α} [Repr α] : Repr (Cached a) where
  reprPrec x := Repr.addAppParen <| "cached " ++ repr x.val

instance {a : α} : Subsingleton (Cached a) :=
  ⟨by intro ⟨x, h⟩; cases h; intro ⟨y, h⟩; cases h; rfl⟩

instance {a : α} : CoeHead (Cached a) α where
  coe x := x.1

def cached (a : α) : Cached a :=
  ⟨a, rfl⟩

def cached' (a : α) (h : a = b) : Cached b :=
  ⟨a, h⟩

instance {a : α} : Inhabited (Cached a) where
  default := cached a

@[simp] theorem cached_val (a : α) (b : Cached a) : (b : α) = a := b.2

end Cached

export Cached (cached)
export Cached (cached')
