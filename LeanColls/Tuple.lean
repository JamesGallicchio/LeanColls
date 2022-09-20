/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

@[reducible]
def Tuple (α : Type u) : Nat → Type u
| 0   => PUnit
| 1   => α
| (n+1)+1 => α × Tuple α (Nat.succ n)

namespace Tuple

@[inline]
def toList (t : Tuple α n) : List α :=
  match n, t with
  | 0,   ()     => []
  | 1,   a      => [a]
  | _+2, (a,as) => a :: toList as

@[simp]
theorem length_toList (t : Tuple α n)
  : t.toList.length = n
  := by
  induction n with
  | zero => simp [toList]
  | succ n ih =>
    cases n <;> simp [toList, ih]

@[inline]
def ofList (L : List α) : Tuple α L.length :=
  match L with
  | []        => ()
  | [x]       => x
  | x::y::xs  => (x, ofList (y::xs))

end Tuple

/-! ## List.choose

Returns list of all ways of choosing `n` elements from `L`.
This is equivalent to the list of all `(L[i1], ... L[in])`
for `0 ≤ i1 < i2 < ... < in < L.length`.
-/
def List.chooseSucc : (n : Nat) → List α → List (Tuple α n.succ)
| 0  , L     => L
| _+1, []    => []
| n+1, x::xs =>
  -- Either x is in the tuple,
  (List.chooseSucc n xs |>.map ((x, ·))) ++
  -- or it is not.
  (List.chooseSucc (n+1) xs)

def List.choose (n : Nat) (h_n : n = n.pred.succ := by decide)
  : List α → List (Tuple α n) :=
  h_n ▸ List.chooseSucc n.pred
