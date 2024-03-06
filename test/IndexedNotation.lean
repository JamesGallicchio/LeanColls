/- Copyright (c) 2023 Tomáš Skřivan.

Authors: Tomáš Skřivan
-/

import LeanColls.Classes.Indexed.Notation

open LeanColls

def NDArray (α : Type) (ι : Type) [IndexType ι] := {a : Array α // a.size = IndexType.card ι}

instance {ι} [IndexType ι] : Indexed (NDArray α ι) ι α where
  mem := sorry
  toMultiset := sorry
  toMultiBagWithIdx := sorry
  fold := sorry
  ofFn := sorry
  get := sorry
  update := sorry

variable (x : NDArray Nat (Fin 10)) (t : NDArray Nat (Fin 10 × Fin 20 × Fin 20))

#check x[1]  -- x[1]

#check t[(1,2,3)] -- x[1,2,3]  -- yes it does not print back t[(1,2,3)]
#check t[1,(2,3)] -- x[1,2,3]  -- yes it does not print back t[1,(2,3)]
#check t[1,2,3]   -- x[1,2,3]

#check_failure t[1,:2,3:4] -- ranges are not yet supported - but syntax is registered

#check show Id Unit from do

  let mut a : NDArray Nat (Fin 10 × Fin 20) := sorry

  for i in IndexType.univ (Fin 10) do
    for j in IndexType.univ (Fin 20) do
      a[i,j] ← (pure 10)
      a[i,j] := 42
      a[i,j] += 42
      a[i,j] -= 42
      a[i,j] *= 42
      a[i,j] /= 42
      a[i,j] •= 42


section IndexNotationElabIssue

variable {Cont Idx Elem} [IndexType Idx] [Indexed Cont Idx Elem] [Inhabited Elem]
example (f : Idx → Elem) :
  Function.invFun (fun (f : Idx → Elem) => Indexed.ofFn (C:=Cont) f)
  =
  -- elaboration of `x[i]` used to cause 'internal exception: isDefEqStuck'
  fun x i => x[i] := sorry

end IndexNotationElabIssue

-- check we didn't mess up Lean's indexing
variable (a : Array Nat) (i j : Fin a.size)

#check a[i]
#check a[:i]
#check a[i:]
#check a[i:j]
