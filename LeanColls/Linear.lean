/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
-/

import LeanColls.Array

namespace LeanColls

structure Vec (α n) where
  data : COWArray α n
deriving Repr

structure Mat (α n m) where
  data : COWArray (Vec α m) n
deriving Repr

namespace Vec

variable {α} [Zero α] [Add α] [Mul α]

def get (a : Vec α n) := a.data.get

def init (f : Fin n → α) : Vec α n := ⟨⟨Array.init f⟩⟩

def add (a b : Vec α n) : Vec α n :=
  init fun i => a.get i + b.get i

def smul (x : α) (a : Vec α n) : Vec α n :=
  init fun i => x * a.get i

instance : Add (Vec α n) where
  add := add

instance : HMul α (Vec α n) (Vec α n) where
  hMul := smul

def innerProd (v1 v2 : Vec α n) : α :=
  (Range.mk n).foldl'
    (fun acc i h => acc + v1.get ⟨i,h⟩ * v2.get ⟨i,h⟩)
    0

instance [Zero α] : Zero (Vec α n) where
  zero := init fun _ => 0

end Vec

namespace Mat

def get (mat : Mat α m n) : Fin m → Vec α n := (mat.data.get ·)

def init (f : Fin m → Vec α n) : Mat α m n := ⟨⟨Array.init f⟩⟩

variable {α} [Zero α] [Add α] [Mul α]

def mulmv (mat : Mat α m n) (vec : Vec α n) : Vec α m :=
  Vec.init fun i => (mat.get i).innerProd vec

def mulvm (vec : Vec α m) (mat : Mat α m n) : Vec α n :=
  (Range.mk m).foldl'
    (fun acc i h => acc + vec.get ⟨i,h⟩ * mat.get ⟨i,h⟩)
    0

def mulmm (a : Mat α l m) (b : Mat α m n) : Mat α l n :=
  init fun i => mulvm (a.get i) b

def id [One α] (n) : Mat α n n :=
  init fun row => Vec.init fun col => if row = col then 1 else 0

nonrec def toString [ToString α] (m : Mat α n m) : String :=
  let strings := Array.init fun i => Array.init fun j => toString (m.get i |>.get j)
  let maxLen := strings |> View.view |>.map (fun i =>
      View.view i |>.map (String.length ·) |> FoldableOps.max |>.getD 0
    ) |> FoldableOps.max |>.getD 0
  let padded := Array.init fun i => Array.init fun j =>
    (strings.get i |>.get j).leftpad maxLen ' '
  Foldable.fold padded (fun acc row =>
    acc ++ Foldable.fold row (fun acc x => acc ++ x ++ "\t") "" ++ "\n"
  ) ""

instance [ToString α] : ToString (Mat α n m) where
  toString := toString

end Mat
