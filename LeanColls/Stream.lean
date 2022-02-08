import LeanColls.Iterable

def take [S : Stream ρ τ] (s : ρ) : Nat → List τ × ρ
| 0 => ([], s)
| n+1 =>
  match S.next? s with
  | none => ([], s)
  | some (x,rest) =>
    let (L,rest) := take rest n
    (x::L, rest)

def isEmpty [S : Stream ρ τ] (s : ρ) : Bool :=
  Option.isNone (S.next? s)

def isFinite [S : Stream ρ τ] (l : ρ) : Prop :=
  ∃ n, isEmpty (take l n).2

def foldUntil f acc init := _

instance [S : Stream ρ τ] : FoldUntil {s : ρ // isFinite s} τ where
