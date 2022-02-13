import LeanColls.Fold
import LeanColls.Queue.BankerQueue
import LeanColls.Queue.LazyBankerQueue

def test1 (iters : Nat) (α) [Q : Queue α Nat] : IO Unit := do
  let mut q := Q.empty

  for i in [:iters] do
    q := Q.enq q i
  
  for i in [:iters] do
    match Q.deq q with
    | none => IO.println "early empty!"
    | some (x,q') =>
      q := q'
      if x ≠ i then
        IO.println "wrong entry!"

def test2 (iters : Nat) (α) [Q : Queue α Nat] : IO Unit := do
  let q := Fold.fold (⟨[:iters],by simp⟩ : {r : Std.Range // r.step > 0}) (λ x i => Q.enq x i) Q.empty

  for i in [:iters] do
    match Q.deq q with
    | none => IO.println "early empty??"
    | some (x,_) =>
      if x ≠ 0 then
        IO.println "wrong entry??"

def time (f : IO Unit) : IO Nat := do
  let pre ← IO.monoMsNow
  f
  let post ← IO.monoMsNow
  pure (post-pre)

def testAll : IO Unit := do
  IO.println "Ephemeral Test"
  let bq  ← time (test1 1000000 (BQueue Nat))
  let lbq ← time (test1 1000000 (LBQueue Nat))
  IO.println s!"BQ:  {bq}ms"
  IO.println s!"LBQ: {lbq}ms"
  IO.println "\nPersistent Test"
  let bq  ← time (test2 10000 (BQueue Nat))
  let lbq ← time (test2 10000 (LBQueue Nat))
  IO.println s!"BQ:  {bq}ms"
  IO.println s!"LBQ: {lbq}ms"
