import LeanColls

set_option compiler.extract_closed false

def testPanicOnPersist : IO Unit :=
  open LeanColls in do
  /- Some linear usage (all gucci!) -/
  let mut arr := Array.new 73 100
  for i in @Range.mk 100 do
    arr := arr.set i i.val
  let mut sum := 0
  for i in @Range.mk 100 do
    sum := sum + arr.get i
  if sum ≠ 4950 then
    IO.eprintln (s!"Expected sum 4950, got {sum}")
  /- Now we do a not-allowed mutation: -/
  let arrOld := arr
  arr := arr.set 0 20
  if arrOld.get 0 ≠ 20 then
    IO.eprintln (s!"Expected mutation on persistent copies")
  if arr.get 20 ≠ 20 then
    IO.eprintln (s!"Expected value to be set properly")

def benchmarkArrayBuffer : IO Unit := do
  let iters := 100
  for i in List.range 10 do
    let size := 10000 * (2 ^ i)
    let (timeStd, _) ← time (do
      for _ in [0:iters] do
        let mut arr : Array Nat := Array.empty
        for i in [0:size] do
          arr := arr.push i
    )
    let (timeLC, _) ← time (
      open LeanColls in do
      for _ in [0:iters] do
        let mut arr : ArrayBuffer Nat := .empty ()
        for i in [0:size] do
          arr := arr.push i
    )
    IO.println s!"{size}, {timeStd}, {timeLC}"
