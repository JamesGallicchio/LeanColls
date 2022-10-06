
@[extern "leancolls_hole_initialize"]
private opaque holeInit : IO Unit

builtin_initialize holeInit

opaque Hole.Pointed (α : Type u) (β : Type v) : NonemptyType.{max u v}
def Hole (α β) := (Hole.Pointed α β).type

namespace Hole

instance : Nonempty (Hole α β) := (Hole.Pointed α β).property

@[extern "leancolls_hole_mk"]
opaque hole : Unit → Hole α α

@[extern "leancolls_hole_fill"]
axiom fill {α β} : Hole α β → α → β

@[extern "leancolls_hole_cons"]
opaque cons : Hole (List α) (List α) → α → Hole (List α) (List α)
