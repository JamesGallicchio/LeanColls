/-
Copyright (c) 2021 James Gallicchio.

Authors: James Gallicchio, Mario Carneiro
-/

namespace LeanColls

constant UninitPointed.{u} (α : Type u) : NonemptyType.{u}

def Uninit.{u} (α : Type u) : Type u := (UninitPointed α).type

namespace Uninit

instance : Nonempty (Uninit α) := (UninitPointed α).property

unsafe def uninitUnsafe {α} : Uninit α := unsafeCast ()
@[implementedBy uninitUnsafe]
constant uninit {α} : Uninit α

unsafe def initUnsafe (a : α) : Uninit α := unsafeCast a
@[implementedBy initUnsafe]
constant init (a : α) : Uninit α

instance : Inhabited (Uninit α) := ⟨uninit⟩

noncomputable constant getValue? : Uninit α → Option α

def ofOption : Option α → Uninit α
| none => uninit
| some a => init a

axiom getValue_ofOption : ∀ {α} (a : Option α), getValue? (ofOption a) = a
axiom ofOption_getValue : ∀ {α} (a : Uninit α), ofOption (getValue? a) = a

noncomputable def isInit (a : Uninit α) : Bool := Option.isSome (getValue? a)

@[simp]
theorem isInit_init : (init a).isInit := by
  unfold isInit
  rw [(by simp [ofOption] : init a = ofOption (some a))]
  rw [←getValue_ofOption (some a)]
  rw [ofOption_getValue]
  rw [getValue_ofOption]
  simp [Option.isSome]

@[simp]
theorem isInit_uninit : ¬(@uninit α).isInit := by
  unfold isInit
  rw [(by simp [ofOption] : uninit = ofOption (none))]
  rw [←getValue_ofOption (none)]
  rw [ofOption_getValue]
  rw [getValue_ofOption]
  simp [Option.isSome]

unsafe def getValueUnsafe (a : Uninit α) (h : a.isInit) : α := unsafeCast a

@[implementedBy getValueUnsafe]
def getValue (a : Uninit α) (h : a.isInit) : α := by
  unfold isInit at h
  exact
  match getValue? a, h with
  | some a, h => a

end Uninit