/-
Copyright (c) 2022 James Gallicchio.

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

theorem getValue?_init {a : α} : (init a).getValue? = some a := by
  rw [(by simp [ofOption] : init a = ofOption (some a)),
        getValue_ofOption]

theorem getValue?_uninit : (@uninit α).getValue? = none := by
  rw [(by simp [ofOption] : uninit = ofOption none),
        getValue_ofOption]

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
def getValue (a : Uninit α) (h : a.isInit) : α := 
  match getValue? a, (by unfold isInit at h; exact h : Option.isSome (getValue? a)) with
  | some a, h => a
  | none, h => by contradiction

@[simp]
theorem getValue_init {a : α} (h) : (init a).getValue h = a := by
  simp [isInit] at h
  unfold getValue
  generalize h' : getValue? (init a) = x, h = hx
  split
  case h_1 x h =>
    rw [(by simp [ofOption] : init a = ofOption (some a)),
        getValue_ofOption] at h'
    simp at h'
    simp [h']
  case h_2 x h =>
    rw [(by simp [ofOption] : init a = ofOption (some a)),
        getValue_ofOption] at h'
    contradiction

@[simp]
theorem getValue_of_getValue?_some {a : α} (h)
  : getValue? x = some a → x.getValue h = a := by
  intro h_some
  simp [isInit] at h
  unfold getValue
  generalize h' : getValue? x = x', h = hx
  split
  case h_1 x' h =>
    simp [h_some] at h'
    simp [h']
  case h_2 x h =>
    contradiction
