/-
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio, Mario Carneiro
-/

namespace LeanColls

opaque UninitPointed.{u} (α : Type u) : NonemptyType.{u}

def Uninit.{u} (α : Type u) : Type u := (UninitPointed α).type

namespace Uninit

instance : Nonempty (Uninit α) := (UninitPointed α).property

noncomputable opaque uninit {α} : Uninit α

unsafe def initUnsafe (a : α) : Uninit α := unsafeCast a
@[implemented_by initUnsafe]
opaque init (a : α) : Uninit α

noncomputable opaque getValue? : Uninit α → Option α

noncomputable def ofOption : Option α → Uninit α
| none => uninit
| some a => init a

axiom getValue_ofOption : ∀ {α} (a : Option α), getValue? (ofOption a) = a
axiom ofOption_getValue : ∀ {α} (a : Uninit α), ofOption (getValue? a) = a

@[simp]
theorem getValue?_init {a : α} : (init a).getValue? = some a := by
  rw [(by simp [ofOption] : init a = ofOption (some a)),
        getValue_ofOption]

@[simp]
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

unsafe def getValueUnsafe (a : Uninit α) (_ : a.isInit) : α := unsafeCast a

@[implemented_by getValueUnsafe]
def getValue (a : Uninit α) (h : a.isInit) : α := 
  match getValue? a, (by unfold isInit at h; exact h : Option.isSome (getValue? a)) with
  | some a, _ => a
  | none, h => by contradiction

@[simp]
theorem getValue_init {a : α} (h) : (init a).getValue h = a := by
  unfold getValue
  split
  case h_1 h _ =>
    simp at h
    rw [h]
  case h_2 h _ =>
    simp at h

theorem getValue_of_eq_init {a : α} {u h} (h' : u = Uninit.init a)
  : u.getValue h = a
  := by cases h'; simp

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
