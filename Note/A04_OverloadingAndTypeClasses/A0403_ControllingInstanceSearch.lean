import Note.A01_GettingToKnowLean.A0106_Polymorpshism
import Note.A04_OverloadingAndTypeClasses.A0401_PositiveNumbers

-- # Controlling Instance Search

def addNatPos : Nat → Pos → Pos
| 0 , p => p
| n + 1, p => .succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
| p, n => addNatPos n p

-- ## Heterogeneous Overloadings

instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

#eval (3 : Pos) + (5 : Nat)
#eval (3 : Nat) + (5 : Pos)

class HPlus' (α : Type) (β : Type) (γ : Type) where
  hPlus : α → β → γ

instance : HPlus' Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus' Pos Nat Pos where
  hPlus := addPosNat

#check_failure HPlus'.hPlus (3 : Pos) (5 : Nat)
#eval (HPlus'.hPlus (3 : Pos) (5 : Nat) : Pos)


-- ## Output Parameters
class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

#eval HPlus.hPlus (3 : Pos) (5 : Nat)


-- ## Default Instances

instance [Add α] : HPlus α α α where
  hPlus := Add.add

#eval HPlus.hPlus (3 : Nat) (5 : Nat)

#check HPlus.hPlus (5 : Nat) (3 : Nat)

#check HPlus.hPlus (5 : Nat)

@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add

#check HPlus.hPlus (5 : Nat)


-- ## Exercises

def PPoint.scalar [Mul α] : PPoint α → α → PPoint α
  | p, a => {x := p.x * a, y := p.y * a}

instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul := PPoint.scalar

#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0
