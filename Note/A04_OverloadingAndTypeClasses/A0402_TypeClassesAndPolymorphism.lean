import Note.A04_OverloadingAndTypeClasses.A0401_PositiveNumbers
import Note.A01_GettingToKnowLean.A0106_Polymorpshism

-- # Type Classes and Polymorphism
-- ## Checking Polymorphic Function's Types


#check (IO.println)

#check @IO.println

-- ## Defining Polymorphic Functions with Instance Implicits

def List.sum [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x + xs.sum

def fourNats : List Nat := [1, 2, 3, 4]
#eval fourNats.sum

def fourPos : List Pos := [1, 2, 3, 4]

-- #eval fourPos.sum

#check PPoint

instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }

-- ## Methods and Implicit Arguments

#check @OfNat.ofNat
#check @Add.add

-- ## Exercises

-- ### Even Number Literals

instance : OfNat Even .zero where
  ofNat := .zero

instance [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := Even.sucsuc (OfNat.ofNat n)

-- ### Recursive Instance Search Depth
-- 128 times!
#eval (254: Even)
-- #eval (256: Even)
