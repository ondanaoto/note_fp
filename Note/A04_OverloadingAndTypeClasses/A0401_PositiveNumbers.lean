-- # Positive Numbers

inductive Pos : Type
  | one : Pos
  | succ : Pos → Pos

-- def seven : Pos := 7

def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))

-- def fourteen : Pos := seven + seven
-- def fortyNine : Pos := seven * seven

-- ## Classes and Instances

#eval 5 + 3

class Plus (α : Type) where
  plus : α → α → α

instance : Plus Nat where
  plus := Nat.add

#eval Plus.plus 5 3

open Plus (plus)

#eval plus 5 3

def Pos.plus : Pos → Pos → Pos
  | .one , k => .succ k
  | .succ n, k => .succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

def fourteen' := plus seven seven

-- #eval plus 5.2 917.25861


-- ## Overloaded Addition

instance : Add Pos where
  add := Pos.plus

def fourteen : Pos := seven + seven


-- ## Conversion to Strings

def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | .one => "Pos.one"
  | .succ n => paren s!"Pos.succ {posToString false n}"

instance : ToString Pos where
  toString := posToString true

#eval s!"There are {seven}"

def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

instance : ToString Pos where
  toString x := toString (x.toNat)

#eval s!"There are {seven}"

-- ## Overloaded Multiplication

def Pos.mul : Pos → Pos → Pos
  | .one, k => k
  | .succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul

#eval [seven * Pos.one,
       seven * seven,
       Pos.succ Pos.one * seven]

-- ## Literal Numbers

#check OfNat

inductive LT4 where
  | zero
  | one
  | two
  | three
deriving Repr

instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three

#eval (3 : LT4)
#eval (0 : LT4)
-- #eval (4 : LT4)

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

def eight : Pos := 8
-- def zero : Pos := 0


-- ## Exercises
-- ### Another Representation

structure Pos' where
  succ ::
  pred : Nat

def four := Pos'.succ 3
def five := Pos'.succ 4

def Pos'.toString : Pos' → String
  | .succ k => s!"Pos'.succ {k}"

instance : ToString Pos' where
  toString := Pos'.toString

#eval four
#eval five

def Pos'.add : Pos' → Pos' → Pos'
  |.succ k, .succ n => .succ (k + n + 1)

instance : Add Pos' where
  add := Pos'.add

#eval four + five

def Pos'.mul : Pos' → Pos' → Pos'
  | .succ k, .succ n => .succ (k * n + k + n)

instance : Mul Pos' where
  mul := Pos'.mul

#eval four * five

instance : OfNat Pos' (n + 1) where
  ofNat :=
    let rec natPlusOne' : Nat → Pos'
      | .zero => .succ 0
      | .succ k => .succ (k + 1)
    natPlusOne' n

#eval (3 : Pos')
#eval 3 * four

-- ### Even Numbers

inductive Even where
| zero : Even
| sucsuc : Even → Even

def two := Even.sucsuc .zero
def six := Even.sucsuc (.sucsuc two)

def Even.toNat : Even → Nat
| .zero => .zero
| .sucsuc n => .succ (.succ (n.toNat))

instance : ToString Even where
  toString e := toString (Even.toNat e)

#eval two
#eval six

def Even.add : Even → Even → Even
| .zero, k => k
| .sucsuc n, k => .sucsuc (n.add k)

instance : Add Even where
  add := Even.add

#eval two + six

def Even.mul : Even → Even → Even
| .zero, _ => .zero
| .sucsuc n, k => k + k + n.mul k

instance : Mul Even where
  mul := Even.mul

#eval six * two

-- ### HTTP Requests
