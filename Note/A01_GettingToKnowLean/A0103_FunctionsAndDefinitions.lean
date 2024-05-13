-- # Functions and Definitions

def hello := "Hello"

def lean : String := "Lean"

#eval String.append hello (String.append " " lean)


-- ## Defining Functions

def add1 (n : Nat) : Nat := n + 1

#eval add1 7

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else
    n

#eval maximum (5 + 8) (2 * 7)

#check add1
#check (add1)

#check maximum
#check (maximum)

#check maximum 3
#check String.append "Hello "

-- ### exercises
def joinStringWith (s₀ s₁ s₂ : String) : String :=
  String.append s₁ (String.append s₀ s₂)

#eval joinStringWith ", " "one" "and another"

#check joinStringWith ": "

def volume (h w d : Nat) : Nat := h * w * d


-- ## Defining Types

def Str : Type := String

def aStr : Str := "This is a string."

#check aStr


-- ### Messages You May Meet

def NaturalNumber : Type := Nat

-- def thirtyEight : NaturalNumer := 38

def thirtyEight : NaturalNumber := (38 : Nat)

abbrev N : Type := Nat

def thirtyNine : N := 39

