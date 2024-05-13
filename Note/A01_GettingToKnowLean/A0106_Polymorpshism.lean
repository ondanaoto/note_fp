-- # Polymorphism

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOrigin : PPoint Nat :=
  {x := Nat.zero, y := Nat.zero}

def replaceX' (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  {point with x := newX}

#check replaceX'

#check replaceX' Nat

#check replaceX' Nat natOrigin

#eval replaceX' Nat natOrigin 5

inductive Sign where
  | pos
  | neg

def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)

#eval posOrNegThree Sign.pos


-- ## Linked Lists

def primeUnder10 : List Nat := [2, 3, 5, 7]

inductive List' (α : Type) where
  | nil : List' α
  | cons : α → List' α → List' α

def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))

def length'' (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons _ ys => Nat.succ (length'' α ys)

def length' (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length' α ys)

-- ## Implicit Arguments

def replaceX {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  {point with x := newX}

#eval replaceX natOrigin 5

def length {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length ys)

#eval length primeUnder10
#eval primeUnder10.length

#check List.length (α := Int)

-- ## More Built-In Datatypes
-- ### `Option`

inductive Option' (α : Type) : Type where
  | none : Option' α
  | some (val : α) : Option' α

def List.head?' {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | x :: _ => some x

#eval primeUnder10.head?

-- #eval [].head?
#eval [].head? (α := Int)
#eval ([] : List Int).head?


-- ### `Prod`

structure Prod' (α : Type) (β : Type) : Type where
  fst : α
  snd : β

def fives' : String × Int := { fst := "five", snd := 5 }
def fives : String × Int := ("five", 5)

def sevens : String × Int × Nat := ("VII", 7, 4 + 3)

def sevens' : String × (Int × Nat) := ("VII", (7, 4 + 3))

#eval sevens = sevens'


-- ### `Sum`

inductive Sum' (α : Type) (β : Type) : Type where
  | inl : α → Sum' α β
  | inr : β → Sum' α β
deriving Repr

#eval Sum.inl 1 (β := Int)

def PetName : Type := String ⊕ String

def animals' : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]

def howManyDogs' (pets : List PetName) : Nat :=
  match pets with
  |[] => 0
  | Sum.inl _ :: morePets => howManyDogs' morePets + 1
  | Sum.inr _ :: morePets => howManyDogs' morePets

#eval howManyDogs' animals'


-- ### Unit

inductive Unit' : Type where
  | unit : Unit'

inductive ArithExpr (ann : Type) : Type where
  | inr : ann → Int → ArithExpr ann
  | plus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann

#check (ArithExpr.inr () 2)


-- ### `Empty`

#check (Sum.inl 2 : Nat ⊕ Empty)

-- ### Naming: Sums, Products, and Units

-- ## Messages You May Meet

-- inductive MyType : Type where
--   | ctor : (α : Type) → α → MyType

-- inductive MyType : Type where
--   | ctor : (MyType → Int) → MyType

-- inductive MyType (α : Type) : Type where
--   | ctor : α → MyType

inductive MyType (α : Type) : Type where
  | ctor : α → MyType α

-- def ofFive : MyType := ctor 5

-- ## Exercises
def last? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | y :: [] => some y
  | _ :: ys => last? ys

#eval last? primeUnder10

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | [] => none
  | y :: ys =>
    if predicate y
    then some y
    else List.findFirst? ys predicate

def maybeAnymals : List (Option String) := [none, some "Tiger", none]
def notNone {α : Type} (x : Option α) : Bool :=
  match x with
  | none => false
  | some _ => true

#eval maybeAnymals.findFirst? (notNone)

def Prod.swap {α β : Type} (pair : α × β) : β × α :=
  (pair.snd, pair.fst)

inductive PetName' : Type where
  | dog : String → PetName'
  | cat : String → PetName'
deriving Repr

def animals : List PetName' :=
  [.dog "Spot", .cat "Tiger", .dog "Fifi", .dog "Rex", .cat "Floof"]

def howManyDogs (pets : List PetName') : Nat :=
  match pets with
  |[] => 0
  | .dog _ :: morePets => howManyDogs morePets + 1
  | .cat _ :: morePets => howManyDogs morePets

#eval howManyDogs animals

def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs, ys with
  | [], _ => []
  | _ , [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys

#eval zip primeUnder10 animals

def take {α : Type} (n : Nat) (x : List α) : List α :=
  match n, x with
  | _, [] => []
  | 0, _ => []
  | .succ k, y :: ys => y :: take k ys

#eval take 3 animals

def distribute {α β γ : Type} (abg : α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
  let a := abg.fst
  match abg.snd with
  | Sum.inl b => Sum.inl (a, b)
  | Sum.inr g => Sum.inr (a, g)

def mult_two {α : Type} (ba : Bool × α) : α ⊕ α :=
  let a := ba.snd
  if ba.fst
  then Sum.inr a
  else Sum.inl a
