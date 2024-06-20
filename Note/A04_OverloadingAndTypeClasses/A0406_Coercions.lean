import Lean

import Note.A04_OverloadingAndTypeClasses.A0401_PositiveNumbers
import Note.A04_OverloadingAndTypeClasses.A0405_StandardClasses

-- # Coercions

-- ## Positive Numbers

#check (Pos.toNat)

-- #eval [1,2,3,4].drop (2 : Pos)

#check (Coe)

instance : Coe Pos Nat where
  coe := Pos.toNat

#eval [1,2,3,4].drop (2 : Pos)

#check [1,2,3,4].drop (2 : Pos)


-- ## Chaining Coercions

def oneInt : Int := Pos.one

inductive A where
  | a

inductive B where
  | b
deriving Repr

instance : Coe A B where
  coe _ := B.b

instance : Coe B A where
  coe _ := A.a

instance : Coe Unit A where
  coe _ := A.a

def coercedToB : B := ()

#eval coercedToB

def List.last? : List α → Option α
  | [] => none
  | [x] => x
  | _ :: x :: xs => last? (x :: xs)

def perhapsPerhapsPerhaps : Option (Option (Option String)) :=
  "Please don't tell me"

-- def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
-- 392
def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  (392 : Nat)

def perhapsPerhapsPerhapsNat' : Option (Option (Option Nat)) :=
  ↑(392 : Nat)


-- ## Non-Empty Lists and Dependent Coercions

instance : Coe (NonEmptyList α) (List α) where
  coe
    | { head := x, tail := xs } => x :: xs

#eval (idahoSpiders : List String)
#check (CoeDep)

instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := {head := x, tail := xs}

#eval ([1,2,3] : NonEmptyList Nat)


-- ## Coercing to Types

structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  {Carrier := Nat, neutral := 1, op := (· * ·)}

def natAddMonoid : Monoid :=
  {Carrier := Nat, neutral := 0, op := (· + ·)}

def stringMonoid : Monoid :=
  {Carrier := String, neutral := "", op := String.append}

def listMonoid (α : Type) : Monoid :=
  {Carrier := List α, neutral := [], op := List.append}

def foldMap' (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

#eval foldMap' natAddMonoid String.length ["hello", "world"]

instance : CoeSort Monoid Type where
  coe m := m.Carrier

def foldMap (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

instance : CoeSort Bool Prop where
  coe b := b = true


-- ## Coercing to Functions

#print CoeFun

structure Adder  where
  howMuch : Nat

def add5 : Adder := ⟨5⟩

/--
error: function expected at
  add5
term has type
  Adder
-/
#guard_msgs in
#eval add5 3

instance : CoeFun Adder (fun _ => Nat → Nat) where
  coe a := (· + a.howMuch)

#eval add5 3

inductive JSON where
| true : JSON
| false : JSON
| null : JSON
| string : String → JSON
| number : Float → JSON
| object : List (String × JSON) → JSON
| array : List JSON → JSON
deriving Repr

structure Serializer where
  Contents : Type
  serialize : Contents → JSON

def Str : Serializer :=
  { Contents := String,
    serialize := JSON.string
  }

instance : CoeFun Serializer (fun s => s.Contents → JSON) where
  coe s := s.serialize

def buildResponse (title : String) (R : Serializer) (record : R.Contents) : JSON :=
  JSON.object [
    ("title", JSON.string title),
    ("status", JSON.number 200),
    ("record", R record)
  ]

#eval buildResponse "Functional Programming in Lean" Str "Programming is fun!"


-- ## Aside: JSON as a String

#eval (5 : Float).toString

def dropDecimals (numString : String) : String :=
  if numString.contains '.' then
    let noTrailingZeros := numString.dropRightWhile (· == '0')
    noTrailingZeros.dropRightWhile (· == '.')
  else numString

#eval dropDecimals (5 : Float).toString

#eval dropDecimals (3.4 : Float).toString

def String.separate (sep : String) (strings : List String) : String :=
  match strings with
  | [] => ""
  | x :: xs => String.join (x :: xs.map (sep ++ ·))

#eval ", ".separate ["2", "3"]
#eval ", ".separate ["1"]
#eval ", ".separate []

partial def JSON.asString (val : JSON) : String :=
  match val with
  | true => "true"
  | false => "false"
  | null => "null"
  | string s => "\"" ++ Lean.Json.escape s ++ "\""
  | number n => dropDecimals n.toString
  | object members =>
    let memberToString mem :=
      "\"" ++ Lean.Json.escape mem.fst ++ "\": " ++ asString mem.snd
    "{" ++ ", ".separate (members.map memberToString) ++ "}"
  | array elements =>
    "[" ++ ", ".separate (elements.map asString) ++ "]"

#eval (buildResponse "Functional Programming in Lean" Str "Programming is fun!").asString


-- ## Messages You May Meet
-- def perhapsPerhapsPerhapsNat'' : Option (Option (Option Nat)) := 392

-- ## Design Considerations

def lastSpider : Option String :=
  List.getLast? idahoSpiders

-- def lastSpider' :=
--   List.getLast? idahoSpiders
