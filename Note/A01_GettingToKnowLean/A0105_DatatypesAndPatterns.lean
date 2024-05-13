import «Note».A01_GettingToKnowLean.A0104_Structures
-- # Datatypes and Patterns

inductive Bool' where
  | false : Bool'
  | true : Bool'
deriving Repr

#eval Bool'.false
#eval Bool'.true

-- standard library
#eval false
#eval true

inductive Nat' where
  | zero : Nat'
  | succ (n : Nat') : Nat'

-- ## Pattern Matching

def isZero (n : Nat) : Bool :=
  match n with
  | .zero => true
  | .succ _ => false

#eval isZero Nat.zero
#eval isZero 5

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

#eval pred 5


def depth (p : Point3D) : Float :=
  match p with
  | {x := _, y := _, z := d} => d

-- ## Recursive Functions

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)


-- def evenLoops (n : Nat) : Bool :=
--   match n with
--   | Nat.zero => true
--   | Nat.succ k => not (evenLoops n)

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')

def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')

def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')

-- needs a proof
-- def div (n : Nat) (k : Nat) : Nat :=
--   if n < k then
--     0
--   else Nat.succ (div (n - k) k)
