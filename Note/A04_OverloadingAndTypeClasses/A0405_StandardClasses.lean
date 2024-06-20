import Note.A04_OverloadingAndTypeClasses.A0401_PositiveNumbers
import Note.A04_OverloadingAndTypeClasses.A0404_ArraysAndIndexing

-- # Standard Classes

-- ## Arithmetic

-- ## Bitwise Operators
#eval 1<<<3

-- ## Equality and Ordering
#eval "Octopus" == "Cuttlefish"
#eval "Octopodes" == "Octo".append "podes"
#check_failure (fun (x : Nat) => 1 + x) == (Nat.succ ·)

#check 2 < 4
#eval if 2 < 4 then 1 else 2
#check_failure if (fun (x : Nat) => 1 + x) = (Nat.succ ·) then "yes" else "no"

def Pos.comp : Pos → Pos → Ordering
| .one, .one => Ordering.eq
| .one, .succ _ => Ordering.lt
| .succ _, .one => Ordering.gt
| .succ n, .succ k => Pos.comp n k

instance : Ord Pos where
  compare := Pos.comp

attribute [instance] ltOfOrd

#eval (3 : Pos) > (2 : Pos)


-- ## Hashing

def hashPos : Pos → UInt64
  | Pos.one => 0
  | Pos.succ n => mixHash 1 (hashPos n)

instance : Hashable Pos where
  hash := hashPos

#eval hash (2 : Pos)

instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf =>
    true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ =>
    false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf =>
    0
  | BinTree.branch left x right =>
    mixHash 1 (mixHash (hashBinTree left) (mixHash (hash x) (hashBinTree right)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree


-- ## Deriving Standard Classes

#check_failure idahoSpiders == idahoSpiders

deriving instance BEq, Hashable for Pos
-- deriving instance ToString for NonEmptyList
deriving instance BEq, Hashable, Repr for NonEmptyList


#eval hash idahoSpiders
#eval idahoSpiders == idahoSpiders
#eval idahoSpiders

-- ## Appending

instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

#eval idahoSpiders ++ idahoSpiders

instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys :=
    { head := xs.head, tail := xs.tail ++ ys }

#eval idahoSpiders ++ ["Trapdoor Spider"]

-- ## Functors

#eval Functor.map (· + 5) [1, 2, 3]
#eval Functor.map toString (some (List.cons 5 List.nil))
#eval Functor.map List.reverse [[1, 2, 3], [4, 5, 6]]

#eval (· + 5) <$> [1, 2, 3]
#eval toString <$> (some (List.cons 5 List.nil))
#eval List.reverse <$> [[1, 2, 3], [4, 5, 6]]

instance : Functor NonEmptyList where
  map f xs := { head := f xs.head, tail := f <$> xs.tail }

#eval "hoge".append <$> idahoSpiders

instance : Functor PPoint where
  map f p := { x := f p.x, y := f p.y }

#eval (· + 2) <$> (PPoint.mk 2 3)

def concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | [] => start
    | (z :: zs) => catList (start ++ z) zs
  catList xs.head xs.tail

-- ## Exercises

def appendl_nonempl : List α → NonEmptyList α → NonEmptyList α
| [], ys => ys
| x::xs, {head, tail} => {head := x, tail := xs++[head]++tail}

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend := appendl_nonempl

#eval ([]: List String) ++ idahoSpiders

def BinTree.map (f : α → β) (binTree : BinTree α) : BinTree β :=
match binTree with
| .leaf => .leaf
| .branch l a r => .branch (l.map f) (f a) (r.map f)

instance : Functor BinTree where
  map := BinTree.map

def intBinTree := BinTree.branch .leaf 2 .leaf

deriving instance Repr for BinTree
#eval (· + 2) <$> intBinTree
