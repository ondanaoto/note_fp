import Note.A04_OverloadingAndTypeClasses.A0401_PositiveNumbers
import Note.A01_GettingToKnowLean.A0106_Polymorpshism
-- # Indexing

-- ## Arrays

def northernTrees : Array String :=
  #["sloe", "birch", "elm", "oak"]

#eval northernTrees.size
#eval northernTrees[2]
-- #eval northernTrees[8]

-- ## Non-Empty Lists

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList String :=
  ⟨
    "Banded Garden Spiders",
    [
      "Long-legged Sac Spider",
      "Wolf Spider",
      "Hobo Spider",
      "Cat-faced Spider"
    ]
  ⟩

def NonEmptyList.get'? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | {head := _, tail := []}, _ + 1 => none
  | {head := _, tail := h :: t}, n + 1 => get'? {head := h, tail := t} n

def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | xs, n + 1 => xs.tail.get? n

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by exact Nat.le_of_ble_eq_true rfl

theorem nonSixSpiders : ¬idahoSpiders.inBounds 5 := by exact Nat.not_succ_le_self 4

def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (_ : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]


-- ## Overloading Indexing
-- class GetElem (coll : Type) (idx : Type) (item : outParam Type) (inBounds : outParam (coll → idx → Prop)) where
--  getElem : (c : coll) → (i : idx) → inBounds c i → item

instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

#eval idahoSpiders[0]
#eval idahoSpiders[1]

#check_failure idahoSpiders[9]

instance : GetElem (List α) Pos α (fun list n => list.length > n.toNat) where
  getElem (xs : List α) (i : Pos) ok := xs[i.toNat]

instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p : PPoint α) (i : Bool) _ :=
    if not i then p.x else p.y

def a : PPoint Float := {x := 2.3, y := 4.5}
#eval a[true]
