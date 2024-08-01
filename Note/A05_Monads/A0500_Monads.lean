import Note.A04_OverloadingAndTypeClasses.A0405_StandardClasses

-- # Monads

-- ## Checking for `none`: Don't Repeat Yourself

def first (xs : List α) : Option α := xs[0]?

def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third => some (first, third)

def firstThirdFifth (xs : List α) : Option (α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        some (first, third, fifth)

def firstThirdFifthSeventh' (xs : List α) : Option (α × α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        match xs[6]? with
        | none => none
        | some seventh =>
          some (first, third, fifth, seventh)

def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some a => next a

def firstThird' (xs : List α) : Option (α × α) :=
  andThen xs[0]? fun first =>
  andThen xs[2]? fun third =>
  some (first, third)


-- ## Infix Operators

infixl:55 " ~~> " => andThen

def firstThirdInfix (xs : List α) : Option (α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  some (first, third)

def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  xs[4]? ~~> fun fifth =>
  xs[6]? ~~> fun seventh =>
  some (first, third, fifth, seventh)

-- inductive Except (ε : Type) (α : Type) where
--   | error : ε → Except ε α
--   | ok : α → Except ε α
-- deriving BEq, Hashable, Repr
#check Except

def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some a => Except.ok a

def ediblePlants : List String :=
  ["reasons", "sea plantain", "sea buckthorn", "garden nasturtium"]

#eval get ediblePlants 2
#eval get ediblePlants 4

def firstExcept (xs : List α) : Except String α :=
  get xs 0

def firstThirdExcept (xs : List α) : Except String (α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third => Except.ok (first, third)

def firstThirdFifthExcept (xs : List α) : Except String (α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth => Except.ok (first, third, fifth)

def andThenExcept (attempt : Except ε α) (next : α → Except ε β) : Except ε β :=
  match attempt with
  | .error msg => .error msg
  | .ok x => next x

def firstThirdExcept' (xs : List α) : Except String (α × α) :=
  andThenExcept (get xs 0) fun first =>
  andThenExcept (get xs 2) fun third =>
  Except.ok (first, third)

def ok (x : α) : Except ε α := Except.ok x

def fail (err : ε) : Except ε α := Except.error err

def get' (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => fail s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => ok x

infixl:55 "~~~>" => andThenExcept

def firstThirdExcept'' (xs : List α) : Except String (α × α) :=
  get xs 0 ~~~> fun first =>
  get xs 2 ~~~> fun third =>
  ok (first, third)

def firstThirdFifthSeventhExcept (xs : List α) : Except String (α × α × α × α) :=
  get xs 0 ~~~> fun first =>
  get xs 2 ~~~> fun third =>
  get xs 4 ~~~> fun fifth =>
  get xs 6 ~~~> fun seventh =>
  ok (first, third, fifth, seventh)


-- ## Logging

def isEven (i : Int) : Bool :=
  i % 2 == 0

def sumAndFindEvens''' : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens''' is
    (if isEven i then i :: moreEven else moreEven, sum + i)

def inorderSum' : BinTree Int → List Int × Int
  | BinTree.leaf => ([], 0)
  | BinTree.branch l x r =>
    let (leftVisited, leftSum) := inorderSum' l
    let (hereVisited, hereSum) := ([x], x)
    let (rightVisited, rightSum) := inorderSum' r
    (leftVisited ++ hereVisited ++ rightVisited, leftSum + hereSum + rightSum)

def sumAndFindEvens'' : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEvens, sum) := sumAndFindEvens'' is
    let (evenHere, ()) := (if isEven i then [i] else [], ())
    (evenHere ++ moreEvens, sum + i)

namespace Log

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
deriving Repr

def andThen (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}

def ok (x : β) : WithLog α β := {log := [], val := x}

def save (data : α) : WithLog α Unit :=
  {log := [data], val := ()}

def sumAndFindEvens' : List Int → WithLog Int Int
| [] => ok 0
| i :: is =>
  andThen (if isEven i then save i else ok ()) fun () =>
  andThen (sumAndFindEvens' is) fun sum =>
  ok (i + sum)

def inorderSum' : BinTree Int → WithLog Int Int
| BinTree.leaf => ok 0
| BinTree.branch l x r =>
  andThen (inorderSum' l) fun leftSum =>
  andThen (save x) fun () =>
  andThen (inorderSum' r) fun rightSum =>
  ok (leftSum + x + rightSum)

infixl:55 " ~~> " => andThen

def sumAndFindEvens : List Int → WithLog Int Int
  | [] => ok 0
  | i :: is =>
    (if isEven i then save i else ok ()) ~~> fun () =>
    sumAndFindEvens is ~~> fun sum =>
    ok (i + sum)

def inorderSum : BinTree Int → WithLog Int Int
  | BinTree.leaf => ok 0
  | BinTree.branch l x r =>
    inorderSum l ~~> fun leftSum =>
    save x ~~> fun () =>
    inorderSum r ~~> fun rightSum =>
    ok (leftSum + x + rightSum)

end Log

-- ## Numbering Tree Nodes

open BinTree in
def aTree :=
  branch
    (branch
      (branch leaf "a" (branch leaf "b" leaf))
      "c"
      leaf)
    "d"
    (branch leaf "e" leaf)

def number (t : BinTree α) : BinTree (Nat × α) :=
  -- nをstartとして数字を割り振ってね
  -- 返り値の第一引数を起点として割り振ってね
  let rec helper (n : Nat) : BinTree α → (Nat × BinTree (Nat × α))
    | BinTree.leaf =>
      (n, BinTree.leaf)
    | BinTree.branch l x r =>
      let (k, numberedLeft) := helper n l
      let (i, numberedRight) := helper (k + 1) r
      (i, BinTree.branch numberedLeft (k, x) numberedRight)
  (helper 0 t).snd

namespace State

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

def ok (x : α) : State σ α :=
  fun s => (s, x)

def get : State σ σ :=
  fun s => (s, s)

def set (s : σ) : State σ Unit :=
  fun _ => (s, ())

def andThen (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s =>
    let (s', a) := first s
    next a s'

infixl:55 " ~~> " => andThen

def number (t : BinTree α) : BinTree (Nat × α) :=
  -- nをstartとして数字を割り振ってね
  -- 返り値の第一引数を起点として割り振ってね
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | .leaf => ok .leaf
    | .branch l x r =>
      helper l ~~> fun numberedLeft =>
      get ~~> fun n =>
      set (n + 1) ~~> fun () =>
      helper r ~~> fun numberedRight =>
      ok (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd

end State

-- ## Monads: A Functional Design Pattern
