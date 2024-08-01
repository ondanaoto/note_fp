import Note.A05_Monads.A0500_Monads
-- # The Monad Type Class

namespace Monad

class Monad (m : Type → Type) where
  pure : α → m α
  bind : m α → (α → m β) → m β

instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some y => next y

instance : Monad (Except ε) where
  pure x := Except.ok x
  bind attempt next :=
    match attempt with
    | .error e => .error e
    | .ok x => next x

end Monad

def firstThirdFifthSeventhh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) := do
  let first ← lookup xs 0
  let third ← lookup xs 2
  let fifth ← lookup xs 4
  let seventh ← lookup xs 6
  pure (first, third, fifth, seventh)

def slowMammals : List String := ["Three-toed sloth", "Slow loris"]

def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]

#eval firstThirdFifthSeventhh (fun xs i => xs[i]?) slowMammals

#eval firstThirdFifthSeventhh (fun xs i => xs[i]?) fastBirds

def getOrExcept (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x

#eval firstThirdFifthSeventhh getOrExcept slowMammals

#eval firstThirdFifthSeventhh getOrExcept fastBirds


-- ## General Monad Operations

def mapM [Monad m] (f : α → m β) : List α → m (List β)
| [] => pure []
| x :: xs => do
  let y ← f x
  let ys ← mapM f xs
  pure (y :: ys)

open State
instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

def increment (howMuch : Int) : State Int Int := do
  let i ← get
  set (i + howMuch)
  pure i

#eval mapM increment [1, 2, 3, 4, 5] 0

open Log in
instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}

open Log in
def saveIfEven (i : Int) : WithLog Int Int := do
  if isEven i then (save i) else pure ()
  pure i

#eval mapM saveIfEven [1, 2, 3, 4, 5]


-- ## The Identity Monad

-- def Id (t : Type) : Type := t

instance : Monad Id where
  pure x := x
  bind x f := f x

#eval mapM (m := Id) (· + 1) [1, 2, 3, 4, 5]


-- ## The Monad Contract

-- ## Exercises

-- ### Mapping on a Tree

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | .leaf => pure .leaf
  | .branch l x r => do
    let l' ← l.mapM f
    let x' ← f x
    let r' ← r.mapM f
    pure (.branch l' x' r')

-- ### The Option Monad Contract

instance : Monad Option where
  pure x := some x
  bind _ _ := none

-- bind (pure x) f = f xにならないといけないが、bind (pure x) f = noneになってしまう
