-- # Step By Step

def greet : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"

-- ## Asking a Question

#eval "Hello!!!".dropRightWhile (· == '!')

#eval "Hello...   ".dropRightWhile (fun c => not (c.isAlphanum))


-- ## `IO` Actions as Values

def twice (action : IO Unit) : IO Unit := do
  action
  action

def printTwice : IO Unit := twice (IO.println "shy")

def nTimes (action : IO Unit) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    action
    nTimes action n

def printHelloThreeTimes := nTimes (IO.println "hello") 3

def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}!!" :: countdown n

def from5 : List (IO Unit) := countdown 5
#eval from5.length

def runActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | act :: actions => do
    act
    runActions actions

def fiveOneBlast : IO Unit := runActions (countdown 5)

-- ## Exercise

def helloBonjour : IO Unit := do
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  englishGreeting

-- Q. When an expression is being evaluated?
-- A. The first line.
-- Q. When and `IO` action is being executed?
-- A. The last two lines.
-- Q. When executing an `IO` action results in a side effect, write it down.
-- A. Executing `IO.println "Bonjour!"` prints `Bonjour!` to the console.
--    Executing `englishGreeting` prints `Hello!` to the console.

def main : IO Unit := helloBonjour
