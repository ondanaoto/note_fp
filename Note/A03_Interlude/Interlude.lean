-- # Interlude: Propositions, Proofs, and Indexing

def woodlandCritters: List String :=
  ["hedgehog", "deer", "snail"]


def hedgehog := woodlandCritters[0]
def deer := woodlandCritters[1]
def snail := woodlandCritters[2]

-- def oops := woodlandCritters[3]


-- ## Propositions and Proofs

def onePlusOneIsTwo : 1 + 1 = 2 := rfl

-- def onePlusOneIsFifteen : 1 + 1 = 15 := rfl

def OnePlusOneIsTwo : Prop := 1 + 1 = 2

theorem onePlusOneIsTwo' : OnePlusOneIsTwo := rfl


-- ## Tactics

theorem onePlusOneIsTwo'' : 1 + 1 = 2 := by
  simp

-- ## Connectives

#print And

theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := And.intro rfl rfl

theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _ => Or.inl a

theorem onePlusOneAndLessThan : 1 + 1 = 2 ∨ 3 < 5 := by simp
theorem notTwoEqualFive : ¬(1 + 1 = 5) := by simp
theorem trueIsTrue : True := True.intro
theorem trueOrFalse : True ∨ False := by simp
theorem falseImpliesTrue : False → True := by simp


-- ## Evidence as Arguments
-- def third (xs : List α) : α := xs[2]

def third (xs : List α) (ok : xs.length > 2) : α := xs[2]

#eval third woodlandCritters (by simp[List.length])

-- ## Indexing Without Evidence

def thirdOption (xs : List α) : Option α := xs[2]?

#eval thirdOption woodlandCritters
#eval thirdOption ["only", "two"]

#eval woodlandCritters[1]!

-- ## Messages You May Meet

-- def unsafeThird (xs : List α) : α := xs[2]!
-- #eval woodlandCritters [1]

-- ## Exercises

example : 2 + 3 = 5 := rfl
example : 15 - 8 = 7 := rfl
example : "Hello, ".append "world" = "Hello, world" := rfl

-- It causes error since rfl tactic can only be applied to equal statements.
-- example : 5 < 18 := rfl

example : 2 + 3 = 5 := by simp
example : 15 - 8 = 7 := by simp
-- example : "Hello, ".append "world" = "Hello, world" := by simp
example : 5 < 18 := by simp

def fifth (xs : List α) (h : xs.length > 4) := xs[4]
