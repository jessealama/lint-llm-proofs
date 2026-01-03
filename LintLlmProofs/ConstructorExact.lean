/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Lean.Elab.Command
import Lean.Meta.Hint

/-!
# Constructor-Exact Pattern Linter

The constructor-exact linter detects the pattern where `constructor` is followed
by multiple `exact` tactics for simple pair/And constructions. This verbose
pattern could be replaced with an anonymous constructor `⟨h1, h2⟩`.

## Example of flagged code:
```lean
example (h1 : P) (h2 : Q) : P ∧ Q := by
  constructor
  exact h1
  exact h2
```

## Suggested fix:
```lean
example (h1 : P) (h2 : Q) : P ∧ Q := by
  exact ⟨h1, h2⟩
```
-/

open Lean Elab Command

namespace LintLlmProofs

/-- The constructor-exact linter emits a warning when `constructor` is followed
by `exact` tactics that could be replaced with anonymous constructor syntax. -/
register_option linter.constructorExact : Bool := {
  defValue := false
  descr := "enable the constructor-exact pattern linter"
}

namespace ConstructorExactLinter

/-- Check if syntax is a `constructor` tactic. -/
def isConstructorTactic (stx : Syntax) : Bool :=
  stx.getArgs.any fun arg =>
    if let .atom _ val := arg then
      val == "constructor"
    else
      false

/-- Check if syntax is an `exact` tactic. -/
def isExactTactic (stx : Syntax) : Bool :=
  stx.getArgs.any fun arg =>
    if let .atom _ val := arg then
      val == "exact"
    else
      false

/-- Flatten a tactic sequence into a list of individual tactics. -/
partial def flattenTactics (stx : Syntax) : Array Syntax :=
  if isConstructorTactic stx || isExactTactic stx then
    #[stx]
  else if stx.getKind == ``Lean.Parser.Tactic.tacticSeq ||
          stx.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
    stx.getArgs.foldl (fun acc child => acc ++ flattenTactics child) #[]
  else
    stx.getArgs.foldl (fun acc child => acc ++ flattenTactics child) #[]

/-- Extract the term argument from an exact tactic. Returns the first non-keyword child. -/
def getExactArg (stx : Syntax) : Option String := Id.run do
  for arg in stx.getArgs do
    -- Skip the "exact" keyword
    if let .atom _ val := arg then
      if val == "exact" then continue
    -- If it's an identifier, return its name
    if arg.isIdent then
      return some arg.getId.toString
    -- For other terms, use prettyPrint
    if !arg.isAtom then
      return some (toString arg.prettyPrint)
  return none

/-- Find constructor-exact patterns. Returns (constructor, exact1, exact2) tuples. -/
partial def findConstructorExactPatterns (stx : Syntax) : Array (Syntax × Syntax × Syntax) := Id.run do
  let mut results := #[]

  let tactics := flattenTactics stx

  for i in [0:tactics.size] do
    if i + 2 < tactics.size then
      let tac1 := tactics[i]!
      let tac2 := tactics[i + 1]!
      let tac3 := tactics[i + 2]!
      -- Check for constructor followed by two exact tactics
      if isConstructorTactic tac1 && isExactTactic tac2 && isExactTactic tac3 then
        -- Make sure there's not a third exact (i.e., it's specifically a pair)
        let hasThirdExact := if i + 3 < tactics.size then isExactTactic tactics[i + 3]! else false
        if !hasThirdExact then
          results := results.push (tac1, tac2, tac3)

  return results

/-- Create a syntax node spanning from start of stx1 to end of stx2. -/
def mkSpanningSyntax (stx1 stx2 : Syntax) : Option Syntax := do
  let range1 ← stx1.getRange?
  let range2 ← stx2.getRange?
  return Syntax.ofRange ⟨range1.start, range2.stop⟩

/-- The constructor-exact linter: detects `constructor; exact h1; exact h2` patterns.

LLMs often spell out pair construction verbosely instead of using `⟨h1, h2⟩`.
-/
def constructorExactLinter : Linter where run := withSetOptionIn fun stx => do
  unless linter.constructorExact.get (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for (ctorStx, exact1, exact2) in findConstructorExactPatterns stx do
    let msg := m!"`constructor` followed by `exact` tactics."
    -- Extract arguments from both exact tactics
    let arg1 := getExactArg exact1 |>.getD "_"
    let arg2 := getExactArg exact2 |>.getD "_"
    let fixStr := s!"exact ⟨{arg1}, {arg2}⟩"

    let suggestion : Meta.Hint.Suggestion := {
      suggestion := fixStr
      span? := mkSpanningSyntax ctorStx exact2
    }
    let hint ← liftCoreM <| MessageData.hint m!"Use anonymous constructor." #[suggestion]
    Linter.logLint linter.constructorExact ctorStx (msg ++ hint)

initialize addLinter constructorExactLinter

end ConstructorExactLinter
end LintLlmProofs
