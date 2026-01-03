/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Lean.Elab.Command
import Lean.Meta.Hint

/-!
# Nested Have Linter

The nested have linter detects `have` statements whose proof body contains
another `have` statement. This is a common pattern in LLM-generated proofs,
where the model produces deeply nested `have` chains instead of flattening them.

## Example of flagged code:
```lean
example : True := by
  have h1 : 1 = 1 := by
    have h2 : 2 = 2 := rfl  -- This inner `have` triggers a warning
    rfl
  trivial
```

## Suggested fix:
```lean
example : True := by
  have h2 : 2 = 2 := rfl  -- Hoisted to outer scope
  have h1 : 1 = 1 := rfl
  trivial
```
-/

open Lean Elab Command

namespace LintLlmProofs

/-- The nested have linter emits a warning when a `have` statement's proof
body contains another `have` statement. -/
register_option linter.nestedHave : Bool := {
  defValue := false
  descr := "enable the nested have linter"
}

namespace NestedHaveLinter

/-- Check if a syntax node represents a `have` tactic using pattern matching. -/
def isHaveTactic (stx : Syntax) : Bool :=
  -- Match on `have` tactic syntax: "have" letConfig letDecl
  if let `(tactic| have $_:letConfig $_:letDecl) := stx then true else false

/-- Extract identifier names from syntax. -/
partial def collectIdents (stx : Syntax) : Array Name :=
  if stx.isIdent then
    #[stx.getId]
  else
    stx.getArgs.foldl (fun acc child => acc ++ collectIdents child) #[]

/-- Extract the first identifier from a have tactic (the hypothesis name). -/
def getHaveHypName (stx : Syntax) : Option Name :=
  let idents := collectIdents stx
  let filtered := idents.filter fun n =>
    !n.isAnonymous && n.toString != "have" && n.toString != "by"
  filtered[0]?

/-- Check if inner have references the outer have's variable. -/
def innerReferencesOuter (innerHave : Syntax) (outerName : Name) : Bool :=
  let innerIdents := collectIdents innerHave
  innerIdents.contains outerName

/-- Recursively find all nested have patterns in a syntax tree.
Returns (outerHave, innerHave) pairs for auto-fix generation. -/
partial def findNestedHaves (stx : Syntax) (outerHave? : Option Syntax := none) : Array (Syntax × Syntax) :=
  let currentIsHave := isHaveTactic stx
  -- If we're inside a have and find another have, record the pair
  let thisMatch := match outerHave? with
    | some outer => if currentIsHave then #[(outer, stx)] else #[]
    | none => #[]
  -- Recurse into children, updating outer have if this is one
  let newOuter := if currentIsHave then some stx else outerHave?
  let childMatches := stx.getArgs.foldl (init := #[]) fun acc child =>
    acc ++ findNestedHaves child newOuter
  thisMatch ++ childMatches

/-- Legacy function for backward compatibility - returns just the inner haves. -/
def findNestedHavesSimple (stx : Syntax) : Array Syntax :=
  (findNestedHaves stx).map (·.2)

/-- Create a syntax node spanning from start of stx1 to end of stx2. -/
def mkSpanningSyntax (stx1 stx2 : Syntax) : Option Syntax := do
  let range1 ← stx1.getRange?
  let range2 ← stx2.getRange?
  return Syntax.ofRange ⟨range1.start, range2.stop⟩

/-- The nested have linter: detects `have` statements nested inside other `have` statements.

LLMs often produce deeply nested `have` chains instead of flattening them at the same
scope level. This linter flags such patterns to encourage cleaner proof structure.
-/
def nestedHaveLinter : Linter where run := withSetOptionIn fun stx => do
  unless linter.nestedHave.get (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for (outerHave, innerHave) in findNestedHaves stx do
    let msg := m!"Nested `have` detected."
    -- Check if inner references outer's variable
    let outerName := getHaveHypName outerHave
    let hasDepend := match outerName with
      | some name => innerReferencesOuter innerHave name
      | none => false
    -- Generate suggestion: inner have printed out for hoisting
    -- Note: Full rewrite is complex; we show the inner have that should be hoisted
    let innerStr := innerHave.reprint.getD (toString innerHave.prettyPrint)
    let suggestion : Meta.Hint.Suggestion := {
      suggestion := innerStr.trim
      span? := some innerHave  -- Replace the inner have with itself (as a hint)
    }
    let hintMsg := if hasDepend then
      m!"This inner `have` references the outer hypothesis, so automatic hoisting may require manual adjustment."
    else
      m!"Hoist this `have` before the outer `have`."
    let hint ← liftCoreM <| MessageData.hint hintMsg #[suggestion]
    Linter.logLint linter.nestedHave innerHave (msg ++ hint)

initialize addLinter nestedHaveLinter

end NestedHaveLinter
end LintLlmProofs
