/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Lean.Elab.Command
import Lean.Meta.Hint

/-!
# Nested Let Linter

The nested let linter detects `let` statements whose proof body contains
another `let` statement. This is a common pattern in LLM-generated proofs,
where the model produces deeply nested `let` chains instead of flattening them.

## Example of flagged code:
```lean
example : True := by
  let x : Nat := by
    let y : Nat := 2  -- This inner `let` triggers a warning
    exact 1
  trivial
```

## Suggested fix:
```lean
example : True := by
  let y : Nat := 2  -- Hoisted to outer scope
  let x : Nat := 1
  trivial
```
-/

open Lean Elab Command

namespace LintLlmProofs

/-- The nested let linter emits a warning when a `let` statement's proof
body contains another `let` statement. -/
register_option linter.nestedLet : Bool := {
  defValue := false
  descr := "enable the nested let linter"
}

namespace NestedLetLinter

/-- Check if a syntax node represents a `let` tactic using pattern matching. -/
def isLetTactic (stx : Syntax) : Bool :=
  -- Match on `let` tactic syntax: "let" letDecl
  if let `(tactic| let $_:letDecl) := stx then true else false

/-- Extract identifier names from syntax. -/
partial def collectIdents (stx : Syntax) : Array Name :=
  if stx.isIdent then
    #[stx.getId]
  else
    stx.getArgs.foldl (fun acc child => acc ++ collectIdents child) #[]

/-- Extract the first identifier from a let tactic (the variable name). -/
def getLetVarName (stx : Syntax) : Option Name :=
  let idents := collectIdents stx
  let filtered := idents.filter fun n =>
    !n.isAnonymous && n.toString != "let" && n.toString != "by"
  filtered[0]?

/-- Check if inner let references the outer let's variable. -/
def innerReferencesOuter (innerLet : Syntax) (outerName : Name) : Bool :=
  let innerIdents := collectIdents innerLet
  innerIdents.contains outerName

/-- Recursively find all nested let patterns in a syntax tree.
Returns (outerLet, innerLet) pairs for auto-fix generation. -/
partial def findNestedLets (stx : Syntax) (outerLet? : Option Syntax := none) : Array (Syntax × Syntax) :=
  let currentIsLet := isLetTactic stx
  -- If we're inside a let and find another let, record the pair
  let thisMatch := match outerLet? with
    | some outer => if currentIsLet then #[(outer, stx)] else #[]
    | none => #[]
  -- Recurse into children, updating outer let if this is one
  let newOuter := if currentIsLet then some stx else outerLet?
  let childMatches := stx.getArgs.foldl (init := #[]) fun acc child =>
    acc ++ findNestedLets child newOuter
  thisMatch ++ childMatches

/-- Legacy function for backward compatibility - returns just the inner lets. -/
def findNestedLetsSimple (stx : Syntax) : Array Syntax :=
  (findNestedLets stx).map (·.2)

/-- Create a syntax node spanning from start of stx1 to end of stx2. -/
def mkSpanningSyntax (stx1 stx2 : Syntax) : Option Syntax := do
  let range1 ← stx1.getRange?
  let range2 ← stx2.getRange?
  return Syntax.ofRange ⟨range1.start, range2.stop⟩

/-- The nested let linter: detects `let` statements nested inside other `let` statements.

LLMs often produce deeply nested `let` chains instead of flattening them at the same
scope level. This linter flags such patterns to encourage cleaner proof structure.
-/
def nestedLetLinter : Linter where run := withSetOptionIn fun stx => do
  unless linter.nestedLet.get (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for (outerLet, innerLet) in findNestedLets stx do
    let msg := m!"Nested `let` detected."
    -- Check if inner references outer's variable
    let outerName := getLetVarName outerLet
    let hasDepend := match outerName with
      | some name => innerReferencesOuter innerLet name
      | none => false
    -- Generate suggestion: inner let printed out for hoisting
    -- Note: Full rewrite is complex; we show the inner let that should be hoisted
    let innerStr := innerLet.reprint.getD (toString innerLet.prettyPrint)
    let suggestion : Meta.Hint.Suggestion := {
      suggestion := innerStr.trim
      span? := some innerLet  -- Replace the inner let with itself (as a hint)
    }
    let hintMsg := if hasDepend then
      m!"This inner `let` references the outer variable, so automatic hoisting may require manual adjustment."
    else
      m!"Hoist this `let` before the outer `let`."
    let hint ← liftCoreM <| MessageData.hint hintMsg #[suggestion]
    Linter.logLint linter.nestedLet innerLet (msg ++ hint)

initialize addLinter nestedLetLinter

end NestedLetLinter
end LintLlmProofs
