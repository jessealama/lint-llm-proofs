/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Lean.Elab.Command

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

/-- Recursively find all nested have patterns in a syntax tree.
Returns all `have` syntax nodes that appear inside another `have`'s proof body. -/
partial def findNestedHaves (stx : Syntax) (insideHave : Bool := false) : Array Syntax :=
  let currentIsHave := isHaveTactic stx
  -- If we're inside a have and find another have, flag it
  let thisMatch := if insideHave && currentIsHave then #[stx] else #[]
  -- Recurse into children, tracking if we're now inside a have
  let childMatches := stx.getArgs.foldl (init := #[]) fun acc child =>
    acc ++ findNestedHaves child (insideHave || currentIsHave)
  thisMatch ++ childMatches

/-- The nested have linter: detects `have` statements nested inside other `have` statements.

LLMs often produce deeply nested `have` chains instead of flattening them at the same
scope level. This linter flags such patterns to encourage cleaner proof structure.
-/
def nestedHaveLinter : Linter where run := withSetOptionIn fun stx => do
  unless linter.nestedHave.get (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for nestedHave in findNestedHaves stx do
    Linter.logLint linter.nestedHave nestedHave
      "Nested `have` detected. Consider hoisting this `have` to the outer scope \
       for clearer proof structure."

initialize addLinter nestedHaveLinter

end NestedHaveLinter
end LintLlmProofs
