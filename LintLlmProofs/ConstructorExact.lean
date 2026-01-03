/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Lean.Elab.Command

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

/-- Find constructor-exact patterns. Flags constructor when followed by exactly 2 exacts. -/
partial def findConstructorExactPatterns (stx : Syntax) : Array Syntax := Id.run do
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
          results := results.push tac1

  return results

/-- The constructor-exact linter: detects `constructor; exact h1; exact h2` patterns.

LLMs often spell out pair construction verbosely instead of using `⟨h1, h2⟩`.
-/
def constructorExactLinter : Linter where run := withSetOptionIn fun stx => do
  unless linter.constructorExact.get (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for ctorStx in findConstructorExactPatterns stx do
    Linter.logLint linter.constructorExact ctorStx
      "`constructor` followed by `exact` tactics. Consider using `exact ⟨_, _⟩` instead."

initialize addLinter constructorExactLinter

end ConstructorExactLinter
end LintLlmProofs
