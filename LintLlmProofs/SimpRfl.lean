/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Lean.Elab.Command

/-!
# Simp-Rfl Redundancy Linter

The simp-rfl linter detects the pattern where `simp` is immediately followed by `rfl`
or `exact rfl`. If `simp` succeeds, it should close reflexivity goals. The trailing
`rfl` is either redundant or indicates `simp` didn't fully work.

## Example of flagged code:
```lean
example (a : Nat) : a + 0 = a := by
  simp
  rfl  -- Warning: redundant after simp
```

## Suggested fix:
```lean
example (a : Nat) : a + 0 = a := by
  simp
```
-/

open Lean Elab Command

namespace LintLlmProofs

/-- The simp-rfl linter emits a warning when `simp` is immediately followed by `rfl`. -/
register_option linter.simpRfl : Bool := {
  defValue := false
  descr := "enable the simp-rfl redundancy linter"
}

namespace SimpRflLinter

/-- Check direct children for an atom with the given value. -/
def hasDirectAtom (stx : Syntax) (val : String) : Bool :=
  stx.getArgs.any fun arg =>
    if let .atom _ v := arg then v == val else false

/-- Check if syntax is a `simp` tactic by looking for simp keyword as direct child. -/
def isSimpTactic (stx : Syntax) : Bool :=
  hasDirectAtom stx "simp" || hasDirectAtom stx "simp_all" || hasDirectAtom stx "simp?"

/-- Check if syntax is `rfl` tactic. -/
def isRflTactic (stx : Syntax) : Bool :=
  hasDirectAtom stx "rfl"

/-- Check if syntax is `exact` followed by `rfl`. -/
def isExactRflTactic (stx : Syntax) : Bool :=
  hasDirectAtom stx "exact" &&
    stx.getArgs.any fun arg =>
      if arg.isIdent then arg.getId.toString == "rfl"
      else if let .atom _ v := arg then v == "rfl"
      else false

/-- Check if syntax is either `rfl` or `exact rfl`. -/
def isRflOrExactRfl (stx : Syntax) : Bool :=
  isRflTactic stx || isExactRflTactic stx

/-- Flatten a tactic sequence into a list of individual tactics. -/
partial def flattenTactics (stx : Syntax) : Array Syntax :=
  if isSimpTactic stx || isRflOrExactRfl stx then
    #[stx]
  else if stx.getKind == ``Lean.Parser.Tactic.tacticSeq ||
          stx.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
    stx.getArgs.foldl (fun acc child => acc ++ flattenTactics child) #[]
  else
    stx.getArgs.foldl (fun acc child => acc ++ flattenTactics child) #[]

/-- Find simp-rfl patterns in tactic sequences. -/
partial def findSimpRflPatterns (stx : Syntax) : Array Syntax := Id.run do
  let mut results := #[]

  let tactics := flattenTactics stx

  for i in [0:tactics.size] do
    if i + 1 < tactics.size then
      let tac1 := tactics[i]!
      let tac2 := tactics[i + 1]!
      if isSimpTactic tac1 && isRflOrExactRfl tac2 then
        results := results.push tac2

  return results

/-- The simp-rfl linter: detects `simp; rfl` or `simp; exact rfl` patterns.

LLMs often add redundant `rfl` after `simp` calls. If `simp` fully simplifies
the goal to reflexivity, the `rfl` is unnecessary.
-/
def simpRflLinter : Linter where run := withSetOptionIn fun stx => do
  unless linter.simpRfl.get (← getOptions) do
    return
  -- Note: We intentionally don't check hasErrors because the pattern we detect
  -- often causes errors (redundant rfl after simp closes the goal).
  for rflStx in findSimpRflPatterns stx do
    Linter.logLint linter.simpRfl rflStx
      "`rfl` immediately after `simp` is often redundant. \
       Consider removing it or using `simp only [...]` if `simp` doesn't close the goal."

initialize addLinter simpRflLinter

end SimpRflLinter
end LintLlmProofs
