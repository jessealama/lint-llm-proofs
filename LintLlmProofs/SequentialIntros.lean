/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Lean.Elab.Command

/-!
# Sequential Intros Linter

The sequential intros linter detects patterns where multiple `intro` tactics are
used consecutively instead of combining them into a single `intro x y z`.

## Example of flagged code:
```lean
example : ∀ x y z : Nat, x = x := by
  intro x
  intro y  -- Warning: sequential intro
  intro z  -- Warning: sequential intro
  rfl
```

## Suggested fix:
```lean
example : ∀ x y z : Nat, x = x := by
  intro x y z
  rfl
```
-/

open Lean Elab Command

namespace LintLlmProofs

/-- The sequential intros linter emits a warning when multiple `intro` tactics
appear consecutively. -/
register_option linter.sequentialIntros : Bool := {
  defValue := false
  descr := "enable the sequential intros linter"
}

namespace SequentialIntrosLinter

/-- Check if syntax is an `intro` tactic. -/
def isIntroTactic (stx : Syntax) : Bool :=
  stx.getArgs.any fun arg =>
    if let .atom _ val := arg then
      val == "intro"
    else
      false

/-- Check if a syntax node is a non-intro tactic by looking for tactic keywords. -/
def isNonIntroTactic (stx : Syntax) : Bool :=
  stx.getArgs.any fun arg =>
    if let .atom _ val := arg then
      -- Common tactic keywords that would break intro sequences
      val == "rfl" || val == "exact" || val == "apply" || val == "simp" ||
      val == "constructor" || val == "cases" || val == "induction" ||
      val == "have" || val == "let" || val == "show" || val == "refine" ||
      val == "trivial" || val == "assumption" || val == "decide" ||
      val == "ring" || val == "linarith" || val == "omega" || val == "norm_num"
    else
      false

/-- Collect all tactic-like nodes from a tactic sequence, marking each as intro or not.
    Returns (isIntro, syntax) pairs to properly track when non-intro tactics break sequences. -/
partial def collectTactics (stx : Syntax) : Array (Bool × Syntax) :=
  if stx.getKind == ``Lean.Parser.Tactic.tacticSeq ||
     stx.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
    stx.getArgs.foldl (fun acc child => acc ++ collectTactics child) #[]
  else if isIntroTactic stx then
    #[(true, stx)]
  else if isNonIntroTactic stx then
    #[(false, stx)]  -- Non-intro tactic that breaks sequences
  else
    stx.getArgs.foldl (fun acc child => acc ++ collectTactics child) #[]

/-- Find sequential intro patterns. Flags all but the first intro in a sequence. -/
partial def findSequentialIntros (stx : Syntax) : Array Syntax := Id.run do
  let mut results := #[]

  let tactics := collectTactics stx

  -- Find runs of consecutive intros and flag all but the first
  let mut inIntroRun := false
  for (isIntro, tac) in tactics do
    if isIntro then
      if inIntroRun then
        -- This is a second (or later) intro in sequence
        results := results.push tac
      else
        -- First intro in a potential sequence
        inIntroRun := true
    else
      inIntroRun := false

  return results

/-- The sequential intros linter: detects multiple consecutive `intro` tactics.

LLMs often introduce variables one at a time instead of using `intro x y z`.
-/
def sequentialIntrosLinter : Linter where run := withSetOptionIn fun stx => do
  unless linter.sequentialIntros.get (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for introStx in findSequentialIntros stx do
    Linter.logLint linter.sequentialIntros introStx
      "Sequential `intro` tactics detected. Consider combining into a single `intro x y z`."

initialize addLinter sequentialIntrosLinter

end SequentialIntrosLinter
end LintLlmProofs
