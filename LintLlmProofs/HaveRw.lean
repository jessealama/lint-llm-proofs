/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Lean.Elab.Command
import Lean.Meta.Hint

/-!
# Have-Rewrite Linter

The have-rewrite linter detects the pattern where a `have` introduces a hypothesis
that is immediately used in a `rw` and nothing else. This is a common pattern in
LLM-generated proofs that could often be simplified with `simp`.

## Example of flagged code:
```lean
example (a b c : Nat) (hab : a = b) (hbc : b = c) : a = c := by
  have h : a = b := hab
  rw [h]        -- Warning: have followed by rw using only that hypothesis
  exact hbc
```

## Suggested fix:
```lean
example (a b c : Nat) (hab : a = b) (hbc : b = c) : a = c := by
  simp only [hab]
  exact hbc
```
-/

open Lean Elab Command

namespace LintLlmProofs

/-- The have-rewrite linter emits a warning when a `have` introduces a hypothesis
that is immediately used in a `rw` (and nothing else). -/
register_option linter.haveRw : Bool := {
  defValue := false
  descr := "enable the have-rewrite linter"
}

namespace HaveRwLinter

/-- Check if syntax is a `have` tactic. -/
def isHaveTactic (stx : Syntax) : Bool :=
  if let `(tactic| have $_:letConfig $_:letDecl) := stx then true else false

/-- Check if syntax is a `rw` tactic by looking for the rw/rewrite keyword. -/
def isRwTactic (stx : Syntax) : Bool :=
  -- Check if there's an atom "rw" or "rewrite" in the syntax
  stx.getArgs.any fun arg =>
    if let .atom _ val := arg then
      val == "rw" || val == "rewrite"
    else
      false

/-- Extract identifier names from syntax. -/
partial def collectIdents (stx : Syntax) : Array Name :=
  if stx.isIdent then
    #[stx.getId]
  else
    stx.getArgs.foldl (fun acc child => acc ++ collectIdents child) #[]

/-- Extract the first identifier from a `have` tactic (the hypothesis name). -/
def getHaveHypName (stx : Syntax) : Option Name :=
  -- In `have h : T := e`, the identifier `h` is usually the first ident
  let idents := collectIdents stx
  -- Filter out common keywords and type-related names
  let filtered := idents.filter fun n =>
    !n.isAnonymous && n.toString != "have" && n.toString != "by"
  filtered[0]?

/-- Check if a `rw` uses only the given hypothesis name (no other terms). -/
def rwUsesOnlyHyp (rwStx : Syntax) (hypName : Name) : Bool :=
  let idents := collectIdents rwStx
  -- Filter to just user identifiers (not keywords)
  let userIdents := idents.filter fun n =>
    !n.isAnonymous &&
    n.toString != "rw" &&
    n.toString != "rewrite" &&
    n.toString != "at" &&
    !n.toString.startsWith "_"
  -- Check if the only user identifier is our hypothesis
  userIdents.size == 1 && userIdents.contains hypName

/-- Count how many times a name appears in a syntax tree (excluding the have that defines it). -/
partial def countUses (stx : Syntax) (name : Name) (excludeHave : Bool := false) : Nat :=
  if excludeHave && isHaveTactic stx then
    -- Don't count uses inside the have that defines the hypothesis
    0
  else if stx.isIdent && stx.getId == name then
    1
  else
    stx.getArgs.foldl (fun acc child => acc + countUses child name excludeHave) 0

/-- Flatten a tactic sequence into a list of individual tactics. -/
partial def flattenTactics (stx : Syntax) : Array Syntax :=
  if isHaveTactic stx || isRwTactic stx then
    #[stx]
  else if stx.getKind == ``Lean.Parser.Tactic.tacticSeq ||
          stx.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
    stx.getArgs.foldl (fun acc child => acc ++ flattenTactics child) #[]
  else
    stx.getArgs.foldl (fun acc child => acc ++ flattenTactics child) #[]

/-- Recursively search for := and return what follows. -/
partial def findBodyAfterAssign (stx : Syntax) : Option String := do
  let args := stx.getArgs
  for i in [0:args.size] do
    if let .atom _ val := args[i]! then
      if val == ":=" && i + 1 < args.size then
        let body := args[i + 1]!
        if body.isIdent then
          return body.getId.toString
        else
          return toString body.prettyPrint
    -- Recurse into children
    if let some result := findBodyAfterAssign args[i]! then
      return result
  none

/-- Extract the body/value expression from a have tactic.
    For `have h : T := e`, returns a string representation of `e`. -/
def getHaveBody (stx : Syntax) : Option String :=
  findBodyAfterAssign stx

/-- Find tactic sequences and check for have-rw patterns.
Only flags when the hypothesis is used ONLY in that one rw and nowhere else.
Returns (haveStx, rwStx) pairs. -/
partial def findHaveRwPatterns (stx : Syntax) : Array (Syntax × Syntax) := Id.run do
  let mut results := #[]

  -- Flatten all tactics in this syntax tree
  let tactics := flattenTactics stx

  -- Check consecutive pairs for have-rw pattern
  for i in [0:tactics.size] do
    if i + 1 < tactics.size then
      let tac1 := tactics[i]!
      let tac2 := tactics[i + 1]!
      if isHaveTactic tac1 && isRwTactic tac2 then
        if let some hypName := getHaveHypName tac1 then
          if rwUsesOnlyHyp tac2 hypName then
            -- Count total uses of the hypothesis in the remaining tactics
            -- If it's only used in this one rw, flag it
            let remainingTactics := tactics.toList.drop (i + 2)
            let usesAfterRw := remainingTactics.foldl (fun acc t => acc + countUses t hypName false) 0
            if usesAfterRw == 0 then
              results := results.push (tac1, tac2)

  return results

/-- Create a syntax node spanning from start of stx1 to end of stx2. -/
def mkSpanningSyntax (stx1 stx2 : Syntax) : Option Syntax := do
  let range1 ← stx1.getRange?
  let range2 ← stx2.getRange?
  return Syntax.ofRange ⟨range1.start, range2.stop⟩

/-- The have-rewrite linter: detects `have h := ...; rw [h]` patterns.

LLMs often spell out trivial rewrite steps that could be handled by `simp`.
This linter flags cases where a `have` introduces a hypothesis that is immediately
used in a `rw` and nothing else.
-/
def haveRwLinter : Linter where run := withSetOptionIn fun stx => do
  unless linter.haveRw.get (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for (haveStx, rwStx) in findHaveRwPatterns stx do
    let msg := m!"`have` immediately followed by `rw` using only that hypothesis."
    -- Extract the have body and generate rw [body]
    let body := getHaveBody haveStx |>.getD "_"
    let fixStr := s!"rw [{body}]"

    let suggestion : Meta.Hint.Suggestion := {
      suggestion := fixStr
      span? := mkSpanningSyntax haveStx rwStx
    }
    let hint ← liftCoreM <| MessageData.hint m!"Inline the expression." #[suggestion]
    Linter.logLint linter.haveRw haveStx (msg ++ hint)

initialize addLinter haveRwLinter

end HaveRwLinter
end LintLlmProofs
