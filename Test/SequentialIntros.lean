import LintLlmProofs

set_option linter.sequentialIntros true
set_option linter.unusedVariables false

-- Should trigger warning: two consecutive intros
/--
warning: Sequential `intro` tactics detected.

Hint: Combine into single `intro`.
  intro x̵
  ̵ ̵ ̵i̵n̵t̵r̵o̵ ̵y̵

Note: This linter can be disabled with `set_option linter.sequentialIntros false`
-/
#guard_msgs in
example : ∀ x y : Nat, x = x := by
  intro x
  intro y
  rfl

-- Should trigger one warning: three consecutive intros (combined into one suggestion)
/--
warning: Sequential `intro` tactics detected.

Hint: Combine into single `intro`.
  intro x̵
  ̵ ̵ ̵i̵n̵t̵r̵o̵ ̵y̵
  ̵ ̵ ̵i̵n̵t̵r̵o̵ ̵z̵

Note: This linter can be disabled with `set_option linter.sequentialIntros false`
-/
#guard_msgs in
example : ∀ x y z : Nat, x = x := by
  intro x
  intro y
  intro z
  rfl

-- Should NOT trigger: single intro
#guard_msgs in
example : ∀ x : Nat, x = x := by
  intro x
  rfl

-- Should NOT trigger: combined intro
#guard_msgs in
example : ∀ x y z : Nat, x = x := by
  intro x y z
  rfl

-- Should NOT trigger: intro separated by other tactic (constructor creates new goals)
#guard_msgs in
example : ∀ x : Nat, (∀ y : Nat, y = y) ∧ (∀ z : Nat, z = z) := by
  intro x
  constructor
  intro y
  rfl
  intro z
  rfl
