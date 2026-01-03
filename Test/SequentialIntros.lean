import LintLlmProofs

set_option linter.sequentialIntros true
set_option linter.unusedVariables false

-- Should trigger warning: two consecutive intros
/--
warning: Sequential `intro` tactics detected. Consider combining into a single `intro x y z`.

Note: This linter can be disabled with `set_option linter.sequentialIntros false`
-/
#guard_msgs in
example : ∀ x y : Nat, x = x := by
  intro x
  intro y
  rfl

-- Should trigger two warnings: three consecutive intros
/--
warning: Sequential `intro` tactics detected. Consider combining into a single `intro x y z`.

Note: This linter can be disabled with `set_option linter.sequentialIntros false`
---
warning: Sequential `intro` tactics detected. Consider combining into a single `intro x y z`.

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
