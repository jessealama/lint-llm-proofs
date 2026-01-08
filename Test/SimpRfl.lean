import LintLlmProofs

set_option linter.simpRfl true

-- Should trigger warning: simp followed by rfl (with error since rfl is redundant)
/--
error: No goals to be solved
---
warning: `rfl` immediately after `simp` is often redundant.

Hint: Remove the redundant `rfl`.
  simp
  ̵ ̵ ̵r̵f̵l̵

Note: This linter can be disabled with `set_option linter.simpRfl false`
-/
#guard_msgs in
example (a : Nat) : a + 0 = a := by
  simp
  rfl

-- Should NOT trigger: just simp alone that closes the goal
#guard_msgs in
example (a : Nat) : a + 0 = a := by
  simp

-- Should NOT trigger: rfl without simp before it
#guard_msgs in
example : 1 = 1 := by
  rfl

-- Should NOT trigger: tactic between simp and rfl
#guard_msgs in
example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp only [Nat.add_zero]
  exact h

-- Should NOT trigger: simp; left; rfl (rfl does not immediately follow simp)
-- Note: The example has a Lean error, but no linter warning should appear
/--
error: No goals to be solved
-/
#guard_msgs in
example (a : Nat) : a + 0 = a ∨ False := by
  simp
  left
  rfl

-- Should NOT trigger: semicolon style with intervening tactic
-- Note: The example has a Lean error, but no linter warning should appear
/--
error: No goals to be solved
-/
#guard_msgs in
example (a : Nat) : a + 0 = a ∨ False := by
  simp; left; rfl

-- Should trigger: semicolon style with simp immediately followed by rfl
/--
error: No goals to be solved
---
warning: `rfl` immediately after `simp` is often redundant.

Hint: Remove the redundant `rfl`.
  simp;̵ ̵r̵f̵l̵

Note: This linter can be disabled with `set_option linter.simpRfl false`
-/
#guard_msgs in
example (a : Nat) : a + 0 = a := by
  simp; rfl
