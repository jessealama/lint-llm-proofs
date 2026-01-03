import LintLlmProofs

set_option linter.haveRw true

-- Should trigger warning: have followed by rw using only that hypothesis
/--
warning: `have` immediately followed by `rw` using only that hypothesis.

Hint: Inline the expression.
  h̵a̵v̵e̵ ̵h̵ ̵:̵ ̵a̵ ̵=̵ ̵b̵ ̵:̵=̵ ̵h̵a̵b̵
  ̵ ̵ ̵r̵w̵ ̵[̵h̵]̵r̲w̲ ̲[̲h̲a̲b̲]̲

Note: This linter can be disabled with `set_option linter.haveRw false`
-/
#guard_msgs in
example (a b c : Nat) (hab : a = b) (hbc : b = c) : a = c := by
  have h : a = b := hab
  rw [h]
  exact hbc

-- Should NOT trigger: rw uses multiple hypotheses
#guard_msgs in
example (a b c : Nat) (hab : a = b) (hbc : b = c) : a = c := by
  have h : a = b := hab
  rw [h, hbc]

-- Should NOT trigger: no have before rw
#guard_msgs in
example (a b : Nat) (hab : a = b) : a = b := by
  rw [hab]

-- Should NOT trigger: rw doesn't use the have hypothesis
#guard_msgs in
example (a b c : Nat) (hab : a = b) (hbc : b = c) : a = c := by
  have _h : a = b := hab
  rw [hab]
  exact hbc

-- Should NOT trigger: hypothesis is used again later (in show)
#guard_msgs in
example (a b c : Nat) (hab : a = b) (hbc : b = c) : a = c := by
  have h : a = b := hab
  rw [h]
  show b = c
  have _use_h_again : a = b := h
  exact hbc
