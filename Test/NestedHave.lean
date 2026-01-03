import LintLlmProofs

set_option linter.nestedHave true

-- Should trigger warning: nested have
/--
warning: Nested `have` detected.

Hint: Hoist this `have` before the outer `have`.
  have h2 : 2 = 2 := rfl

Note: This linter can be disabled with `set_option linter.nestedHave false`
-/
#guard_msgs in
example : True := by
  have h1 : 1 = 1 := by
    have h2 : 2 = 2 := rfl
    rfl
  trivial

-- Should NOT trigger warning: sequential haves at same level
#guard_msgs in
example : True := by
  have h1 : 1 = 1 := rfl
  have h2 : 2 = 2 := rfl
  trivial

-- Should NOT trigger warning: single have
#guard_msgs in
example : True := by
  have h1 : 1 = 1 := rfl
  trivial

-- Should trigger warning: deeply nested have (flags both inner haves)
/--
warning: Nested `have` detected.

Hint: Hoist this `have` before the outer `have`.
  have h2 : 2 = 2 := by
        have h3 : 3 = 3 := rfl
        rfl

Note: This linter can be disabled with `set_option linter.nestedHave false`
---
warning: Nested `have` detected.

Hint: Hoist this `have` before the outer `have`.
  have h3 : 3 = 3 := rfl

Note: This linter can be disabled with `set_option linter.nestedHave false`
-/
#guard_msgs in
example : True := by
  have h1 : 1 = 1 := by
    have h2 : 2 = 2 := by
      have h3 : 3 = 3 := rfl
      rfl
    rfl
  trivial
