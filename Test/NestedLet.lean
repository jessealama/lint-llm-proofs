import LintLlmProofs

set_option linter.nestedLet true

-- Should trigger warning: nested let
/--
warning: Nested `let` detected.

Hint: Hoist this `let` before the outer `let`.
  let y := 2

Note: This linter can be disabled with `set_option linter.nestedLet false`
-/
#guard_msgs in
example : True := by
  let x := 1 + by
    let y := 2
    exact 0
  trivial

-- Should NOT trigger warning: sequential lets at same level
#guard_msgs in
example : True := by
  let x := 1
  let y := 2
  trivial

-- Should NOT trigger warning: single let
#guard_msgs in
example : True := by
  let x := 1
  trivial

-- Should trigger warning: deeply nested let (flags both inner lets)
/--
warning: Nested `let` detected.

Hint: Hoist this `let` before the outer `let`.
  let y := 2 + by
        let z := 3
        exact 0

Note: This linter can be disabled with `set_option linter.nestedLet false`
---
warning: Nested `let` detected.

Hint: Hoist this `let` before the outer `let`.
  let z := 3

Note: This linter can be disabled with `set_option linter.nestedLet false`
-/
#guard_msgs in
example : True := by
  let x := 1 + by
    let y := 2 + by
      let z := 3
      exact 0
    exact 0
  trivial

-- Should NOT trigger warning: let inside have (mixed case)
#guard_msgs in
example : True := by
  have h : 1 = 1 := by
    let x := 1
    rfl
  trivial

-- Should NOT trigger warning: have inside let (mixed case)
#guard_msgs in
example : True := by
  let x := 1 + by
    have h : 1 = 1 := rfl
    exact 0
  trivial
