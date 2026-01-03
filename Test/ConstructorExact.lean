import LintLlmProofs

set_option linter.constructorExact true

-- Should trigger warning: constructor followed by two exact
/--
warning: `constructor` followed by `exact` tactics.

Hint: Use anonymous constructor.
  c̵o̵n̵s̵t̵r̵u̵c̵t̵o̵r̵
  ̵ ̵ ̵e̵x̵a̵c̵t̵ ̵h̵1̵
  ̵ ̵ ̵e̵x̵a̵c̵t̵ ̵h̵2̵e̲x̲a̲c̲t̲ ̲⟨̲h̲1̲,̲ ̲h̲2̲⟩̲

Note: This linter can be disabled with `set_option linter.constructorExact false`
-/
#guard_msgs in
example (h1 : 1 = 1) (h2 : 2 = 2) : 1 = 1 ∧ 2 = 2 := by
  constructor
  exact h1
  exact h2

-- Should NOT trigger: just constructor without exact
#guard_msgs in
example (h1 : 1 = 1) (h2 : 2 = 2) : 1 = 1 ∧ 2 = 2 := by
  constructor
  · assumption
  · assumption

-- Should NOT trigger: already using anonymous constructor
#guard_msgs in
example (h1 : 1 = 1) (h2 : 2 = 2) : 1 = 1 ∧ 2 = 2 := by
  exact ⟨h1, h2⟩

-- Should NOT trigger: constructor with only one exact
#guard_msgs in
example (h1 : 1 = 1) : 1 = 1 ∧ 1 = 1 := by
  constructor
  exact h1
  assumption

-- Should NOT trigger: exact followed by non-exact
#guard_msgs in
example (h1 : 1 = 1) (h2 : 2 = 2) : 1 = 1 ∧ 2 = 2 := by
  constructor
  exact h1
  assumption
