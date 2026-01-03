# LintLLMProofs

Lean 4 linters for detecting patterns typical of LLM-generated proofs.

## Installation

Add to your `lakefile.toml`:
```toml
[[require]]
name = "lintLlmProofs"
git = "https://github.com/jessealama/lint-llm-proofs"
rev = "main"
```

Or if using `lakefile.lean`:
```lean
require lintLlmProofs from git
  "https://github.com/jessealama/lint-llm-proofs" @ "main"
```

## Available Linters

### Nested Have Linter (`linter.nestedHave`)

Detects nested `have` statements where a `have`'s proof contains another `have`.
LLMs often produce deeply nested `have` chains instead of flattening them.

**Enable:**
```lean
import LintLlmProofs
set_option linter.nestedHave true
```

**Example flagged code:**
```lean
example : True := by
  have h1 : 1 = 1 := by
    have h2 : 2 = 2 := rfl  -- Warning: nested have
    rfl
  trivial
```

**Suggested fix:**
```lean
example : True := by
  have h2 : 2 = 2 := rfl  -- Hoisted
  have h1 : 1 = 1 := rfl
  trivial
```

### Have-Rewrite Linter (`linter.haveRw`)

Detects when a `have` introduces a hypothesis that is immediately used in a `rw`
and nothing else. This verbose pattern could often be simplified with `simp`.

**Enable:**
```lean
import LintLlmProofs
set_option linter.haveRw true
```

**Example flagged code:**
```lean
example (a b c : Nat) (hab : a = b) (hbc : b = c) : a = c := by
  have h : a = b := hab
  rw [h]        -- Warning: have followed by rw using only that hypothesis
  exact hbc
```

**Suggested fix:**
```lean
example (a b c : Nat) (hab : a = b) (hbc : b = c) : a = c := by
  simp only [hab]
  exact hbc
```

### Simp-Rfl Redundancy Linter (`linter.simpRfl`)

Detects when `simp` is immediately followed by `rfl` or `exact rfl`. If `simp`
succeeds, it should close reflexivity goals. The trailing `rfl` is either
redundant or indicates `simp` didn't fully work.

**Enable:**
```lean
import LintLlmProofs
set_option linter.simpRfl true
```

**Example flagged code:**
```lean
example (a : Nat) : a + 0 = a := by
  simp
  rfl  -- Warning: redundant after simp
```

**Suggested fix:**
```lean
example (a : Nat) : a + 0 = a := by
  simp
```

### Sequential Intros Linter (`linter.sequentialIntros`)

Detects when multiple `intro` tactics appear consecutively instead of being
combined into a single `intro x y z`.

**Enable:**
```lean
import LintLlmProofs
set_option linter.sequentialIntros true
```

**Example flagged code:**
```lean
example : forall x y z : Nat, x = x := by
  intro x
  intro y  -- Warning: sequential intro
  intro z  -- Warning: sequential intro
  rfl
```

**Suggested fix:**
```lean
example : forall x y z : Nat, x = x := by
  intro x y z
  rfl
```

### Constructor-Exact Pattern Linter (`linter.constructorExact`)

Detects when `constructor` is followed by two `exact` tactics for simple
pair/And constructions. This verbose pattern could be replaced with
anonymous constructor syntax `⟨h1, h2⟩`.

**Enable:**
```lean
import LintLlmProofs
set_option linter.constructorExact true
```

**Example flagged code:**
```lean
example (h1 : P) (h2 : Q) : P ∧ Q := by
  constructor     -- Warning: could use ⟨_, _⟩
  exact h1
  exact h2
```

**Suggested fix:**
```lean
example (h1 : P) (h2 : Q) : P ∧ Q := by
  exact ⟨h1, h2⟩
```

## License

MIT
