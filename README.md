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

## License

MIT
