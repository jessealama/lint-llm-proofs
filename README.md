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

## License

MIT
