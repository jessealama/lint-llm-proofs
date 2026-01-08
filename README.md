# LintLLMProofs

Lean 4 linters for detecting patterns typical of LLM-generated proofs, with automatic fix suggestions.

## Features

- Detects 6 common LLM proof anti-patterns
- **Auto-fix support**: Clickable suggestions in any LSP-compatible editor (VS Code, Emacs, Neovim, etc.)
- All linters disabled by default for opt-in usage
- Configurable per-file, per-section, or project-wide

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

Then run `lake update`.

## Usage

### Enabling Linters

All linters are disabled by default. Enable them with `set_option`:

```lean
import LintLlmProofs

set_option linter.nestedHave true
set_option linter.nestedLet true
set_option linter.haveRw true
set_option linter.simpRfl true
set_option linter.sequentialIntros true
set_option linter.constructorExact true
```

### Scoped Configuration

Enable for a specific section:
```lean
section MyProofs
  set_option linter.sequentialIntros true
  -- linter active here
end MyProofs
-- linter inactive here
```

Disable for a specific declaration:
```lean
set_option linter.nestedHave true  -- enabled for file

set_option linter.nestedHave false in
example : True := by  -- no warning here
  have h1 := by have h2 := rfl; rfl
  trivial
```

### Project-Wide Configuration

Add to your `lakefile.toml` to enable linters for all files:

```toml
[[lean_lib]]
name = "MyProject"
moreLeanArgs = [
  "-Dlinter.nestedHave=true",
  "-Dlinter.nestedLet=true",
  "-Dlinter.simpRfl=true",
  "-Dlinter.sequentialIntros=true",
  "-Dlinter.constructorExact=true",
  "-Dlinter.haveRw=true"
]
```

### Command-Line Usage

Run linters on a single file:
```bash
lake env lean -Dlinter.nestedHave=true MyProject/MyFile.lean
```

## Auto-Fix Support

All linters provide clickable auto-fix suggestions via Lean 4's LSP code actions. In supported editors:

1. Hover over the warning to see the suggested fix with an inline diff
2. Click the suggestion or use the editor's "Quick Fix" action (lightbulb menu)
3. The fix is applied automatically

The diff display shows deletions with strikethrough and insertions underlined.

## Available Linters

| Linter | Option | Pattern | Auto-Fix |
|--------|--------|---------|----------|
| Nested Have | `linter.nestedHave` | `have` inside `have` body | Hoist inner `have` |
| Nested Let | `linter.nestedLet` | `let` inside `let` body | Hoist inner `let` |
| Have-Rewrite | `linter.haveRw` | `have h := e; rw [h]` | `rw [e]` |
| Simp-Rfl | `linter.simpRfl` | `simp; rfl` | Remove `rfl` |
| Sequential Intros | `linter.sequentialIntros` | `intro x; intro y` | `intro x y` |
| Constructor-Exact | `linter.constructorExact` | `constructor; exact a; exact b` | `exact ⟨a, b⟩` |

### Nested Have (`linter.nestedHave`)

Detects nested `have` statements. LLMs often produce deeply nested chains instead of flattening them.

```lean
-- Flagged:
example : True := by
  have h1 : 1 = 1 := by
    have h2 : 2 = 2 := rfl  -- Warning
    rfl
  trivial

-- Suggested:
example : True := by
  have h2 : 2 = 2 := rfl
  have h1 : 1 = 1 := rfl
  trivial
```

### Nested Let (`linter.nestedLet`)

Detects nested `let` statements. Similar to nested `have`, LLMs sometimes produce deeply nested `let` chains.

```lean
-- Flagged:
example : True := by
  let x := 1 + by
    let y := 2  -- Warning
    exact 0
  trivial

-- Suggested:
example : True := by
  let y := 2
  let x := 1
  trivial
```

### Have-Rewrite (`linter.haveRw`)

Detects `have h := e; rw [h]` where `h` is only used once.

```lean
-- Flagged:
example (hab : a = b) (hbc : b = c) : a = c := by
  have h : a = b := hab
  rw [h]  -- Warning
  exact hbc

-- Suggested:
example (hab : a = b) (hbc : b = c) : a = c := by
  rw [hab]
  exact hbc
```

### Simp-Rfl (`linter.simpRfl`)

Detects redundant `rfl` after `simp`.

```lean
-- Flagged:
example (a : Nat) : a + 0 = a := by
  simp
  rfl  -- Warning: redundant

-- Suggested:
example (a : Nat) : a + 0 = a := by
  simp
```

### Sequential Intros (`linter.sequentialIntros`)

Detects consecutive `intro` tactics that should be combined.

```lean
-- Flagged:
example : forall x y z : Nat, x = x := by
  intro x
  intro y  -- Warning
  intro z
  rfl

-- Suggested:
example : forall x y z : Nat, x = x := by
  intro x y z
  rfl
```

### Constructor-Exact (`linter.constructorExact`)

Detects verbose pair construction.

```lean
-- Flagged:
example (h1 : P) (h2 : Q) : P ∧ Q := by
  constructor  -- Warning
  exact h1
  exact h2

-- Suggested:
example (h1 : P) (h2 : Q) : P ∧ Q := by
  exact ⟨h1, h2⟩
```

## Development

```bash
lake build        # Build library
lake build Test   # Run tests (uses #guard_msgs)
```

## License

MIT
