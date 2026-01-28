# Sequent Calculus Proof Assistant

A Python/Tkinter GUI application for constructing formal proofs using **sequent calculus**. Designed for CMU 15-316 Software Security course, supporting propositional logic, first-order logic, and dynamic logic.

![Python](https://img.shields.io/badge/Python-3.x-blue)
![Tkinter](https://img.shields.io/badge/GUI-Tkinter-green)
![Tests](https://img.shields.io/badge/tests-41%20passing-brightgreen)

> 📖 **New User?** Check out the comprehensive **[How To Guide](How_To_Guide.md)** for step-by-step instructions!

## Features

### Logic Systems Supported
- **Propositional Logic**: ∧, ∨, →, ¬, ↔, ⊤, ⊥
- **First-Order Logic**: ∀ (forall), ∃ (exists) with term substitution
- **Dynamic Logic**: Box modality [α]P for program verification
  - Assignment `[x := e]P`
  - Test `[?P]Q`
  - Skip `[skip]P`
  - Sequential composition `[α; β]P`
  - Non-deterministic choice `[α ∪ β]P`
  - Iteration `[α*]P`
  - Conditionals `[if P then α else β]Q`
  - While loops `[while P do α]Q` with invariant support
  - Bounded for loops `[for 0 ≤ i < n do α]Q`

### User Interface
- **Tabbed Rule Organization**: 5 tabs organizing 30+ inference rules
- **Interactive Proof Tree**: Visual representation of proof structure
- **LaTeX Export**: Export proofs for academic papers
- **Custom Rules**: Define and save your own inference rules

## Installation

```bash
# Clone the repository
git clone https://github.com/yourusername/Sequent-Generator-15-316.git
cd Sequent-Generator-15-316

# Create virtual environment (optional but recommended)
python -m venv .venv
.venv\Scripts\activate  # Windows
source .venv/bin/activate  # macOS/Linux

# Run the application
python sequentGen.py
```

**Requirements**: Python 3.x with Tkinter (included in standard library)

## Usage

### Basic Workflow
1. **Enter a sequent** in the input field using the syntax below
2. **Click "▶ Start Proof"** to begin
3. **Select a formula** from the LHS or RHS listbox
4. **Apply a rule** from the appropriate tab
5. **Repeat** until all branches are closed (marked with ✔)

### Input Syntax

```
# Propositional Logic
p implies q, p |- q
p and q |- p
not (A or B) |- not A and not B
A iff B |- A implies B

# First-Order Logic
forall x. P |- exists y. P
∀x. Human(x) -> Mortal(x), Human(socrates) |- Mortal(socrates)

# Dynamic Logic
[x := 5]x = 5 |- true
[?x > 0]y = x |- x > 0 implies y = x
[a; b]P |- [a][b]P
[skip]P |- P
[skip; a]Q |- [a]Q
[for 0 <= i < n do x := i]P |- Q
```

### Keyboard Shortcuts
- **Enter**: Start proof (when in input field)

## Rule Reference

### Tab 1: 📐 Propositional Rules
| Rule | LHS/RHS | Behavior |
|------|---------|----------|
| ∧L | LHS | Split conjunction |
| ∧R | RHS | Branch (prove both) |
| ∨L | LHS | Branch (prove both) |
| ∨R | RHS | Split disjunction |
| →L | LHS | Branch (antecedent/consequent) |
| →R | RHS | Move antecedent to LHS |
| ¬L | LHS | Move negated formula to RHS |
| ¬R | RHS | Move inner formula to LHS |
| ↔L/R | Both | Bi-implication decomposition |
| ⊥L | LHS | Close if ⊥ present |
| ⊤R | RHS | Close if ⊤ present |

### Tab 2: ∀∃ Quantifier Rules
| Rule | Description |
|------|-------------|
| ∀R | Introduce fresh variable |
| ∀L | Instantiate with term (prompted) |
| ∃R | Instantiate with term (prompted) |
| ∃L | Introduce fresh variable |

### Tab 3: [α] Dynamic Logic Rules
| Rule | Program Type | Result |
|------|--------------|--------|
| [:=]R | Assignment | Add equality, substitute |
| [?]L/R | Test | Move guard to LHS / branch |
| [skip]L/R | Skip | Remove skip, keep postcondition |
| [;]L/R | Sequence | Nest modalities |
| [∪]R | Choice | Branch for each option |
| [*]unfold | Loop | Branch: exit or iterate |
| [if]R | Conditional | Branch on guard |
| [while]unfold | While | Branch on guard |
| [while]inv | While with invariant | 3 branches (init, preserve, exit) |
| [for]R | Bounded for loop | Desugar to while loop |

### Tab 4: ⚙ Structural Rules
| Rule | Description |
|------|-------------|
| WL/WR | Weakening - add formula |
| CL/CR | Contraction - remove duplicate |
| Cut | Introduce lemma |

### Tab 5: ✨ Custom Rules

Create your own rules for domain-specific reasoning:

1. Click **"+ Add Rule"**
2. Configure the rule:
   - **Name**: Unique identifier
   - **Side**: LHS or RHS
   - **Type**: Unary (1 branch), Binary (2 branches), or Close
3. Use **placeholders** in formulas:
   - `LEFT` - left operand of binary formula
   - `RIGHT` - right operand of binary formula
   - `INNER` - inner formula of negation
   - `FORMULA` - the entire selected formula
4. Rules are **saved automatically** to `custom_rules.json`

## Running Tests

```bash
python -m unittest test -v
```

All 41 tests cover:
- Propositional rules (∧, ∨, →, ¬, ↔, ⊤, ⊥)
- Quantifier rules (∀, ∃)
- Dynamic logic rules ([:=], [?], [;], [∪], [*], [skip], [if], [while], [for])
- While loop with invariant ([while]inv - 3 branch proof)
- Structural rules (W, C, Cut)
- Parser for all formula types
- Complete proof verification (e.g., `⊢ [skip;α]Q ↔ [α]Q`)

## LaTeX Export

Click **"⬇ Export LaTeX"** to generate proof tree code:

```latex
\begin{rules}
\infer[\ms{→R}]
  {p \to q \vdash p \to q}
  {
    \infer[\ms{id}]
      {p, p \to q \vdash q}
      {}
  }
\end{rules}
```

## Project Structure

```
Sequent-Generator-15-316/
├── sequentGen.py       # Main application (2200+ lines)
├── test.py             # Unit tests (41 tests)
├── How_To_Guide.md     # 📖 Comprehensive user guide with examples
├── custom_rules.json   # User-defined rules (auto-generated)
├── README.md           # This file
├── Notes To Reference/ # PDF lecture notes for rule reference
│   ├── 02-prop.pdf        # Propositional logic rules
│   ├── 03-dynamiclogic.pdf # Dynamic logic (box modality, programs)
│   ├── 04-semantics.pdf    # Semantics reference
│   ├── 05-safety.pdf       # Safety proofs
│   └── 06-memsafety.pdf    # Memory safety
└── .github/
    └── copilot-instructions.md  # Developer documentation
```

> **📚 Developer Note**: Always check the `Notes To Reference/` folder for PDF lecture notes containing formal rule definitions and examples. These PDFs are the authoritative source for sequent calculus rules in 15-316.

## Contributing

1. Fork the repository
2. Create a feature branch
3. Add tests for new functionality
4. Ensure all tests pass
5. Submit a pull request

## License

MIT License - see LICENSE file for details.

## Acknowledgments

- CMU 15-316 Software Security course materials
- Sequent calculus formalization from lecture notes
