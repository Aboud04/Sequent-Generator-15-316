# Sequent Calculus Proof Assistant — with Authorization Logic

A Python/Tkinter GUI application for constructing formal proofs using **sequent calculus**, extended with **authorization logic** from CMU 15-316 Lectures 15–17. Also includes an automated proof search engine (`sequent_generator.py`).

![Python](https://img.shields.io/badge/Python-3.12-blue)
![Tkinter](https://img.shields.io/badge/GUI-Tkinter-green)

## Installation & Running

```bash
git clone https://github.com/Aboud04/Sequent-Generator-15-316.git
cd Sequent-Generator-15-316
python sequentGen.py
```

**Requirements**: Python 3.12+ with Tkinter (included in standard Python).

## Complete Rule Reference

The GUI has **6 tabs** of rules. Here is every rule across all tabs:

### Tab 1: 📐 Propositional Rules

| Rule | Side | Behavior | Lecture |
|------|------|----------|---------|
| ∧L | LHS | Split conjunction: Γ, P ∧ Q ⊢ Δ → Γ, P, Q ⊢ Δ | 15 |
| ∧R | RHS | Branch: Γ ⊢ P ∧ Q → Γ ⊢ P and Γ ⊢ Q | 15 |
| ∨L | LHS | Branch: Γ, P ∨ Q ⊢ Δ → Γ, P ⊢ Δ and Γ, Q ⊢ Δ | 15 |
| ∨R | RHS | Classical split (keeps both disjuncts in succedent) | — |
| →L | LHS | Branch: Γ, P→Q ⊢ Δ → Γ ⊢ P and Γ, Q ⊢ Δ | 15 |
| →R | RHS | Move antecedent: Γ ⊢ P→Q → Γ, P ⊢ Q | 15 |
| ¬L/¬R | Both | Negation decomposition | — |
| ↔L/↔R | Both | Bi-implication decomposition | — |
| ⊥L | LHS | Close branch (ex falso) | — |
| ⊤R | RHS | Close branch (trivially true) | — |

### Tab 2: ∀∃ Quantifier Rules

| Rule | Behavior | Lecture |
|------|----------|---------|
| ∀R | Introduce fresh variable y: Γ ⊢ ∀x.P(x) → Γ ⊢ P(y) | 15 |
| ∀L | Instantiate with term: Γ, ∀x.P(x) ⊢ Δ → Γ, P(c) ⊢ Δ | 15 |
| ∃R | Instantiate with term | — |
| ∃L | Introduce fresh variable | — |

### Tab 3: [α] Dynamic Logic Rules

Assignment, test, sequence, choice, loop, conditional, while, for rules.

### Tab 4: ⚙ Structural Rules

| Rule | Behavior | Lecture |
|------|----------|---------|
| WL/WR | Weakening — add unused formula | — |
| CL/CR | Contraction — remove duplicate | — |
| Cut | Lemma introduction: Γ ⊢ Δ from Γ ⊢ P and Γ, P ⊢ Δ | 16 |
| Identity | Close branch when same formula on both sides | 15 |

### Tab 5: 🔐 Auth Logic (Lectures 15-17)

**This is the new tab.** All rules from the authorization logic lectures:

| Rule | Behavior | Lecture |
|------|----------|---------|
| **saysR** | Γ ⊢ A says P → Γ ⊢ A aff P | 15 |
| **saysL** | Γ, A says P ⊢ A aff Q → Γ, P ⊢ A aff Q (same principal) | 15 |
| **aff** | Γ ⊢ A aff P → Γ ⊢ P (drop affirmation) | 15 |
| **∨R₁** | Γ ⊢ P ∨ Q → Γ ⊢ P (intuitionistic: pick left disjunct only) | 15 |
| **∨R₂** | Γ ⊢ P ∨ Q → Γ ⊢ Q (intuitionistic: pick right disjunct only) | 15 |
| **≤-says** | Rewrite B says P → A says P on LHS when trust A ≤ B holds | — |
| **Set trust** | Declare a trust relationship A ≤ B | — |
| **cut'** | Split-context cut: Γ₁,Γ₂ ⊢ δ from Γ₁ ⊢ P and Γ₂,P ⊢ δ | 16 |

**Note on Lecture 16 focusing rules:** The focusR, focusL, blurR, blurL rules from Lecture 16 are **proof search strategy rules** that control which formula to decompose next. They are not user-applied inference rules — they govern the order of rule application in automated search. The automated prover in `sequent_generator.py` implements them internally.

**Note on Lecture 17:** Lecture 17 defines **proof term annotations** on all existing rules (λx.M for →R, ⟨M,N⟩ for ∧R, {M}_A for saysR, etc.) — it does not introduce new inference rules. The automated prover generates these proof terms.

### Tab 6: ✨ Custom Rules

User-defined rules saved to `custom_rules.json`.

## Input Syntax

### Propositional & Quantifier Logic
```
p implies q, p |- q
p and q |- p
not (A or B) |- not A and not B
forall x. P |- P
```

### Authorization Logic (NEW)
```
admin says p |- admin says p
admin says (p -> q), admin says p |- admin says q
admin aff p |- p
fp says studentOf(hemant, fp) |- fp says studentOf(hemant, fp)
```

The `says` and `aff` keywords bind to the identifier immediately before them:
- `admin says P` parses as `(admin says P)` — admin is the principal
- `admin says (P -> Q)` — use parentheses for complex inner formulas
- `admin aff P` parses as `(admin aff P)`

### Trust Relationships

Trust is declared at runtime via the **Set trust...** button (not in the sequent syntax). Click it and enter `admin <= fp` to declare that admin trusts fp. Then use **≤-says** to apply the trust relationship.

## Walkthrough: Proving admin says Q from admin says (P→Q) and admin says P

1. Enter: `admin says (p -> q), admin says p |- admin says q`
2. Click **▶ Start Proof**
3. Select `(admin says q)` on RHS → click **saysR** → goal becomes `admin aff q`
4. Select `(admin says (p -> q))` on LHS → click **saysL** → unwraps to `(p -> q)`
5. Select `(admin says p)` on LHS → click **saysL** → unwraps to `p`
6. Select `(admin aff q)` on RHS → click **aff** → goal becomes `q`
7. Select `(p -> q)` on LHS → click **→L** → branches into `⊢ p` and `q ⊢ q`
8. Close both branches with **Identity**

## Project Structure

```
Sequent-Generator-15-316/
├── sequentGen.py              # GUI application (Tkinter) — all rules
├── sequent_generator.py       # Automated prover — auth logic proof search
├── test.py                    # Original unit tests (41 tests)
├── tests/
│   ├── test_rules.py          # Auth logic pytest tests (45 tests)
│   ├── generate_latex_tests.py
│   └── latex/
│       └── test_all_rules.tex # 23-section LaTeX verification document
├── README.md
└── How_To_Guide.tex
```

## Running Tests

```bash
# Original GUI tests
python -m unittest test -v

# Authorization logic tests
python -m pytest tests/test_rules.py -v

# LaTeX compilation
cd tests/latex && pdflatex test_all_rules.tex
```

## License

MIT License

## Acknowledgments

- CMU 15-316 Software Foundations of Security & Privacy
- Frank Pfenning's lecture notes (Lectures 15–17)
