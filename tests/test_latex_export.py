#!/usr/bin/env python3
"""Exhaustive tests for LaTeX export of authorization logic rules.

Tests both:
  - sequent_generator.py  (proof_to_latex, Formula.to_latex, rule labels)
  - The generated test_all_rules.tex (section count, compilation)
"""

import os
import re
import subprocess
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from sequent_generator import (
    Atom, Not, And, Or, Implies, Forall, Exists, Top, Bottom,
    Principal, Says, Aff, TrustLeq, TrustContext,
    Sequent, Proof,
    prove, proof_to_latex, proof_to_latex_document,
    reset_fresh_counter, grey_system_sequent,
    INVERTIBLE_RULES, NON_INVERTIBLE_RULES,
)
import sequent_generator as sg


LATEX_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "latex")


# ============================================================================
# Part 1: proof_to_latex output for every rule
# ============================================================================

class TestProofToLatex(unittest.TestCase):
    """Verify LaTeX output for all authorization-logic sequent proofs."""

    def _prove(self, seq, trust=None):
        reset_fresh_counter()
        proof = prove(seq, trust=trust, max_depth=50)
        self.assertIsNotNone(proof, f"Failed to prove: {seq}")
        return proof

    # --- 1. Identity ---
    def test_identity(self):
        proof = self._prove(Sequent([Atom('p')], Atom('p')))
        self.assertEqual(proof.rule, "id")
        tex = proof_to_latex(proof)
        self.assertIn(r"\infer[\ms{id}]", tex)
        self.assertNotIn(r"\infer-", tex)
        self.assertIn(r"p \vdash p", tex)

    # --- 2. →R ---
    def test_implies_right(self):
        proof = self._prove(Sequent([], Implies(Atom('p'), Atom('p'))))
        tex = proof_to_latex(proof)
        self.assertIn(r"\infer-[{\arrow}R]", tex)
        self.assertIn(r"\vdash (p \arrow p)", tex)

    # --- 3. →L ---
    def test_implies_left(self):
        seq = Sequent(
            [Implies(Atom('p'), Atom('q')), Implies(Atom('q'), Atom('r'))],
            Implies(Atom('p'), Atom('r')))
        proof = self._prove(seq)
        tex = proof_to_latex(proof)
        self.assertIn(r"[{\arrow}L]", tex)
        self.assertIn(r"\infer[{\arrow}L]", tex)  # solid line (non-invertible)

    # --- 4. ∧R ---
    def test_and_right(self):
        proof = self._prove(Sequent([Atom('p'), Atom('q')],
                                    And(Atom('p'), Atom('q'))))
        self.assertEqual(proof.rule, "∧R")
        tex = proof_to_latex(proof)
        self.assertIn(r"\infer-[{\land}R]", tex)
        self.assertIn(r"(p \land q)", tex)

    # --- 5. ∧L ---
    def test_and_left(self):
        proof = self._prove(Sequent([And(Atom('p'), Atom('q'))],
                                    And(Atom('q'), Atom('p'))))
        tex = proof_to_latex(proof)
        self.assertIn(r"\infer-[{\land}L]", tex)

    # --- 6. ∨R₁ ---
    def test_or_right_1(self):
        proof = self._prove(Sequent([Atom('p')], Or(Atom('p'), Atom('q'))))
        self.assertEqual(proof.rule, "∨R₁")
        tex = proof_to_latex(proof)
        self.assertIn(r"\infer[{\lor}R_1]", tex)
        self.assertNotIn(r"\infer-[{\lor}R_1]", tex)

    # --- 7. ∨R₂ ---
    def test_or_right_2(self):
        proof = self._prove(Sequent([Atom('q')], Or(Atom('p'), Atom('q'))))
        self.assertEqual(proof.rule, "∨R₂")
        tex = proof_to_latex(proof)
        self.assertIn(r"\infer[{\lor}R_2]", tex)
        self.assertNotIn(r"\infer-[{\lor}R_2]", tex)

    # --- 8. ∨L ---
    def test_or_left(self):
        proof = self._prove(Sequent([Or(Atom('p'), Atom('q'))],
                                    Or(Atom('q'), Atom('p'))))
        tex = proof_to_latex(proof)
        self.assertIn(r"\infer-[{\lor}L]", tex)

    # --- 9. saysR ---
    def test_says_right(self):
        admin = Principal('admin')
        proof = self._prove(Sequent([Atom('P')], Says(admin, Atom('P'))))
        tex = proof_to_latex(proof)
        self.assertIn(r"\infer-[{\mb{says}}R]", tex)
        self.assertIn(r"\mi{admin} \says P", tex)

    # --- 10. saysL ---
    def test_says_left(self):
        admin = Principal('admin')
        proof = self._prove(
            Sequent([Says(admin, Atom('P'))], Aff(admin, Atom('P'))))
        tex = proof_to_latex(proof)
        self.assertIn(r"\infer-[{\mb{says}}L]", tex)
        self.assertIn(r"\mi{admin} \aff P", tex)

    # --- 11. aff ---
    def test_aff(self):
        admin = Principal('admin')
        proof = self._prove(Sequent([Atom('P')], Aff(admin, Atom('P'))))
        self.assertEqual(proof.rule, "aff")
        tex = proof_to_latex(proof)
        self.assertIn(r"\infer[\mb{aff}]", tex)
        self.assertNotIn(r"\infer-[\mb{aff}]", tex)

    # --- 12. Trust (≤-says) ---
    def test_trust(self):
        admin = Principal('admin')
        fp = Principal('fp')
        trust = TrustContext()
        trust.add(admin, fp)
        proof = self._prove(
            Sequent([Says(fp, Atom('P'))], Says(admin, Atom('P'))),
            trust=trust)
        tex = proof_to_latex(proof)
        self.assertIn(r"\leq\mbox{-}\mb{says}", tex)
        self.assertIn(r"\mi{fp} \says P", tex)
        self.assertIn(r"\mi{admin} \says P", tex)

    # --- 13. HW5-1 ---
    def test_hw5_1(self):
        A = Principal('A')
        proof = self._prove(Sequent(
            [And(Says(A, Atom('P')), Says(A, Atom('Q')))],
            Says(A, And(Atom('P'), Atom('Q')))))
        tex = proof_to_latex(proof)
        self.assertIn(r"{\mb{says}}R", tex)
        self.assertIn(r"{\mb{says}}L", tex)
        self.assertIn(r"{\land}R", tex)
        self.assertIn(r"{\land}L", tex)

    # --- 14. HW5-2 ---
    def test_hw5_2(self):
        A = Principal('A')
        proof = self._prove(Sequent(
            [Says(A, And(Atom('P'), Atom('Q')))],
            And(Says(A, Atom('P')), Says(A, Atom('Q')))))
        tex = proof_to_latex(proof)
        self.assertIn(r"{\land}R", tex)
        self.assertIn(r"{\mb{says}}R", tex)
        self.assertIn(r"{\mb{says}}L", tex)

    # --- 15. Grey system ---
    def test_grey_system(self):
        admin = Principal('admin')
        fp = Principal('fp')
        hemant = Principal('hemant')
        reset_fresh_counter()
        grey = grey_system_sequent(admin, fp, hemant)
        proof = prove(grey, max_depth=50)
        self.assertIsNotNone(proof, "Grey system proof failed")
        tex = proof_to_latex(proof)
        self.assertIn(r"\ms{mayOpen}", tex)
        self.assertIn(r"\ms{owns}", tex)
        self.assertIn(r"\mi{admin}", tex)
        self.assertIn(r"\mi{fp}", tex)
        # hemant appears as a predicate argument, not a principal modality
        self.assertIn("hemant", tex)
        self.assertIn(r"{\mb{says}}R", tex)
        self.assertIn(r"{\mb{says}}L", tex)


# ============================================================================
# Part 1b: Rule label mapping
# ============================================================================

class TestRuleLabels(unittest.TestCase):
    """Verify _rule_to_latex produces correct lecture-notation labels."""

    EXPECTED = {
        "id":       r"\ms{id}",
        "→R":       r"{\arrow}R",
        "→L":       r"{\arrow}L",
        "∧R":       r"{\land}R",
        "∧L":       r"{\land}L",
        "∨R₁":      r"{\lor}R_1",
        "∨R₂":      r"{\lor}R_2",
        "∨L":       r"{\lor}L",
        "∀R":       r"{\forall}R^y",
        "∀L":       r"{\forall}L",
        "saysR":    r"{\mb{says}}R",
        "saysL":    r"{\mb{says}}L",
        "aff":      r"\mb{aff}",
        "cut":      r"\ms{cut}",
    }

    def test_all_rule_labels(self):
        rtl = sg._rule_to_latex
        for rule, expected in self.EXPECTED.items():
            with self.subTest(rule=rule):
                self.assertEqual(rtl(rule), expected)

    def test_invertible_dashed(self):
        """Invertible rules must use \\infer- (dashed line)."""
        expected_invertible = {"→R", "∧R", "∧L", "∨L", "∀R",
                               "saysR", "saysL", "≤-says+saysL", "cut"}
        self.assertEqual(INVERTIBLE_RULES, expected_invertible)

    def test_non_invertible_solid(self):
        """Non-invertible rules must use \\infer (solid line)."""
        expected_non_inv = {"→L", "∨R₁", "∨R₂", "∀L", "aff"}
        self.assertEqual(NON_INVERTIBLE_RULES, expected_non_inv)

    def test_id_not_invertible(self):
        self.assertNotIn("id", INVERTIBLE_RULES)


# ============================================================================
# Part 2: Generated test_all_rules.tex
# ============================================================================

class TestLatexDocument(unittest.TestCase):
    """Verify the generated test_all_rules.tex is correct and compiles."""

    @classmethod
    def setUpClass(cls):
        tex_path = os.path.join(LATEX_DIR, "test_all_rules.tex")
        with open(tex_path, 'r') as f:
            cls.tex_content = f.read()

    def test_has_23_sections(self):
        count = self.tex_content.count(r"\section{")
        self.assertEqual(count, 23, f"Expected 23 sections, found {count}")

    def test_uses_lmacros(self):
        self.assertIn(r"\input{lmacros}", self.tex_content)

    def test_uses_proof_dashed(self):
        self.assertIn(r"\usepackage{lecnotes}", self.tex_content)

    def test_infer_commands_present(self):
        self.assertIn(r"\infer[", self.tex_content)
        self.assertIn(r"\infer-[", self.tex_content)

    def test_macros_used(self):
        for macro in [r"\says", r"\aff", r"\arrow", r"\mi{", r"\ms{",
                      r"\mb{", r"\land", r"\lor", r"\vdash"]:
            with self.subTest(macro=macro):
                self.assertIn(macro, self.tex_content)

    def test_pdflatex_compiles(self):
        """Compile with pdflatex — zero errors and zero undefined control sequences."""
        result = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "test_all_rules.tex"],
            cwd=LATEX_DIR,
            capture_output=True,
            text=True,
            timeout=60,
        )
        self.assertEqual(result.returncode, 0,
                         f"pdflatex failed:\n{result.stdout[-2000:]}")
        log_path = os.path.join(LATEX_DIR, "test_all_rules.log")
        with open(log_path, 'r') as f:
            log = f.read()
        undef = log.count("Undefined control sequence")
        self.assertEqual(undef, 0,
                         f"Found {undef} undefined control sequences in log")
        errors = [l for l in log.split('\n') if l.startswith('!')]
        self.assertEqual(len(errors), 0, f"LaTeX errors: {errors}")


# ============================================================================
# Part 3: Formula.to_latex() for auth types
# ============================================================================

class TestFormulaToLatex(unittest.TestCase):
    """Verify to_latex() for Says, Aff, and nested formulas."""

    def test_says(self):
        s = Says(Principal("admin"), Atom("p"))
        self.assertEqual(s.to_latex(), r"(\mi{admin} \says p)")

    def test_aff(self):
        a = Aff(Principal("admin"), Atom("p"))
        self.assertEqual(a.to_latex(), r"(\mi{admin} \aff p)")

    def test_says_nested_implies(self):
        s = Says(Principal("admin"), Implies(Atom("p"), Atom("q")))
        self.assertEqual(s.to_latex(),
                         r"(\mi{admin} \says (p \arrow q))")

    def test_aff_nested_and(self):
        a = Aff(Principal("fp"), And(Atom("p"), Atom("q")))
        self.assertEqual(a.to_latex(),
                         r"(\mi{fp} \aff (p \land q))")

    def test_says_with_predicate(self):
        s = Says(Principal("admin"), Atom("owns(fp, ghc6017)"))
        self.assertEqual(s.to_latex(),
                         r"(\mi{admin} \says \ms{owns}(fp, ghc6017))")

    def test_principal_to_latex(self):
        self.assertEqual(Principal("admin").to_latex(), r"\mi{admin}")
        self.assertEqual(Principal("fp").to_latex(), r"\mi{fp}")

    def test_trust_leq_to_latex(self):
        t = TrustLeq(Principal("admin"), Principal("fp"))
        self.assertEqual(t.to_latex(),
                         r"(\mi{admin} \leq \mi{fp})")

    def test_sequent_to_latex_empty_context(self):
        seq = Sequent([], Atom("p"))
        self.assertEqual(seq.to_latex(), r"\cdot \vdash p")

    def test_sequent_to_latex_with_context(self):
        seq = Sequent([Atom("p"), Atom("q")], And(Atom("p"), Atom("q")))
        self.assertEqual(seq.to_latex(), r"p, q \vdash (p \land q)")

    def test_atom_predicate_latex(self):
        a = Atom("owns(A, R)")
        self.assertEqual(a.to_latex(), r"\ms{owns}(A, R)")

    def test_forall_latex(self):
        f = Forall("x", Atom("P(x)"))
        self.assertEqual(f.to_latex(), r"(\forall x.\, \ms{P}(x))")

    def test_or_latex(self):
        o = Or(Atom("p"), Atom("q"))
        self.assertEqual(o.to_latex(), r"(p \lor q)")

    def test_implies_latex(self):
        i = Implies(Atom("p"), Atom("q"))
        self.assertEqual(i.to_latex(), r"(p \arrow q)")

    def test_nested_says_says(self):
        """A says (B says P)"""
        inner = Says(Principal("B"), Atom("P"))
        outer = Says(Principal("A"), inner)
        self.assertEqual(outer.to_latex(),
                         r"(\mi{A} \says (\mi{B} \says P))")


# ============================================================================
# Part 3b: Negative test cases (should not prove)
# ============================================================================

class TestNegativeCases(unittest.TestCase):
    """Sequents that should NOT be provable."""

    def test_excluded_middle_fails(self):
        seq = Sequent([], Or(Atom('P'), Implies(Atom('P'), Atom('Q'))))
        self.assertIsNone(prove(seq))

    def test_wrong_principal_fails(self):
        fp = Principal('fp')
        admin = Principal('admin')
        seq = Sequent([Says(fp, Atom('P'))], Aff(admin, Atom('P')))
        self.assertIsNone(prove(seq))

    def test_trust_absent_fails(self):
        admin = Principal('admin')
        fp = Principal('fp')
        trust = TrustContext()
        trust.add(admin, fp)
        seq = Sequent(
            [Says(fp, Atom('P')), Says(admin, Atom('Q'))],
            Says(fp, Atom('Q')))
        self.assertIsNone(prove(seq, trust=trust))


if __name__ == "__main__":
    unittest.main(verbosity=2)
