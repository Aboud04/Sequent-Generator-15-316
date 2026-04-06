"""Exhaustive tests for authorization logic rules in sequentGen.py.

Tests cover:
  1. Formula classes (Says, Aff) — construction, __str__, __eq__, to_latex()
  2. Parser — "admin says p", "admin says (p -> q)", "admin aff p", nested
  3. _substitute — handles Says and Aff
  4. _trust_holds — reflexivity, transitivity, non-symmetry
  5. Rule logic — saysR, saysL, aff, ∨R₁, ∨R₂, ≤-says, cut'
  6. LaTeX export — correct rule labels
"""

import sys
import os
import unittest

# Insert project root so we can import sequentGen
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from sequentGen import (
    Formula, Atom, Not, And, Or, Implies, Iff, Top, Bottom,
    Says, Aff,
    Forall, Exists,
    Sequent, ProofNode,
    LogicParser,
    SequentProverApp,
)


class MockApp:
    """Lightweight stand-in for SequentProverApp that provides only the
    state needed to test _trust_holds, _substitute, apply_unary_rule,
    apply_binary_rule, and the rule_* methods — without a Tk root."""

    def __init__(self):
        self.trust_facts = []
        self.parser = LogicParser()
        self.current_proof_node = None
        self.selected_formula_index = None
        self.selected_side = None
        self.current_tree_id = "mock"
        self.node_map = {}
        self._last_status = ""

    # Bind real methods from the class
    _trust_holds = SequentProverApp._trust_holds
    _substitute = SequentProverApp._substitute

    # Lightweight apply_unary_rule that doesn't touch GUI
    def apply_unary_rule(self, rule_name, new_lhs_list, new_rhs_list):
        node = self.current_proof_node
        seq = node.sequent
        next_lhs = seq.lhs[:]
        next_rhs = seq.rhs[:]
        if self.selected_side == "lhs":
            del next_lhs[self.selected_formula_index]
        else:
            del next_rhs[self.selected_formula_index]
        next_lhs.extend(new_lhs_list)
        next_rhs.extend(new_rhs_list)
        new_sequent = Sequent(next_lhs, next_rhs)
        node.add_child(new_sequent)
        node.rule_applied = rule_name

    def apply_binary_rule(self, rule_name, branch1_add, branch2_add):
        node = self.current_proof_node
        seq = node.sequent
        base_lhs = seq.lhs[:]
        base_rhs = seq.rhs[:]
        if self.selected_side == "lhs":
            del base_lhs[self.selected_formula_index]
        else:
            del base_rhs[self.selected_formula_index]
        b1_seq = Sequent(base_lhs + branch1_add[0], base_rhs + branch1_add[1])
        node.add_child(b1_seq)
        b2_seq = Sequent(base_lhs + branch2_add[0], base_rhs + branch2_add[1])
        node.add_child(b2_seq)
        node.rule_applied = rule_name

    def get_target(self):
        if self.selected_formula_index is None:
            return None, None, None
        node = self.current_proof_node
        if node.children or node.is_closed:
            return None, None, None
        seq = node.sequent
        if self.selected_side == "lhs":
            target = seq.lhs[self.selected_formula_index]
        else:
            target = seq.rhs[self.selected_formula_index]
        return node, seq, target

    class _StatusVar:
        def __init__(self):
            self.value = ""
        def set(self, v):
            self.value = v

    @property
    def status_var(self):
        if not hasattr(self, "_sv"):
            self._sv = self._StatusVar()
        return self._sv

    def _setup_sequent(self, lhs, rhs, side, index):
        """Helper: set up a fresh leaf node ready for a rule application."""
        seq = Sequent(lhs, rhs)
        node = ProofNode(seq)
        self.current_proof_node = node
        self.selected_side = side
        self.selected_formula_index = index
        return node

    # Bind real rule methods
    rule_says_r = SequentProverApp.rule_says_r
    rule_says_l = SequentProverApp.rule_says_l
    rule_aff = SequentProverApp.rule_aff
    rule_or_r1 = SequentProverApp.rule_or_r1
    rule_or_r2 = SequentProverApp.rule_or_r2
    rule_trust_says = SequentProverApp.rule_trust_says


# ============================================================================
# 1. Formula classes — Says, Aff
# ============================================================================

class TestSaysFormula(unittest.TestCase):

    def test_construction(self):
        s = Says("admin", Atom("p"))
        self.assertEqual(s.principal, "admin")
        self.assertEqual(s.inner, Atom("p"))

    def test_str(self):
        s = Says("admin", Atom("p"))
        self.assertEqual(str(s), "(admin says p)")

    def test_str_nested(self):
        s = Says("admin", Implies(Atom("p"), Atom("q")))
        self.assertEqual(str(s), "(admin says (p → q))")

    def test_eq_same(self):
        a = Says("admin", Atom("p"))
        b = Says("admin", Atom("p"))
        self.assertEqual(a, b)

    def test_eq_diff_principal(self):
        a = Says("admin", Atom("p"))
        b = Says("user", Atom("p"))
        self.assertNotEqual(a, b)

    def test_eq_diff_inner(self):
        a = Says("admin", Atom("p"))
        b = Says("admin", Atom("q"))
        self.assertNotEqual(a, b)

    def test_eq_diff_type(self):
        a = Says("admin", Atom("p"))
        b = Aff("admin", Atom("p"))
        self.assertNotEqual(a, b)

    def test_to_latex(self):
        s = Says("admin", Atom("p"))
        latex = s.to_latex()
        self.assertIn("\\says", latex)
        self.assertIn("admin", latex)
        self.assertIn("p", latex)

    def test_to_latex_nested(self):
        s = Says("fp", Implies(Atom("a"), Atom("b")))
        latex = s.to_latex()
        self.assertIn("\\says", latex)
        self.assertIn("\\to", latex)

    def test_repr(self):
        s = Says("admin", Atom("p"))
        self.assertEqual(repr(s), str(s))


class TestAffFormula(unittest.TestCase):

    def test_construction(self):
        a = Aff("admin", Atom("p"))
        self.assertEqual(a.principal, "admin")
        self.assertEqual(a.inner, Atom("p"))

    def test_str(self):
        a = Aff("admin", Atom("p"))
        self.assertEqual(str(a), "(admin aff p)")

    def test_str_nested(self):
        a = Aff("user", Or(Atom("a"), Atom("b")))
        self.assertEqual(str(a), "(user aff (a ∨ b))")

    def test_eq_same(self):
        a = Aff("admin", Atom("p"))
        b = Aff("admin", Atom("p"))
        self.assertEqual(a, b)

    def test_eq_diff_principal(self):
        self.assertNotEqual(Aff("admin", Atom("p")), Aff("user", Atom("p")))

    def test_eq_diff_inner(self):
        self.assertNotEqual(Aff("admin", Atom("p")), Aff("admin", Atom("q")))

    def test_eq_says_vs_aff(self):
        self.assertNotEqual(Aff("admin", Atom("p")), Says("admin", Atom("p")))

    def test_to_latex(self):
        a = Aff("admin", Atom("p"))
        latex = a.to_latex()
        self.assertIn("\\aff", latex)
        self.assertIn("admin", latex)
        self.assertIn("p", latex)

    def test_to_latex_nested(self):
        a = Aff("fp", And(Atom("x"), Atom("y")))
        latex = a.to_latex()
        self.assertIn("\\aff", latex)
        self.assertIn("\\land", latex)


# ============================================================================
# 2. Parser tests
# ============================================================================

class TestParserAuth(unittest.TestCase):

    def setUp(self):
        self.parser = LogicParser()

    def test_parse_says_simple(self):
        f = self.parser.parse("admin says p")
        self.assertIsInstance(f, Says)
        self.assertEqual(f.principal, "admin")
        self.assertEqual(f.inner, Atom("p"))

    def test_parse_says_parens(self):
        f = self.parser.parse("admin says (p -> q)")
        self.assertIsInstance(f, Says)
        self.assertEqual(f.principal, "admin")
        self.assertIsInstance(f.inner, Implies)
        self.assertEqual(f.inner.left, Atom("p"))
        self.assertEqual(f.inner.right, Atom("q"))

    def test_parse_aff_simple(self):
        f = self.parser.parse("admin aff p")
        self.assertIsInstance(f, Aff)
        self.assertEqual(f.principal, "admin")
        self.assertEqual(f.inner, Atom("p"))

    def test_parse_aff_complex(self):
        f = self.parser.parse("fp aff (a & b)")
        self.assertIsInstance(f, Aff)
        self.assertEqual(f.principal, "fp")
        self.assertIsInstance(f.inner, And)

    def test_parse_says_with_or(self):
        f = self.parser.parse("admin says (p | q)")
        self.assertIsInstance(f, Says)
        self.assertIsInstance(f.inner, Or)

    def test_parse_nested_says(self):
        f = self.parser.parse("admin says (user says p)")
        self.assertIsInstance(f, Says)
        self.assertEqual(f.principal, "admin")
        self.assertIsInstance(f.inner, Says)
        self.assertEqual(f.inner.principal, "user")

    def test_parse_says_implies_aff(self):
        """says has lower precedence than connectives — verify grouping."""
        f = self.parser.parse("admin says p -> q")
        # "admin says (p -> q)" because says consumes rest via parse_iff
        self.assertIsInstance(f, Says)
        self.assertIsInstance(f.inner, Implies)

    def test_parse_roundtrip_says(self):
        f = self.parser.parse("admin says p")
        f2 = self.parser.parse(str(f))
        self.assertEqual(f, f2)

    def test_parse_roundtrip_aff(self):
        f = self.parser.parse("admin aff p")
        f2 = self.parser.parse(str(f))
        self.assertEqual(f, f2)

    def test_parse_says_not(self):
        f = self.parser.parse("admin says ~p")
        self.assertIsInstance(f, Says)
        self.assertIsInstance(f.inner, Not)

    def test_parse_says_with_and(self):
        f = self.parser.parse("admin says (p & q)")
        self.assertIsInstance(f, Says)
        self.assertIsInstance(f.inner, And)


# ============================================================================
# 3. _substitute handles Says and Aff
# ============================================================================

class TestSubstitute(unittest.TestCase):

    def setUp(self):
        self.app = MockApp()

    def test_substitute_atom_match(self):
        result = self.app._substitute(Atom("x"), "x", Atom("t"))
        self.assertEqual(result, Atom("t"))

    def test_substitute_atom_no_match(self):
        result = self.app._substitute(Atom("y"), "x", Atom("t"))
        self.assertEqual(result, Atom("y"))

    def test_substitute_says_inner(self):
        f = Says("admin", Atom("x"))
        result = self.app._substitute(f, "x", Atom("t"))
        self.assertIsInstance(result, Says)
        self.assertEqual(result.principal, "admin")
        self.assertEqual(result.inner, Atom("t"))

    def test_substitute_says_no_match(self):
        f = Says("admin", Atom("p"))
        result = self.app._substitute(f, "x", Atom("t"))
        self.assertEqual(result.inner, Atom("p"))

    def test_substitute_aff_inner(self):
        f = Aff("user", Atom("x"))
        result = self.app._substitute(f, "x", Atom("t"))
        self.assertIsInstance(result, Aff)
        self.assertEqual(result.principal, "user")
        self.assertEqual(result.inner, Atom("t"))

    def test_substitute_aff_no_match(self):
        f = Aff("user", Atom("q"))
        result = self.app._substitute(f, "x", Atom("t"))
        self.assertEqual(result.inner, Atom("q"))

    def test_substitute_says_nested(self):
        f = Says("admin", Implies(Atom("x"), Atom("y")))
        result = self.app._substitute(f, "x", Atom("t"))
        self.assertIsInstance(result, Says)
        self.assertIsInstance(result.inner, Implies)
        self.assertEqual(result.inner.left, Atom("t"))
        self.assertEqual(result.inner.right, Atom("y"))

    def test_substitute_aff_nested(self):
        f = Aff("fp", And(Atom("x"), Atom("x")))
        result = self.app._substitute(f, "x", Atom("t"))
        self.assertEqual(result.inner.left, Atom("t"))
        self.assertEqual(result.inner.right, Atom("t"))

    def test_substitute_preserves_principal(self):
        """Principal name is a string, not a formula — substitution doesn't touch it."""
        f = Says("x", Atom("x"))
        result = self.app._substitute(f, "x", Atom("t"))
        self.assertEqual(result.principal, "x")
        self.assertEqual(result.inner, Atom("t"))


# ============================================================================
# 4. _trust_holds — reflexivity, transitivity, non-symmetry
# ============================================================================

class TestTrustHolds(unittest.TestCase):

    def setUp(self):
        self.app = MockApp()

    def test_reflexivity(self):
        self.assertTrue(self.app._trust_holds("admin", "admin"))

    def test_reflexivity_no_facts(self):
        self.assertTrue(self.app._trust_holds("x", "x"))

    def test_direct_trust(self):
        self.app.trust_facts = [("admin", "fp")]
        self.assertTrue(self.app._trust_holds("admin", "fp"))

    def test_no_trust(self):
        self.app.trust_facts = [("admin", "fp")]
        self.assertFalse(self.app._trust_holds("admin", "user"))

    def test_non_symmetry(self):
        """a ≤ b does NOT imply b ≤ a."""
        self.app.trust_facts = [("admin", "fp")]
        self.assertTrue(self.app._trust_holds("admin", "fp"))
        self.assertFalse(self.app._trust_holds("fp", "admin"))

    def test_transitivity(self):
        self.app.trust_facts = [("admin", "fp"), ("fp", "user")]
        self.assertTrue(self.app._trust_holds("admin", "user"))

    def test_transitivity_longer_chain(self):
        self.app.trust_facts = [("a", "b"), ("b", "c"), ("c", "d")]
        self.assertTrue(self.app._trust_holds("a", "d"))
        self.assertFalse(self.app._trust_holds("d", "a"))

    def test_transitivity_not_shortcut(self):
        """Middle link missing → no transitivity."""
        self.app.trust_facts = [("a", "b"), ("c", "d")]
        self.assertFalse(self.app._trust_holds("a", "d"))

    def test_cycle_handling(self):
        """Cycles should terminate without infinite loop."""
        self.app.trust_facts = [("a", "b"), ("b", "c"), ("c", "a")]
        self.assertTrue(self.app._trust_holds("a", "c"))
        self.assertTrue(self.app._trust_holds("c", "a"))

    def test_empty_trust_facts(self):
        self.app.trust_facts = []
        self.assertFalse(self.app._trust_holds("admin", "fp"))

    def test_multiple_paths(self):
        self.app.trust_facts = [("a", "b"), ("a", "c"), ("b", "d"), ("c", "d")]
        self.assertTrue(self.app._trust_holds("a", "d"))


# ============================================================================
# 5. Rule logic — saysR, saysL, aff, ∨R₁, ∨R₂, ≤-says, cut'
# ============================================================================

class TestRuleSaysR(unittest.TestCase):
    """saysR: Γ ⊢ (A says P), Δ  --->  Γ ⊢ (A aff P), Δ"""

    def setUp(self):
        self.app = MockApp()

    def test_basic(self):
        says = Says("admin", Atom("p"))
        node = self.app._setup_sequent(
            [Atom("q")], [says], side="rhs", index=0
        )
        self.app.rule_says_r()
        self.assertEqual(len(node.children), 1)
        child = node.children[0].sequent
        self.assertEqual(child.lhs, [Atom("q")])
        self.assertEqual(len(child.rhs), 1)
        self.assertIsInstance(child.rhs[0], Aff)
        self.assertEqual(child.rhs[0].principal, "admin")
        self.assertEqual(child.rhs[0].inner, Atom("p"))
        self.assertEqual(node.rule_applied, "saysR")

    def test_preserves_other_rhs(self):
        says = Says("fp", Atom("r"))
        node = self.app._setup_sequent(
            [Atom("a")], [Atom("x"), says], side="rhs", index=1
        )
        self.app.rule_says_r()
        child = node.children[0].sequent
        self.assertEqual(child.rhs[0], Atom("x"))
        self.assertIsInstance(child.rhs[1], Aff)

    def test_rejects_non_says(self):
        """Applying saysR to non-Says formula should be rejected."""
        node = self.app._setup_sequent(
            [], [Atom("p")], side="rhs", index=0
        )
        self.app.rule_says_r()
        self.assertEqual(len(node.children), 0)  # No rule applied

    def test_rejects_lhs(self):
        """saysR only works on RHS."""
        says = Says("admin", Atom("p"))
        node = self.app._setup_sequent(
            [says], [Atom("q")], side="lhs", index=0
        )
        self.app.rule_says_r()
        self.assertEqual(len(node.children), 0)

    def test_complex_inner(self):
        inner = Implies(Atom("a"), Atom("b"))
        says = Says("admin", inner)
        node = self.app._setup_sequent([], [says], side="rhs", index=0)
        self.app.rule_says_r()
        child = node.children[0].sequent
        self.assertIsInstance(child.rhs[0], Aff)
        self.assertEqual(child.rhs[0].inner, inner)


class TestRuleSaysL(unittest.TestCase):
    """saysL: Γ, A says P ⊢ A aff Q  --->  Γ, P ⊢ A aff Q"""

    def setUp(self):
        self.app = MockApp()

    def test_basic(self):
        says = Says("admin", Atom("p"))
        aff = Aff("admin", Atom("q"))
        node = self.app._setup_sequent(
            [says], [aff], side="lhs", index=0
        )
        self.app.rule_says_l()
        self.assertEqual(len(node.children), 1)
        child = node.children[0].sequent
        # LHS: removed Says("admin",p), added p
        self.assertEqual(child.lhs, [Atom("p")])
        # RHS unchanged
        self.assertEqual(child.rhs, [aff])
        self.assertEqual(node.rule_applied, "saysL")

    def test_rejects_no_matching_aff(self):
        """saysL requires RHS to have Aff with same principal."""
        says = Says("admin", Atom("p"))
        node = self.app._setup_sequent(
            [says], [Atom("q")], side="lhs", index=0
        )
        self.app.rule_says_l()
        self.assertEqual(len(node.children), 0)

    def test_rejects_different_principal(self):
        says = Says("admin", Atom("p"))
        aff = Aff("user", Atom("q"))
        node = self.app._setup_sequent(
            [says], [aff], side="lhs", index=0
        )
        self.app.rule_says_l()
        self.assertEqual(len(node.children), 0)

    def test_rejects_rhs_side(self):
        says = Says("admin", Atom("p"))
        aff = Aff("admin", Atom("q"))
        node = self.app._setup_sequent(
            [Atom("x")], [says, aff], side="rhs", index=0
        )
        self.app.rule_says_l()
        self.assertEqual(len(node.children), 0)

    def test_preserves_context(self):
        says = Says("admin", Atom("p"))
        aff = Aff("admin", Atom("q"))
        node = self.app._setup_sequent(
            [Atom("a"), says, Atom("b")], [aff], side="lhs", index=1
        )
        self.app.rule_says_l()
        child = node.children[0].sequent
        self.assertIn(Atom("a"), child.lhs)
        self.assertIn(Atom("b"), child.lhs)
        self.assertIn(Atom("p"), child.lhs)
        self.assertNotIn(says, child.lhs)

    def test_complex_inner(self):
        inner = And(Atom("x"), Atom("y"))
        says = Says("fp", inner)
        aff = Aff("fp", Atom("z"))
        node = self.app._setup_sequent([says], [aff], side="lhs", index=0)
        self.app.rule_says_l()
        child = node.children[0].sequent
        self.assertEqual(child.lhs, [inner])


class TestRuleAff(unittest.TestCase):
    """aff: Γ ⊢ (A aff P), Δ  --->  Γ ⊢ P, Δ"""

    def setUp(self):
        self.app = MockApp()

    def test_basic(self):
        aff = Aff("admin", Atom("p"))
        node = self.app._setup_sequent(
            [Atom("q")], [aff], side="rhs", index=0
        )
        self.app.rule_aff()
        self.assertEqual(len(node.children), 1)
        child = node.children[0].sequent
        self.assertEqual(child.rhs, [Atom("p")])
        self.assertEqual(child.lhs, [Atom("q")])
        self.assertEqual(node.rule_applied, "aff")

    def test_rejects_non_aff(self):
        node = self.app._setup_sequent(
            [], [Atom("p")], side="rhs", index=0
        )
        self.app.rule_aff()
        self.assertEqual(len(node.children), 0)

    def test_rejects_lhs(self):
        aff = Aff("admin", Atom("p"))
        node = self.app._setup_sequent(
            [aff], [Atom("q")], side="lhs", index=0
        )
        self.app.rule_aff()
        self.assertEqual(len(node.children), 0)

    def test_preserves_other_rhs(self):
        aff = Aff("admin", Atom("p"))
        node = self.app._setup_sequent(
            [], [Atom("x"), aff, Atom("y")], side="rhs", index=1
        )
        self.app.rule_aff()
        child = node.children[0].sequent
        self.assertIn(Atom("x"), child.rhs)
        self.assertIn(Atom("y"), child.rhs)
        self.assertIn(Atom("p"), child.rhs)

    def test_complex_inner(self):
        inner = Implies(Atom("a"), Atom("b"))
        aff = Aff("fp", inner)
        node = self.app._setup_sequent([], [aff], side="rhs", index=0)
        self.app.rule_aff()
        child = node.children[0].sequent
        self.assertEqual(child.rhs, [inner])


class TestRuleOrR1(unittest.TestCase):
    """∨R₁: Γ ⊢ P ∨ Q  --->  Γ ⊢ P"""

    def setUp(self):
        self.app = MockApp()

    def test_basic(self):
        disj = Or(Atom("p"), Atom("q"))
        node = self.app._setup_sequent([], [disj], side="rhs", index=0)
        self.app.rule_or_r1()
        self.assertEqual(len(node.children), 1)
        child = node.children[0].sequent
        self.assertEqual(child.rhs, [Atom("p")])
        self.assertEqual(node.rule_applied, "∨R₁")

    def test_rejects_non_or(self):
        node = self.app._setup_sequent([], [Atom("p")], side="rhs", index=0)
        self.app.rule_or_r1()
        self.assertEqual(len(node.children), 0)

    def test_rejects_lhs(self):
        disj = Or(Atom("p"), Atom("q"))
        node = self.app._setup_sequent([disj], [], side="lhs", index=0)
        self.app.rule_or_r1()
        self.assertEqual(len(node.children), 0)

    def test_preserves_lhs(self):
        disj = Or(Atom("p"), Atom("q"))
        node = self.app._setup_sequent(
            [Atom("a"), Atom("b")], [disj], side="rhs", index=0
        )
        self.app.rule_or_r1()
        child = node.children[0].sequent
        self.assertEqual(child.lhs, [Atom("a"), Atom("b")])


class TestRuleOrR2(unittest.TestCase):
    """∨R₂: Γ ⊢ P ∨ Q  --->  Γ ⊢ Q"""

    def setUp(self):
        self.app = MockApp()

    def test_basic(self):
        disj = Or(Atom("p"), Atom("q"))
        node = self.app._setup_sequent([], [disj], side="rhs", index=0)
        self.app.rule_or_r2()
        self.assertEqual(len(node.children), 1)
        child = node.children[0].sequent
        self.assertEqual(child.rhs, [Atom("q")])
        self.assertEqual(node.rule_applied, "∨R₂")

    def test_rejects_non_or(self):
        node = self.app._setup_sequent([], [Atom("p")], side="rhs", index=0)
        self.app.rule_or_r2()
        self.assertEqual(len(node.children), 0)

    def test_rejects_lhs(self):
        disj = Or(Atom("p"), Atom("q"))
        node = self.app._setup_sequent([disj], [], side="lhs", index=0)
        self.app.rule_or_r2()
        self.assertEqual(len(node.children), 0)


class TestRuleTrustSays(unittest.TestCase):
    """≤-says: If A ≤ B and (B says P) on LHS, rewrite to (A says P)."""

    def setUp(self):
        self.app = MockApp()

    def test_basic(self):
        self.app.trust_facts = [("admin", "fp")]
        says = Says("fp", Atom("p"))
        node = self.app._setup_sequent(
            [says], [Atom("q")], side="lhs", index=0
        )
        self.app.rule_trust_says()
        self.assertEqual(len(node.children), 1)
        child = node.children[0].sequent
        # Should have replaced (fp says p) with (admin says p)
        new_says = child.lhs[0]
        self.assertIsInstance(new_says, Says)
        self.assertEqual(new_says.principal, "admin")
        self.assertEqual(new_says.inner, Atom("p"))
        self.assertEqual(node.rule_applied, "≤-says")

    def test_rejects_non_says(self):
        self.app.trust_facts = [("admin", "fp")]
        node = self.app._setup_sequent(
            [Atom("p")], [Atom("q")], side="lhs", index=0
        )
        self.app.rule_trust_says()
        self.assertEqual(len(node.children), 0)

    def test_rejects_rhs(self):
        self.app.trust_facts = [("admin", "fp")]
        says = Says("fp", Atom("p"))
        node = self.app._setup_sequent(
            [Atom("q")], [says], side="rhs", index=0
        )
        self.app.rule_trust_says()
        self.assertEqual(len(node.children), 0)

    def test_rejects_no_trust_facts(self):
        self.app.trust_facts = []
        says = Says("fp", Atom("p"))
        node = self.app._setup_sequent(
            [says], [Atom("q")], side="lhs", index=0
        )
        self.app.rule_trust_says()
        self.assertEqual(len(node.children), 0)

    def test_rejects_no_eligible(self):
        """Trust exists but nobody trusts the formula's principal."""
        self.app.trust_facts = [("x", "y")]
        says = Says("fp", Atom("p"))
        node = self.app._setup_sequent(
            [says], [Atom("q")], side="lhs", index=0
        )
        self.app.rule_trust_says()
        self.assertEqual(len(node.children), 0)


class TestRuleCutPrime(unittest.TestCase):
    """cut': Split-context cut variant.
    Γ₁,Γ₂ ⊢ δ  from  Γ₁ ⊢ P  and  Γ₂,P ⊢ δ"""

    def setUp(self):
        self.app = MockApp()
        self.app.parser = LogicParser()

    def test_basic(self):
        """Directly simulate cut' logic (since it uses simpledialog)."""
        lhs = [Atom("a"), Atom("b"), Atom("c")]
        rhs = [Atom("d")]
        seq = Sequent(lhs, rhs)
        node = ProofNode(seq)
        cut_formula = Atom("P")
        gamma1_indices = {0, 2}  # a, c go to Γ₁

        gamma1 = [f for i, f in enumerate(lhs) if i in gamma1_indices]
        gamma2 = [f for i, f in enumerate(lhs) if i not in gamma1_indices]

        # Branch 1: Γ₁ ⊢ P
        b1_seq = Sequent(gamma1, [cut_formula])
        node.add_child(b1_seq)
        # Branch 2: Γ₂, P ⊢ δ
        b2_seq = Sequent(gamma2 + [cut_formula], rhs[:])
        node.add_child(b2_seq)
        node.rule_applied = "cut'"

        self.assertEqual(len(node.children), 2)
        # Branch 1: {a, c} ⊢ P
        self.assertEqual(node.children[0].sequent.lhs, [Atom("a"), Atom("c")])
        self.assertEqual(node.children[0].sequent.rhs, [Atom("P")])
        # Branch 2: {b}, P ⊢ d
        self.assertEqual(node.children[1].sequent.lhs, [Atom("b"), Atom("P")])
        self.assertEqual(node.children[1].sequent.rhs, [Atom("d")])
        self.assertEqual(node.rule_applied, "cut'")

    def test_all_to_gamma1(self):
        lhs = [Atom("a"), Atom("b")]
        rhs = [Atom("d")]
        seq = Sequent(lhs, rhs)
        node = ProofNode(seq)
        cut_formula = Atom("P")
        gamma1_indices = {0, 1}

        gamma1 = [f for i, f in enumerate(lhs) if i in gamma1_indices]
        gamma2 = [f for i, f in enumerate(lhs) if i not in gamma1_indices]

        b1_seq = Sequent(gamma1, [cut_formula])
        node.add_child(b1_seq)
        b2_seq = Sequent(gamma2 + [cut_formula], rhs[:])
        node.add_child(b2_seq)
        node.rule_applied = "cut'"

        self.assertEqual(node.children[0].sequent.lhs, [Atom("a"), Atom("b")])
        self.assertEqual(node.children[1].sequent.lhs, [Atom("P")])

    def test_empty_gamma1(self):
        lhs = [Atom("a")]
        rhs = [Atom("d")]
        seq = Sequent(lhs, rhs)
        node = ProofNode(seq)
        cut_formula = Atom("P")
        gamma1_indices = set()

        gamma1 = [f for i, f in enumerate(lhs) if i in gamma1_indices]
        gamma2 = [f for i, f in enumerate(lhs) if i not in gamma1_indices]

        b1_seq = Sequent(gamma1, [cut_formula])
        node.add_child(b1_seq)
        b2_seq = Sequent(gamma2 + [cut_formula], rhs[:])
        node.add_child(b2_seq)
        node.rule_applied = "cut'"

        # Branch 1: empty context ⊢ P
        self.assertEqual(node.children[0].sequent.lhs, [])
        # Branch 2: a, P ⊢ d
        self.assertEqual(node.children[1].sequent.lhs, [Atom("a"), Atom("P")])


# ============================================================================
# 6. LaTeX export — correct rule labels
# ============================================================================

class TestLatexRuleLabels(unittest.TestCase):
    """Verify the LaTeX export produces correct rule labels."""

    def _build_latex(self, node):
        """Replicate the recursive_build from export_latex."""
        def recursive_build(n, depth=0):
            indent = "  " * depth
            rule = n.rule_applied if n.rule_applied else "?"
            rule_tex = (
                rule.replace("∧", "\\land ")
                .replace("∨", "\\lor ")
                .replace("→", "\\to ")
                .replace("¬", "\\lnot ")
                .replace("saysR", "{\\mathbf{says}}R")
                .replace("saysL", "{\\mathbf{says}}L")
                .replace("≤-says", "\\leq\\mbox{-}\\mathbf{says}")
                .replace("cut'", "\\ms{cut}'")
            )
            if rule_tex == "aff":
                rule_tex = "\\mathbf{aff}"
            sequent_tex = n.sequent.to_latex()
            if not n.children:
                if n.is_closed:
                    return f"{indent}\\infer[\\ms{{id}}]\n{indent}  {{{sequent_tex}}}\n{indent}  {{}}"
                else:
                    return f"{indent}\\deduce[?]\n{indent}  {{{sequent_tex}}}\n{indent}  {{}}"
            premises = [recursive_build(child, depth + 1) for child in n.children]
            joined_premises = f"\n{indent}  &\n".join(premises)
            return f"{indent}\\infer[{rule_tex}]\n{indent}  {{{sequent_tex}}}\n{indent}  {{\n{joined_premises}\n{indent}  }}"
        return recursive_build(node)

    def test_says_r_label(self):
        seq = Sequent([Atom("q")], [Says("admin", Atom("p"))])
        node = ProofNode(seq)
        child_seq = Sequent([Atom("q")], [Aff("admin", Atom("p"))])
        node.add_child(child_seq)
        node.rule_applied = "saysR"
        latex = self._build_latex(node)
        self.assertIn("{\\mathbf{says}}R", latex)

    def test_says_l_label(self):
        seq = Sequent([Says("admin", Atom("p"))], [Aff("admin", Atom("q"))])
        node = ProofNode(seq)
        child_seq = Sequent([Atom("p")], [Aff("admin", Atom("q"))])
        node.add_child(child_seq)
        node.rule_applied = "saysL"
        latex = self._build_latex(node)
        self.assertIn("{\\mathbf{says}}L", latex)

    def test_aff_label(self):
        seq = Sequent([], [Aff("admin", Atom("p"))])
        node = ProofNode(seq)
        child_seq = Sequent([], [Atom("p")])
        node.add_child(child_seq)
        node.rule_applied = "aff"
        latex = self._build_latex(node)
        self.assertIn("\\mathbf{aff}", latex)

    def test_or_r1_label(self):
        seq = Sequent([], [Or(Atom("p"), Atom("q"))])
        node = ProofNode(seq)
        child_seq = Sequent([], [Atom("p")])
        node.add_child(child_seq)
        node.rule_applied = "∨R₁"
        latex = self._build_latex(node)
        self.assertIn("\\lor R", latex)

    def test_or_r2_label(self):
        seq = Sequent([], [Or(Atom("p"), Atom("q"))])
        node = ProofNode(seq)
        child_seq = Sequent([], [Atom("q")])
        node.add_child(child_seq)
        node.rule_applied = "∨R₂"
        latex = self._build_latex(node)
        self.assertIn("\\lor R", latex)

    def test_trust_says_label(self):
        seq = Sequent([Says("fp", Atom("p"))], [Atom("q")])
        node = ProofNode(seq)
        child_seq = Sequent([Says("admin", Atom("p"))], [Atom("q")])
        node.add_child(child_seq)
        node.rule_applied = "≤-says"
        latex = self._build_latex(node)
        self.assertIn("\\leq\\mbox{-}\\mathbf{says}", latex)

    def test_cut_prime_label(self):
        seq = Sequent([Atom("a"), Atom("b")], [Atom("d")])
        node = ProofNode(seq)
        node.add_child(Sequent([Atom("a")], [Atom("P")]))
        node.add_child(Sequent([Atom("b"), Atom("P")], [Atom("d")]))
        node.rule_applied = "cut'"
        latex = self._build_latex(node)
        self.assertIn("\\ms{cut}'", latex)

    def test_says_to_latex(self):
        """Says formula LaTeX uses \\says and \\mi."""
        s = Says("admin", Atom("p"))
        self.assertIn("\\says", s.to_latex())
        self.assertIn("\\mi{admin}", s.to_latex())

    def test_aff_to_latex(self):
        a = Aff("admin", Atom("p"))
        self.assertIn("\\aff", a.to_latex())
        self.assertIn("\\mi{admin}", a.to_latex())

    def test_sequent_to_latex_empty(self):
        """Empty sides should use \\cdot."""
        seq = Sequent([], [])
        latex = seq.to_latex()
        self.assertEqual(latex.count("\\cdot"), 2)
        self.assertIn("\\vdash", latex)

    def test_sequent_to_latex_nonempty(self):
        seq = Sequent([Atom("p")], [Atom("q")])
        latex = seq.to_latex()
        self.assertIn("p", latex)
        self.assertIn("q", latex)
        self.assertIn("\\vdash", latex)
        self.assertNotIn("\\cdot", latex)


# ============================================================================
# Additional edge case tests
# ============================================================================

class TestRuleInteractions(unittest.TestCase):
    """Test applying multiple rules in sequence (workflow tests)."""

    def setUp(self):
        self.app = MockApp()

    def test_says_r_then_aff(self):
        """saysR followed by aff should unwrap completely:
        ⊢ admin says p  →  ⊢ admin aff p  →  ⊢ p"""
        says = Says("admin", Atom("p"))
        node = self.app._setup_sequent([], [says], side="rhs", index=0)
        self.app.rule_says_r()

        child = node.children[0]
        self.assertIsInstance(child.sequent.rhs[0], Aff)

        # Now apply aff to child
        self.app.current_proof_node = child
        self.app.selected_side = "rhs"
        self.app.selected_formula_index = 0
        self.app.rule_aff()

        grandchild = child.children[0]
        self.assertEqual(grandchild.sequent.rhs, [Atom("p")])

    def test_says_l_unwraps_inner(self):
        """saysL should extract the inner formula to LHS."""
        says = Says("admin", Implies(Atom("a"), Atom("b")))
        aff = Aff("admin", Atom("q"))
        node = self.app._setup_sequent([says], [aff], side="lhs", index=0)
        self.app.rule_says_l()
        child = node.children[0]
        # Inner formula should be on LHS
        self.assertIn(Implies(Atom("a"), Atom("b")), child.sequent.lhs)

    def test_cannot_apply_to_closed_branch(self):
        """Rules should not apply to closed branches."""
        says = Says("admin", Atom("p"))
        node = self.app._setup_sequent([], [says], side="rhs", index=0)
        node.is_closed = True
        self.app.rule_says_r()
        self.assertEqual(len(node.children), 0)

    def test_cannot_apply_to_non_leaf(self):
        """Rules should not apply to nodes with children."""
        says = Says("admin", Atom("p"))
        node = self.app._setup_sequent([], [says], side="rhs", index=0)
        node.add_child(Sequent([], [Atom("dummy")]))
        self.app.rule_says_r()
        # Should still have only 1 child (the pre-existing one)
        self.assertEqual(len(node.children), 1)

    def test_no_selection(self):
        """Rules should handle no formula selected."""
        self.app.current_proof_node = ProofNode(Sequent([], []))
        self.app.selected_formula_index = None
        self.app.selected_side = None
        self.app.rule_says_r()
        # Should not crash


class TestProofNodeStructure(unittest.TestCase):

    def test_add_child(self):
        parent_seq = Sequent([Atom("a")], [Atom("b")])
        parent = ProofNode(parent_seq)
        child_seq = Sequent([Atom("a")], [Atom("c")])
        child = parent.add_child(child_seq)
        self.assertEqual(len(parent.children), 1)
        self.assertEqual(child.parent, parent)
        self.assertEqual(child.sequent, child_seq)

    def test_initial_state(self):
        seq = Sequent([], [])
        node = ProofNode(seq)
        self.assertIsNone(node.parent)
        self.assertEqual(node.children, [])
        self.assertIsNone(node.rule_applied)
        self.assertFalse(node.is_closed)


if __name__ == "__main__":
    unittest.main()
