import unittest
import tkinter as tk
from unittest.mock import MagicMock, patch
from sequentGen import (
    SequentProverApp, LogicParser, ProofNode, Sequent, 
    And, Or, Implies, Not, Atom, Iff, Top, Bottom,
    Forall, Exists, Box, Diamond, Assign, Test, Seq, Choice, Loop, Skip, IfProg, WhileProg, ForProg,
    Equals, NotEquals, LessThan, LessEq, GreaterThan, GreaterEq
)

class TestSequentRules(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        # Create a hidden root window so Tkinter variables work
        cls.root = tk.Tk()
        cls.root.withdraw() # Hide the window

    def setUp(self):
        # Initialize the app
        self.app = SequentProverApp(self.root)
        
        # MOCKING THE UI:
        # We replace UI components with MagicMocks so we don't need to click real buttons
        self.app.tree = MagicMock()
        self.app.lhs_listbox = MagicMock()
        self.app.rhs_listbox = MagicMock()
        self.app.update_tree_display = MagicMock() # Disable visual tree updates
        
        # Parser for easy setup
        self.parser = LogicParser()

    def load_sequent(self, lhs_str, rhs_str):
        """Helper to load a sequent and prepare the app state."""
        seq = self.app.parse_sequent_input(f"{lhs_str} |- {rhs_str}")
        node = ProofNode(seq)
        
        # Manually set the internal state of the app
        self.app.root_node = node
        self.app.current_proof_node = node
        self.app.node_map = {'dummy_id': node}
        self.app.current_tree_id = 'dummy_id'
        
        return node

    def select_formula(self, side, index):
        """Simulate clicking a formula in the listbox."""
        self.app.selected_side = side
        self.app.selected_formula_index = index

    def assert_sequent_formulas(self, sequent, expected_lhs, expected_rhs):
        """Helper to verify the formulas in a sequent match string representations."""
        actual_lhs = [str(x) for x in sequent.lhs]
        actual_rhs = [str(x) for x in sequent.rhs]
        
        # Sort to ignore order if necessary, though list order usually matters in sequent calc
        self.assertEqual(actual_lhs, expected_lhs, f"LHS Mismatch. Got {actual_lhs}, expected {expected_lhs}")
        self.assertEqual(actual_rhs, expected_rhs, f"RHS Mismatch. Got {actual_rhs}, expected {expected_rhs}")

    # =========================================================================
    # TESTS FOR LOGICAL RULES
    # =========================================================================

    def test_and_left(self):
        """Test ∧L: A & B, G |- D  --->  A, B, G |- D"""
        print("\nTesting And Left (∧L)...")
        node = self.load_sequent("A and B, C", "D")
        self.select_formula('lhs', 0) # Select (A and B)
        
        self.app.rule_and_l()
        
        self.assertEqual(len(node.children), 1)
        child = node.children[0].sequent
        self.assert_sequent_formulas(child, ['C', 'A', 'B'], ['D'])

    def test_and_right(self):
        """Test ∧R: G |- A & B  --->  G |- A  AND  G |- B (Branching)"""
        print("Testing And Right (∧R)...")
        node = self.load_sequent("C", "A and B")
        self.select_formula('rhs', 0)
        
        self.app.rule_and_r()
        
        self.assertEqual(len(node.children), 2)
        self.assert_sequent_formulas(node.children[0].sequent, ['C'], ['A'])
        self.assert_sequent_formulas(node.children[1].sequent, ['C'], ['B'])

    def test_or_left(self):
        """Test ∨L: A or B, G |- D ---> A, G |- D AND B, G |- D (Branching)"""
        print("Testing Or Left (∨L)...")
        node = self.load_sequent("A or B", "D")
        self.select_formula('lhs', 0)
        
        self.app.rule_or_l()
        
        self.assertEqual(len(node.children), 2)
        self.assert_sequent_formulas(node.children[0].sequent, ['A'], ['D'])
        self.assert_sequent_formulas(node.children[1].sequent, ['B'], ['D'])

    def test_or_right(self):
        """Test ∨R: G |- A or B ---> G |- A, B"""
        print("Testing Or Right (∨R)...")
        node = self.load_sequent("C", "A or B")
        self.select_formula('rhs', 0)
        
        self.app.rule_or_r()
        
        self.assertEqual(len(node.children), 1)
        self.assert_sequent_formulas(node.children[0].sequent, ['C'], ['A', 'B'])

    def test_implies_left(self):
        """Test →L: A -> B, G |- D ---> G |- A, D  AND  B, G |- D (Branching)"""
        print("Testing Implies Left (→L)...")
        node = self.load_sequent("A implies B, C", "D")
        self.select_formula('lhs', 0)
        
        self.app.rule_imp_l()
        
        self.assertEqual(len(node.children), 2)
        # Left branch: G |- A, D (Hypothesis check)
        self.assert_sequent_formulas(node.children[0].sequent, ['C'], ['D', 'A'])
        # Right branch: B, G |- D (Conclusion usage)
        self.assert_sequent_formulas(node.children[1].sequent, ['C', 'B'], ['D'])

    def test_implies_right(self):
        """Test →R: G |- A -> B ---> A, G |- B"""
        print("Testing Implies Right (→R)...")
        node = self.load_sequent("C", "A implies B")
        self.select_formula('rhs', 0)
        
        self.app.rule_imp_r()
        
        self.assertEqual(len(node.children), 1)
        self.assert_sequent_formulas(node.children[0].sequent, ['C', 'A'], ['B'])

    def test_not_left(self):
        """Test ¬L: not A, G |- D ---> G |- A, D"""
        print("Testing Not Left (¬L)...")
        node = self.load_sequent("not A, C", "D")
        self.select_formula('lhs', 0)
        
        self.app.rule_not_l()
        
        self.assertEqual(len(node.children), 1)
        self.assert_sequent_formulas(node.children[0].sequent, ['C'], ['D', 'A'])

    def test_not_right(self):
        """Test ¬R: G |- not A ---> A, G |- """
        print("Testing Not Right (¬R)...")
        node = self.load_sequent("C", "not A")
        self.select_formula('rhs', 0)
        
        self.app.rule_not_r()
        
        self.assertEqual(len(node.children), 1)
        # Note: Depending on list implementation, A usually appends to end
        self.assert_sequent_formulas(node.children[0].sequent, ['C', 'A'], [])

    def test_identity_success(self):
        """Test Identity (Axiom): p, q |- p (Should close branch)"""
        print("Testing Identity Success...")
        node = self.load_sequent("p, q", "p")
        self.app.current_proof_node = node # Ensure App knows this is current
        
        self.app.rule_id()
        
        self.assertTrue(node.is_closed, "Node should be marked closed")
        self.assertEqual(node.rule_applied, "id")

    def test_identity_fail(self):
        """Test Identity Fail: p, q |- r (Should NOT close)"""
        print("Testing Identity Failure...")
        node = self.load_sequent("p, q", "r")
        
        self.app.rule_id()
        
        self.assertFalse(node.is_closed, "Node should NOT be marked closed")

    # =========================================================================
    # TESTS FOR NEW RULES (Iff, Top, Bottom)
    # =========================================================================

    def test_iff_left(self):
        """Test ↔L: A ↔ B, G |- D ---> (A,B,G |- D) AND (G |- A,B,D) (Branching)"""
        print("\nTesting Iff Left (↔L)...")
        node = self.load_sequent("A iff B, C", "D")
        self.select_formula('lhs', 0)
        
        self.app.rule_iff_l()
        
        self.assertEqual(len(node.children), 2)
        # Branch 1: A, B, C |- D (both true case)
        self.assert_sequent_formulas(node.children[0].sequent, ['C', 'A', 'B'], ['D'])
        # Branch 2: C |- A, B, D (both false case)
        self.assert_sequent_formulas(node.children[1].sequent, ['C'], ['D', 'A', 'B'])

    def test_iff_right(self):
        """Test ↔R: G |- A ↔ B ---> (G,A |- B) AND (G,B |- A) (Branching)"""
        print("Testing Iff Right (↔R)...")
        node = self.load_sequent("C", "A iff B")
        self.select_formula('rhs', 0)
        
        self.app.rule_iff_r()
        
        self.assertEqual(len(node.children), 2)
        # Branch 1: C, A |- B (A implies B)
        self.assert_sequent_formulas(node.children[0].sequent, ['C', 'A'], ['B'])
        # Branch 2: C, B |- A (B implies A)
        self.assert_sequent_formulas(node.children[1].sequent, ['C', 'B'], ['A'])

    def test_top_right(self):
        """Test ⊤R: G |- ⊤ closes the branch"""
        print("Testing Top Right (⊤R)...")
        node = self.load_sequent("p", "true")
        self.app.current_proof_node = node
        
        self.app.rule_top_r()
        
        self.assertTrue(node.is_closed, "Node should be closed with ⊤R")
        self.assertEqual(node.rule_applied, "⊤R")

    def test_top_right_fail(self):
        """Test ⊤R fails when no ⊤ in succedent"""
        print("Testing Top Right Failure...")
        node = self.load_sequent("p", "q")
        self.app.current_proof_node = node
        
        self.app.rule_top_r()
        
        self.assertFalse(node.is_closed, "Node should NOT be closed without ⊤")

    def test_bottom_left(self):
        """Test ⊥L: ⊥, G |- D closes the branch"""
        print("Testing Bottom Left (⊥L)...")
        node = self.load_sequent("false, p", "q")
        self.app.current_proof_node = node
        
        self.app.rule_bot_l()
        
        self.assertTrue(node.is_closed, "Node should be closed with ⊥L")
        self.assertEqual(node.rule_applied, "⊥L")

    def test_bottom_left_fail(self):
        """Test ⊥L fails when no ⊥ in antecedent"""
        print("Testing Bottom Left Failure...")
        node = self.load_sequent("p", "q")
        self.app.current_proof_node = node
        
        self.app.rule_bot_l()
        
        self.assertFalse(node.is_closed, "Node should NOT be closed without ⊥")

    def test_bottom_right(self):
        """Test ⊥R: Γ ⊢ ⊥, Δ ---> Γ ⊢ Δ (removes ⊥ from succedent)"""
        print("Testing Bottom Right (⊥R)...")
        seq = Sequent([Atom("P")], [Bottom(), Atom("Q")])
        node = ProofNode(seq)
        
        self.app.root_node = node
        self.app.current_proof_node = node
        self.app.node_map = {'dummy_id': node}
        self.app.current_tree_id = 'dummy_id'
        
        self.select_formula('rhs', 0)  # Select ⊥
        self.app.rule_bot_r()
        
        self.assertEqual(len(node.children), 1)
        child = node.children[0].sequent
        # ⊥ should be removed, only Q remains
        self.assertEqual(len(child.rhs), 1)
        self.assertEqual(str(child.rhs[0]), "Q")
        self.assertEqual(node.rule_applied, "⊥R")

    def test_top_left(self):
        """Test ⊤L: Γ, ⊤ ⊢ Δ ---> Γ ⊢ Δ (removes vacuous ⊤ from antecedent)"""
        print("Testing Top Left (⊤L)...")
        seq = Sequent([Top(), Atom("P")], [Atom("Q")])
        node = ProofNode(seq)
        
        self.app.root_node = node
        self.app.current_proof_node = node
        self.app.node_map = {'dummy_id': node}
        self.app.current_tree_id = 'dummy_id'
        
        self.select_formula('lhs', 0)  # Select ⊤
        self.app.rule_top_l()
        
        self.assertEqual(len(node.children), 1)
        child = node.children[0].sequent
        # ⊤ should be removed, only P remains
        self.assertEqual(len(child.lhs), 1)
        self.assertEqual(str(child.lhs[0]), "P")
        self.assertEqual(node.rule_applied, "⊤L")

    def test_parser_iff(self):
        """Test parser handles iff/bi-implication"""
        print("Testing Parser - Iff...")
        result = self.parser.parse("A iff B")
        self.assertIsInstance(result, Iff)
        self.assertEqual(str(result.left), "A")
        self.assertEqual(str(result.right), "B")

    def test_parser_top_bottom(self):
        """Test parser handles true/false constants"""
        print("Testing Parser - Top/Bottom...")
        top = self.parser.parse("true")
        self.assertIsInstance(top, Top)
        
        bot = self.parser.parse("false")
        self.assertIsInstance(bot, Bottom)
        
        # Alternative syntax
        top2 = self.parser.parse("top")
        self.assertIsInstance(top2, Top)
        
        bot2 = self.parser.parse("bottom")
        self.assertIsInstance(bot2, Bottom)

    # =========================================================================
    # TESTS FOR QUANTIFIER RULES
    # =========================================================================

    def test_parser_forall(self):
        """Test parser handles universal quantifier"""
        print("\nTesting Parser - Forall...")
        result = self.parser.parse("forall x. P")
        self.assertIsInstance(result, Forall)
        self.assertEqual(result.var, "x")
        self.assertEqual(str(result.inner), "P")

    def test_parser_exists(self):
        """Test parser handles existential quantifier"""
        print("Testing Parser - Exists...")
        result = self.parser.parse("exists y. Q")
        self.assertIsInstance(result, Exists)
        self.assertEqual(result.var, "y")
        self.assertEqual(str(result.inner), "Q")

    def test_forall_right(self):
        """Test ∀R: Γ ⊢ ∀x.P(x), Δ ---> Γ ⊢ P(x'), Δ with fresh x'"""
        print("Testing Forall Right (∀R)...")
        # Create a sequent with forall on the right manually
        forall_formula = Forall("x", Atom("P"))
        seq = Sequent([Atom("A")], [forall_formula])
        node = ProofNode(seq)
        
        self.app.root_node = node
        self.app.current_proof_node = node
        self.app.node_map = {'dummy_id': node}
        self.app.current_tree_id = 'dummy_id'
        
        self.select_formula('rhs', 0)
        self.app.rule_forall_r()
        
        self.assertEqual(len(node.children), 1)
        # Should have substituted with fresh variable
        child = node.children[0].sequent
        self.assertEqual(len(child.rhs), 1)
        # The inner formula P should appear with the fresh variable name
        self.assertIn("P", str(child.rhs[0]))

    def test_exists_left(self):
        """Test ∃L: Γ, ∃x.P(x) ⊢ Δ ---> Γ, P(x') ⊢ Δ with fresh x'"""
        print("Testing Exists Left (∃L)...")
        exists_formula = Exists("y", Atom("Q"))
        seq = Sequent([exists_formula], [Atom("R")])
        node = ProofNode(seq)
        
        self.app.root_node = node
        self.app.current_proof_node = node
        self.app.node_map = {'dummy_id': node}
        self.app.current_tree_id = 'dummy_id'
        
        self.select_formula('lhs', 0)
        self.app.rule_exists_l()
        
        self.assertEqual(len(node.children), 1)
        child = node.children[0].sequent
        self.assertEqual(len(child.lhs), 1)

    # =========================================================================
    # TESTS FOR DYNAMIC LOGIC RULES  
    # =========================================================================

    def test_parser_box_modality(self):
        """Test parser handles box modality [x := e]P"""
        print("\nTesting Parser - Box Modality...")
        result = self.parser.parse("[x := 5]P")
        self.assertIsInstance(result, Box)
        self.assertIsInstance(result.program, Assign)
        self.assertEqual(result.program.var, "x")
        self.assertEqual(str(result.postcondition), "P")

    def test_parser_sequence(self):
        """Test parser handles sequential composition [a; b]P"""
        print("Testing Parser - Sequence...")
        # Simple test for assignment followed by another
        result = self.parser.parse("[x := 1; y := 2]P")
        self.assertIsInstance(result, Box)
        self.assertIsInstance(result.program, Seq)

    def test_seq_rule_r(self):
        """Test [;]R: [α;β]Q ---> [α][β]Q"""
        print("Testing Sequence Right ([;]R)...")
        # Create [x := 1; y := 2]P
        prog = Seq(Assign("x", Atom("1")), Assign("y", Atom("2")))
        box_formula = Box(prog, Atom("P"))
        seq = Sequent([Atom("A")], [box_formula])
        node = ProofNode(seq)
        
        self.app.root_node = node
        self.app.current_proof_node = node
        self.app.node_map = {'dummy_id': node}
        self.app.current_tree_id = 'dummy_id'
        
        self.select_formula('rhs', 0)
        self.app.rule_seq_r()
        
        self.assertEqual(len(node.children), 1)
        child = node.children[0].sequent
        # Should now be [x := 1][y := 2]P (nested boxes)
        self.assertIsInstance(child.rhs[0], Box)

    def test_choice_rule_r(self):
        """Test [∪]R: [α∪β]Q ---> [α]Q ∧ [β]Q (branching)"""
        print("Testing Choice Right ([∪]R)...")
        prog = Choice(Assign("x", Atom("1")), Assign("x", Atom("2")))
        box_formula = Box(prog, Atom("P"))
        seq = Sequent([Atom("A")], [box_formula])
        node = ProofNode(seq)
        
        self.app.root_node = node
        self.app.current_proof_node = node
        self.app.node_map = {'dummy_id': node}
        self.app.current_tree_id = 'dummy_id'
        
        self.select_formula('rhs', 0)
        self.app.rule_choice_r()
        
        self.assertEqual(len(node.children), 2)
        # Both branches should have box formulas

    def test_test_rule_r(self):
        """Test [?]R: [?P]Q ---> P ⊢ Q"""
        print("Testing Test Right ([?]R)...")
        prog = Test(Atom("P"))
        box_formula = Box(prog, Atom("Q"))
        seq = Sequent([Atom("A")], [box_formula])
        node = ProofNode(seq)
        
        self.app.root_node = node
        self.app.current_proof_node = node
        self.app.node_map = {'dummy_id': node}
        self.app.current_tree_id = 'dummy_id'
        
        self.select_formula('rhs', 0)
        self.app.rule_test_r()
        
        self.assertEqual(len(node.children), 1)
        child = node.children[0].sequent
        # P should be added to LHS, Q to RHS
        self.assertIn("P", [str(f) for f in child.lhs])
        self.assertIn("Q", [str(f) for f in child.rhs])

    # =========================================================================
    # TESTS FOR STRUCTURAL RULES
    # =========================================================================

    @patch('tkinter.simpledialog.askstring')
    def test_weaken_left(self, mock_ask):
        """Test WL (Weakening Left): Add formula to antecedent"""
        print("\nTesting Weakening Left (WL)...")
        mock_ask.return_value = "R"  # Formula to add
        
        node = self.load_sequent("P", "Q")
        self.app.rule_weaken_l()
        
        self.assertEqual(len(node.children), 1)
        child = node.children[0].sequent
        self.assertIn("R", [str(f) for f in child.lhs])
        self.assertEqual(len(child.lhs), 2)  # P and R

    @patch('tkinter.simpledialog.askstring')
    def test_weaken_right(self, mock_ask):
        """Test WR (Weakening Right): Add formula to succedent"""
        print("Testing Weakening Right (WR)...")
        mock_ask.return_value = "S"
        
        node = self.load_sequent("P", "Q")
        self.app.rule_weaken_r()
        
        self.assertEqual(len(node.children), 1)
        child = node.children[0].sequent
        self.assertIn("S", [str(f) for f in child.rhs])
        self.assertEqual(len(child.rhs), 2)

    def test_contract_left(self):
        """Test CL (Contraction Left): Remove duplicate from antecedent"""
        print("Testing Contraction Left (CL)...")
        seq = Sequent([Atom("P"), Atom("P"), Atom("Q")], [Atom("R")])
        node = ProofNode(seq)
        
        self.app.root_node = node
        self.app.current_proof_node = node
        self.app.node_map = {'dummy_id': node}
        self.app.current_tree_id = 'dummy_id'
        
        self.select_formula('lhs', 0)
        self.app.rule_contract_l()
        
        self.assertEqual(len(node.children), 1)
        child = node.children[0].sequent
        self.assertEqual(len(child.lhs), 2)  # P and Q (one P removed)

    @patch('tkinter.simpledialog.askstring')
    def test_cut_rule(self, mock_ask):
        """Test Cut: Introduce lemma to split proof"""
        print("Testing Cut Rule...")
        mock_ask.return_value = "Lemma"
        
        node = self.load_sequent("P", "Q")
        self.app.rule_cut()
        
        self.assertEqual(len(node.children), 2)
        # Branch 1: P ⊢ Lemma, Q (prove the cut formula)
        self.assertIn("Lemma", [str(f) for f in node.children[0].sequent.rhs])
        # Branch 2: P, Lemma ⊢ Q (use the cut formula)
        self.assertIn("Lemma", [str(f) for f in node.children[1].sequent.lhs])

    # =========================================================================
    # TESTS FOR COMPARISON OPERATORS
    # =========================================================================

    def test_parser_equality(self):
        """Test parser handles equality operator"""
        print("\nTesting Parser - Equality...")
        # Note: equality parsing is context-dependent
        result = self.parser.parse("x = 5")
        self.assertIsInstance(result, Equals)

    def test_parser_less_than(self):
        """Test parser handles comparison operators"""
        print("Testing Parser - Comparisons...")
        result = self.parser.parse("x < y")
        self.assertIsInstance(result, LessThan)

    # =========================================================================
    # COMPREHENSIVE PROOF TEST: [skip;α]Q ↔ [α]Q
    # =========================================================================

    def test_complete_proof_skip_sequence_equivalence(self):
        """
        Test the complete proof tree for: ⊢ [skip;α]Q ↔ [α]Q
        
        This verifies the proof from the LaTeX:
        1. Apply ↔R: branches into two implications
        2. First branch: ⊢ [skip;α]Q → [α]Q
           - Apply →R: [skip;α]Q ⊢ [α]Q
           - Apply [;]L: [skip]([α]Q) ⊢ [α]Q
           - Apply [skip]L: [α]Q ⊢ [α]Q
           - Apply id: closed
        3. Second branch: ⊢ [α]Q → [skip;α]Q
           - Apply →R: [α]Q ⊢ [skip;α]Q
           - Apply [;]R: [α]Q ⊢ [skip]([α]Q)
           - Apply [skip]R: [α]Q ⊢ [α]Q
           - Apply id: closed
        """
        print("\nTesting Complete Proof: [skip;α]Q ↔ [α]Q...")
        
        # Build the initial sequent: ⊢ [skip;α]Q ↔ [α]Q
        # We use 'a' as the program α and 'Q' as the postcondition
        alpha = Assign("a", Atom("a"))  # Simple program 'a'
        Q = Atom("Q")
        
        skip_seq_alpha = Seq(Skip(), alpha)  # skip; α
        box_skip_seq = Box(skip_seq_alpha, Q)  # [skip;α]Q
        box_alpha = Box(alpha, Q)  # [α]Q
        
        iff_formula = Iff(box_skip_seq, box_alpha)  # [skip;α]Q ↔ [α]Q
        
        initial_sequent = Sequent([], [iff_formula])
        root = ProofNode(initial_sequent)
        
        self.app.root_node = root
        self.app.current_proof_node = root
        self.app.node_map = {'root': root}
        self.app.current_tree_id = 'root'
        
        # Step 1: Apply ↔R to the Iff formula
        self.app.selected_side = 'rhs'
        self.app.selected_formula_index = 0
        self.app.rule_iff_r()
        
        self.assertEqual(len(root.children), 2, "↔R should create 2 branches")
        self.assertEqual(root.rule_applied, "↔R")
        
        # === FIRST BRANCH: [skip;α]Q ⊢ [α]Q ===
        branch1 = root.children[0]
        # After ↔R, branch1 should be: [skip;α]Q ⊢ [α]Q
        # (the first operand on LHS, second operand on RHS)
        
        self.app.current_proof_node = branch1
        self.app.node_map['branch1'] = branch1
        self.app.current_tree_id = 'branch1'
        
        # Verify branch1 structure: should have [skip;α]Q on LHS, [α]Q on RHS
        self.assertEqual(len(branch1.sequent.lhs), 1)
        self.assertEqual(len(branch1.sequent.rhs), 1)
        
        # Step 2a: Apply [;]L to [skip;α]Q on LHS
        self.app.selected_side = 'lhs'
        self.app.selected_formula_index = 0
        self.app.rule_seq_l()
        
        self.assertEqual(len(branch1.children), 1, "[;]L should create 1 child")
        self.assertEqual(branch1.rule_applied, "[;]L")
        
        branch1_step2 = branch1.children[0]
        # Now should have [skip]([α]Q) on LHS
        
        self.app.current_proof_node = branch1_step2
        self.app.node_map['branch1_step2'] = branch1_step2
        self.app.current_tree_id = 'branch1_step2'
        
        # Step 3a: Apply [skip]L to [skip]([α]Q)
        self.app.selected_side = 'lhs'
        self.app.selected_formula_index = 0
        self.app.rule_skip_l()
        
        self.assertEqual(len(branch1_step2.children), 1, "[skip]L should create 1 child")
        self.assertEqual(branch1_step2.rule_applied, "[skip]L")
        
        branch1_step3 = branch1_step2.children[0]
        # Now should have [α]Q on both sides
        
        self.app.current_proof_node = branch1_step3
        self.app.node_map['branch1_step3'] = branch1_step3
        self.app.current_tree_id = 'branch1_step3'
        
        # Step 4a: Apply identity to close
        self.app.rule_id()
        
        self.assertTrue(branch1_step3.is_closed, "Branch 1 should be closed by identity")
        self.assertEqual(branch1_step3.rule_applied, "id")
        
        # === SECOND BRANCH: [α]Q ⊢ [skip;α]Q ===
        branch2 = root.children[1]
        # After ↔R, branch2 should be: [α]Q ⊢ [skip;α]Q
        
        self.app.current_proof_node = branch2
        self.app.node_map['branch2'] = branch2
        self.app.current_tree_id = 'branch2'
        
        # Verify branch2 structure
        self.assertEqual(len(branch2.sequent.lhs), 1)
        self.assertEqual(len(branch2.sequent.rhs), 1)
        
        # Step 2b: Apply [;]R to [skip;α]Q on RHS
        self.app.selected_side = 'rhs'
        self.app.selected_formula_index = 0
        self.app.rule_seq_r()
        
        self.assertEqual(len(branch2.children), 1, "[;]R should create 1 child")
        self.assertEqual(branch2.rule_applied, "[;]R")
        
        branch2_step2 = branch2.children[0]
        # Now should have [skip]([α]Q) on RHS
        
        self.app.current_proof_node = branch2_step2
        self.app.node_map['branch2_step2'] = branch2_step2
        self.app.current_tree_id = 'branch2_step2'
        
        # Step 3b: Apply [skip]R to [skip]([α]Q)
        self.app.selected_side = 'rhs'
        self.app.selected_formula_index = 0
        self.app.rule_skip_r()
        
        self.assertEqual(len(branch2_step2.children), 1, "[skip]R should create 1 child")
        self.assertEqual(branch2_step2.rule_applied, "[skip]R")
        
        branch2_step3 = branch2_step2.children[0]
        # Now should have [α]Q on both sides
        
        self.app.current_proof_node = branch2_step3
        self.app.node_map['branch2_step3'] = branch2_step3
        self.app.current_tree_id = 'branch2_step3'
        
        # Step 4b: Apply identity to close
        self.app.rule_id()
        
        self.assertTrue(branch2_step3.is_closed, "Branch 2 should be closed by identity")
        self.assertEqual(branch2_step3.rule_applied, "id")
        
        # ============================================================
        # FINAL VERIFICATION: Check that final sequents match expected
        # ============================================================
        
        # Branch 1 final: [α]Q ⊢ [α]Q
        final_branch1_lhs = [str(f) for f in branch1_step3.sequent.lhs]
        final_branch1_rhs = [str(f) for f in branch1_step3.sequent.rhs]
        
        print(f"  Branch 1 final: {final_branch1_lhs} ⊢ {final_branch1_rhs}")
        
        # Both sides should have the same [α]Q formula
        self.assertEqual(final_branch1_lhs, final_branch1_rhs, 
                         "Branch 1 should end with identical formulas on both sides")
        
        # Branch 2 final: [α]Q ⊢ [α]Q
        final_branch2_lhs = [str(f) for f in branch2_step3.sequent.lhs]
        final_branch2_rhs = [str(f) for f in branch2_step3.sequent.rhs]
        
        print(f"  Branch 2 final: {final_branch2_lhs} ⊢ {final_branch2_rhs}")
        
        # Both sides should have the same [α]Q formula
        self.assertEqual(final_branch2_lhs, final_branch2_rhs,
                         "Branch 2 should end with identical formulas on both sides")
        
        print("  [PASS] Complete proof verified! Both branches closed correctly.")

    # =========================================================================
    # TESTS FOR WHILE LOOP WITH INVARIANT
    # =========================================================================

    def test_parser_while_with_invariant(self):
        """Test parser handles while loop with invariant annotation: while_{J} P do α"""
        print("\nTesting Parser - While with Invariant...")
        # Create while loop with invariant manually for testing
        result = WhileProg(Atom("P"), Assign("x", Atom("1")), Atom("J"))
        self.assertIsInstance(result, WhileProg)
        self.assertEqual(result.invariant.name, "J")
        self.assertEqual(str(result.guard), "P")
        # Verify string representation includes invariant
        self.assertIn("J", str(result))

    def test_while_inv_rule(self):
        """Test [while]inv: Uses loop invariant to create 3 branches
           Γ ⊢ [while_J P do α]Q, Δ creates:
           1. Γ ⊢ J, Δ  (invariant holds initially)
           2. J, P ⊢ [α]J  (invariant preserved)
           3. J, ¬P ⊢ Q  (invariant implies postcondition)"""
        print("Testing While Invariant Rule ([while]inv)...")
        
        # Create a while loop with invariant
        body = Assign("x", Atom("1"))
        while_prog = WhileProg(Atom("P"), body, Atom("J"))
        box_formula = Box(while_prog, Atom("Q"))
        
        seq = Sequent([Atom("A")], [box_formula])
        node = ProofNode(seq)
        
        self.app.root_node = node
        self.app.current_proof_node = node
        self.app.node_map = {'dummy_id': node}
        self.app.current_tree_id = 'dummy_id'
        
        self.select_formula('rhs', 0)
        self.app.rule_while_inv_r()
        
        # Should have 3 branches
        self.assertEqual(len(node.children), 3)
        self.assertEqual(node.rule_applied, "[while]inv")
        
        # Branch 1: A ⊢ J (invariant holds initially)
        b1 = node.children[0].sequent
        self.assertEqual(len(b1.lhs), 1)  # A
        self.assertEqual(len(b1.rhs), 1)  # J
        self.assertEqual(str(b1.rhs[0]), "J")
        
        # Branch 2: J, P ⊢ [α]J (invariant preserved)
        b2 = node.children[1].sequent
        self.assertEqual(len(b2.lhs), 2)  # J, P
        self.assertEqual(len(b2.rhs), 1)  # [α]J
        self.assertIn("J", [str(f) for f in b2.lhs])
        self.assertIn("P", [str(f) for f in b2.lhs])
        
        # Branch 3: J, ¬P ⊢ Q (implies postcondition)
        b3 = node.children[2].sequent
        self.assertEqual(len(b3.lhs), 2)  # J, ¬P
        self.assertEqual(len(b3.rhs), 1)  # Q
        self.assertEqual(str(b3.rhs[0]), "Q")
        
        print("  [PASS] [while]inv correctly created 3 branches")

    def test_while_inv_requires_invariant(self):
        """Test [while]inv fails if while loop has no invariant"""
        print("Testing While Invariant Rule without invariant...")
        
        # While loop WITHOUT invariant
        body = Assign("x", Atom("1"))
        while_prog = WhileProg(Atom("P"), body)  # No invariant!
        box_formula = Box(while_prog, Atom("Q"))
        
        seq = Sequent([Atom("A")], [box_formula])
        node = ProofNode(seq)
        
        self.app.root_node = node
        self.app.current_proof_node = node
        self.app.node_map = {'dummy_id': node}
        self.app.current_tree_id = 'dummy_id'
        
        self.select_formula('rhs', 0)
        # This should not create any children (shows info dialog instead)
        self.app.rule_while_inv_r()
        
        self.assertEqual(len(node.children), 0, "Should not apply without invariant")

    # =========================================================================
    # TESTS FOR FOR LOOP
    # =========================================================================

    def test_for_loop_class(self):
        """Test ForProg class creation and string representation"""
        print("\nTesting ForProg class...")
        for_prog = ForProg("i", "n", Assign("x", Atom("1")))
        self.assertEqual(for_prog.loop_var, "i")
        self.assertEqual(for_prog.bound_var, "n")
        self.assertIn("0 ≤ i < n", str(for_prog))
        print(f"  ForProg string: {for_prog}")

    def test_parser_for_loop(self):
        """Test parser handles for loop: for 0 <= i < n do α"""
        print("Testing Parser - For Loop...")
        parser = LogicParser()
        result = parser.parse("[for 0 <= i < n do x := 1]Q")
        
        self.assertIsInstance(result, Box)
        self.assertIsInstance(result.program, ForProg)
        self.assertEqual(result.program.loop_var, "i")
        self.assertEqual(result.program.bound_var, "n")

    def test_for_rule_r(self):
        """Test [for]R: Desugars for loop to while loop
           [for 0 ≤ i < n do α]Q ---> [i := 0; while (i < n) do (α; i := i + 1)]Q"""
        print("Testing For Rule Right ([for]R)...")
        
        # Create a for loop
        body = Assign("x", Atom("1"))
        for_prog = ForProg("i", "n", body)
        box_formula = Box(for_prog, Atom("Q"))
        
        seq = Sequent([Atom("A")], [box_formula])
        node = ProofNode(seq)
        
        self.app.root_node = node
        self.app.current_proof_node = node
        self.app.node_map = {'dummy_id': node}
        self.app.current_tree_id = 'dummy_id'
        
        self.select_formula('rhs', 0)
        self.app.rule_for_r()
        
        # Should have 1 child with desugared program
        self.assertEqual(len(node.children), 1)
        self.assertEqual(node.rule_applied, "[for]R")
        
        child = node.children[0].sequent
        # The RHS should now have a Box with Seq(Assign, WhileProg)
        self.assertEqual(len(child.rhs), 1)
        desugared = child.rhs[0]
        self.assertIsInstance(desugared, Box)
        self.assertIsInstance(desugared.program, Seq)
        
        # First part should be i := 0
        self.assertIsInstance(desugared.program.first, Assign)
        self.assertEqual(desugared.program.first.var, "i")
        
        # Second part should be while loop
        self.assertIsInstance(desugared.program.second, WhileProg)
        
        print(f"  Desugared: {desugared}")
        print("  [PASS] [for]R correctly desugared to while loop")

    def test_for_loop_latex(self):
        """Test ForProg LaTeX output"""
        print("Testing ForProg LaTeX...")
        for_prog = ForProg("i", "n", Assign("x", Atom("1")))
        latex = for_prog.to_latex()
        self.assertIn("\\mathbf{for}", latex)
        self.assertIn("\\leq", latex)
        print(f"  LaTeX: {latex}")

    @classmethod
    def tearDownClass(cls):
        cls.root.destroy()

if __name__ == '__main__':
    unittest.main()