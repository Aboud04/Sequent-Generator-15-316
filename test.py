import unittest
import tkinter as tk
from unittest.mock import MagicMock
from sequentGen import SequentProverApp, LogicParser, ProofNode, Sequent, And, Or, Implies, Not, Atom

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

    @classmethod
    def tearDownClass(cls):
        cls.root.destroy()

if __name__ == '__main__':
    unittest.main()