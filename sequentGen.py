import tkinter as tk
from tkinter import ttk, messagebox, font
import re
import json
import os

class Formula:
    def __repr__(self):
        return str(self)

    def to_latex(self):
        raise NotImplementedError


class Atom(Formula):
    def __init__(self, name):
        self.name = name.strip()

    def __str__(self):
        return self.name

    def to_latex(self):
        return self.name

    def __eq__(self, other):
        return isinstance(other, Atom) and self.name == other.name


class Not(Formula):
    def __init__(self, inner):
        self.inner = inner

    def __str__(self):
        return f"¬{self.inner}" if isinstance(self.inner, Atom) else f"¬({self.inner})"

    def to_latex(self):
        return f"\\lnot {self.inner.to_latex()}"


class BinaryFormula(Formula):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __eq__(self, other):
        return (
            isinstance(other, self.__class__)
            and self.left == other.left
            and self.right == other.right
        )


class And(BinaryFormula):
    def __str__(self):
        return f"({self.left} ∧ {self.right})"

    def to_latex(self):
        return f"({self.left.to_latex()} \\land {self.right.to_latex()})"


class Or(BinaryFormula):
    def __str__(self):
        return f"({self.left} ∨ {self.right})"

    def to_latex(self):
        return f"({self.left.to_latex()} \\lor {self.right.to_latex()})"


class Implies(BinaryFormula):
    def __str__(self):
        return f"({self.left} → {self.right})"

    def to_latex(self):
        return f"({self.left.to_latex()} \\to {self.right.to_latex()})"


class Iff(BinaryFormula):
    """Bi-implication (logical equivalence): F ↔ G"""
    def __str__(self):
        return f"({self.left} ↔ {self.right})"

    def to_latex(self):
        return f"({self.left.to_latex()} \\leftrightarrow {self.right.to_latex()})"


class Top(Formula):
    """Logical constant for truth (⊤)"""
    def __str__(self):
        return "⊤"

    def to_latex(self):
        return "\\top"

    def __eq__(self, other):
        return isinstance(other, Top)


class Bottom(Formula):
    """Logical constant for falsity (⊥)"""
    def __str__(self):
        return "⊥"

    def to_latex(self):
        return "\\bot"

    def __eq__(self, other):
        return isinstance(other, Bottom)


# ============================================================================
# AUTHORIZATION LOGIC FORMULAS (Lectures 15-17)
# ============================================================================

class Says(Formula):
    """A says P — principal A affirms proposition P."""
    def __init__(self, principal, inner):
        self.principal = principal  # string name of principal
        self.inner = inner          # Formula

    def __str__(self):
        return f"({self.principal} says {self.inner})"

    def to_latex(self):
        return f"(\\mi{{{self.principal}}} \\says {self.inner.to_latex()})"

    def __eq__(self, other):
        return (isinstance(other, Says)
                and self.principal == other.principal
                and self.inner == other.inner)


class Aff(Formula):
    """A aff P — judgment that A affirms P."""
    def __init__(self, principal, inner):
        self.principal = principal  # string name of principal
        self.inner = inner          # Formula

    def __str__(self):
        return f"({self.principal} aff {self.inner})"

    def to_latex(self):
        return f"(\\mi{{{self.principal}}} \\aff {self.inner.to_latex()})"

    def __eq__(self, other):
        return (isinstance(other, Aff)
                and self.principal == other.principal
                and self.inner == other.inner)


# ============================================================================
# QUANTIFIER FORMULAS
# ============================================================================

class Forall(Formula):
    """Universal quantifier: ∀x. P(x)"""
    def __init__(self, var, inner):
        self.var = var  # Variable name (string)
        self.inner = inner  # Formula

    def __str__(self):
        return f"(∀{self.var}. {self.inner})"

    def to_latex(self):
        return f"(\\forall {self.var}.\\ {self.inner.to_latex()})"

    def __eq__(self, other):
        return isinstance(other, Forall) and self.var == other.var and self.inner == other.inner


class Exists(Formula):
    """Existential quantifier: ∃x. P(x)"""
    def __init__(self, var, inner):
        self.var = var
        self.inner = inner

    def __str__(self):
        return f"(∃{self.var}. {self.inner})"

    def to_latex(self):
        return f"(\\exists {self.var}.\\ {self.inner.to_latex()})"

    def __eq__(self, other):
        return isinstance(other, Exists) and self.var == other.var and self.inner == other.inner


# ============================================================================
# DYNAMIC LOGIC - PROGRAM CONSTRUCTS
# ============================================================================

class Program:
    """Base class for program constructs in dynamic logic"""
    def __repr__(self):
        return str(self)


class Assign(Program):
    """Assignment: x := e"""
    def __init__(self, var, expr):
        self.var = var  # Variable name
        self.expr = expr  # Expression (can be Atom or complex)

    def __str__(self):
        return f"{self.var} := {self.expr}"

    def to_latex(self):
        expr_tex = self.expr.to_latex() if hasattr(self.expr, 'to_latex') else str(self.expr)
        return f"{self.var} := {expr_tex}"


class Test(Program):
    """Test/Guard: ?P"""
    def __init__(self, formula):
        self.formula = formula

    def __str__(self):
        return f"?{self.formula}"

    def to_latex(self):
        return f"?{self.formula.to_latex()}"


class Seq(Program):
    """Sequential composition: α; β"""
    def __init__(self, first, second):
        self.first = first
        self.second = second

    def __str__(self):
        return f"({self.first}; {self.second})"

    def to_latex(self):
        return f"({self.first.to_latex()};\\ {self.second.to_latex()})"


class Choice(Program):
    """Non-deterministic choice: α ∪ β"""
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} ∪ {self.right})"

    def to_latex(self):
        return f"({self.left.to_latex()} \\cup {self.right.to_latex()})"


class Loop(Program):
    """Iteration/loop: α*"""
    def __init__(self, body):
        self.body = body

    def __str__(self):
        return f"({self.body})*"

    def to_latex(self):
        return f"({self.body.to_latex()})^*"


class Skip(Program):
    """Skip/no-op program: skip"""
    def __str__(self):
        return "skip"

    def to_latex(self):
        return "\\mathbf{skip}"

    def __eq__(self, other):
        return isinstance(other, Skip)


class IfProg(Program):
    """Conditional: if P then α else β"""
    def __init__(self, guard, then_branch, else_branch):
        self.guard = guard  # Formula
        self.then_branch = then_branch  # Program
        self.else_branch = else_branch  # Program

    def __str__(self):
        return f"if {self.guard} then {self.then_branch} else {self.else_branch}"

    def to_latex(self):
        return f"\\text{{if }} {self.guard.to_latex()} \\text{{ then }} {self.then_branch.to_latex()} \\text{{ else }} {self.else_branch.to_latex()}"


class WhileProg(Program):
    """While loop: while P do α (with optional invariant J)
    Syntax: while P do α  OR  while_J P do α (with invariant J)"""
    def __init__(self, guard, body, invariant=None):
        self.guard = guard  # Formula
        self.body = body  # Program
        self.invariant = invariant  # Optional loop invariant

    def __str__(self):
        if self.invariant:
            return f"while_{{{self.invariant}}} {self.guard} do {self.body}"
        return f"while {self.guard} do {self.body}"

    def to_latex(self):
        if self.invariant:
            return f"\\text{{while}}_{{{self.invariant.to_latex()}}} {self.guard.to_latex()} \\text{{ do }} {self.body.to_latex()}"
        return f"\\text{{while }} {self.guard.to_latex()} \\text{{ do }} {self.body.to_latex()}"


class ForProg(Program):
    """Bounded for loop: for 0 ≤ i < n do α
    
    The loop body α may depend on variables i and n (which must be different),
    but α may not assign to i or n.
    
    Semantically equivalent to: i := 0; while (i < n) { α; i := i + 1 }
    """
    def __init__(self, loop_var, bound_var, body):
        self.loop_var = loop_var  # Loop variable name (e.g., 'i')
        self.bound_var = bound_var  # Upper bound variable name (e.g., 'n')
        self.body = body  # Program (loop body)

    def __str__(self):
        return f"for 0 ≤ {self.loop_var} < {self.bound_var} do {self.body}"

    def to_latex(self):
        body_tex = self.body.to_latex() if hasattr(self.body, 'to_latex') else str(self.body)
        return f"\\mathbf{{for}}\\; 0 \\leq {self.loop_var} < {self.bound_var}\\; \\mathbf{{do}}\\; {body_tex}"

    def __eq__(self, other):
        return (isinstance(other, ForProg) and 
                self.loop_var == other.loop_var and 
                self.bound_var == other.bound_var and
                self.body == other.body)


# ============================================================================
# DYNAMIC LOGIC - MODAL FORMULAS
# ============================================================================

class Box(Formula):
    """Box modality: [α]P - after all executions of α, P holds"""
    def __init__(self, program, postcondition):
        self.program = program  # Program
        self.postcondition = postcondition  # Formula

    def __str__(self):
        return f"[{self.program}]{self.postcondition}"

    def to_latex(self):
        prog_tex = self.program.to_latex() if hasattr(self.program, 'to_latex') else str(self.program)
        return f"[{prog_tex}]{self.postcondition.to_latex()}"

    def __eq__(self, other):
        return isinstance(other, Box) and self.program == other.program and self.postcondition == other.postcondition


class Diamond(Formula):
    """Diamond modality: ⟨α⟩P - there exists an execution of α where P holds"""
    def __init__(self, program, postcondition):
        self.program = program
        self.postcondition = postcondition

    def __str__(self):
        return f"⟨{self.program}⟩{self.postcondition}"

    def to_latex(self):
        prog_tex = self.program.to_latex() if hasattr(self.program, 'to_latex') else str(self.program)
        return f"\\langle {prog_tex} \\rangle {self.postcondition.to_latex()}"

    def __eq__(self, other):
        return isinstance(other, Diamond) and self.program == other.program and self.postcondition == other.postcondition


# ============================================================================
# ARITHMETIC/EQUALITY FORMULAS (for dynamic logic)
# ============================================================================

class Equals(Formula):
    """Equality: e1 = e2"""
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} = {self.right})"

    def to_latex(self):
        l = self.left.to_latex() if hasattr(self.left, 'to_latex') else str(self.left)
        r = self.right.to_latex() if hasattr(self.right, 'to_latex') else str(self.right)
        return f"({l} = {r})"

    def __eq__(self, other):
        return isinstance(other, Equals) and self.left == other.left and self.right == other.right


class NotEquals(Formula):
    """Inequality: e1 ≠ e2"""
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} ≠ {self.right})"

    def to_latex(self):
        l = self.left.to_latex() if hasattr(self.left, 'to_latex') else str(self.left)
        r = self.right.to_latex() if hasattr(self.right, 'to_latex') else str(self.right)
        return f"({l} \\neq {r})"

    def __eq__(self, other):
        return isinstance(other, NotEquals) and self.left == other.left and self.right == other.right


class LessThan(Formula):
    """Less than: e1 < e2"""
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} < {self.right})"

    def to_latex(self):
        l = self.left.to_latex() if hasattr(self.left, 'to_latex') else str(self.left)
        r = self.right.to_latex() if hasattr(self.right, 'to_latex') else str(self.right)
        return f"({l} < {r})"


class LessEq(Formula):
    """Less than or equal: e1 ≤ e2"""
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} ≤ {self.right})"

    def to_latex(self):
        l = self.left.to_latex() if hasattr(self.left, 'to_latex') else str(self.left)
        r = self.right.to_latex() if hasattr(self.right, 'to_latex') else str(self.right)
        return f"({l} \\leq {r})"


class GreaterThan(Formula):
    """Greater than: e1 > e2"""
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} > {self.right})"

    def to_latex(self):
        l = self.left.to_latex() if hasattr(self.left, 'to_latex') else str(self.left)
        r = self.right.to_latex() if hasattr(self.right, 'to_latex') else str(self.right)
        return f"({l} > {r})"


class GreaterEq(Formula):
    """Greater than or equal: e1 ≥ e2"""
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} ≥ {self.right})"

    def to_latex(self):
        l = self.left.to_latex() if hasattr(self.left, 'to_latex') else str(self.left)
        r = self.right.to_latex() if hasattr(self.right, 'to_latex') else str(self.right)
        return f"({l} \\geq {r})"


class LogicParser:
    """
    Extended parser supporting:
    - Propositional logic: and, or, not, implies, iff
    - Quantifiers: forall x. P, exists x. P
    - Dynamic logic: [x := e]P, [a;b]P, [if P then a else b]P, [while P do a]P
    - Comparisons: =, !=, <, <=, >, >=
    """
    def __init__(self):
        self.tokens = []
        self.pos = 0
        self.fresh_var_counter = 0

    def get_fresh_var(self, base="x"):
        """Generate a fresh variable name."""
        self.fresh_var_counter += 1
        return f"{base}_{self.fresh_var_counter}"

    def tokenize(self, text):
        # Use placeholders for multi-char operators before single-char replacements
        text = text.replace(":=", " ASSIGN_OP ")
        text = text.replace("!=", " NOTEQ_OP ")
        text = text.replace("<=", " LESSEQ_OP ")
        text = text.replace(">=", " GREATEQ_OP ")
        text = text.replace("<->", " BICONDITIONAL_OP ")
        text = text.replace("->", " IMPLIES_OP ")
        
        # Handle brackets for box/diamond modality
        text = text.replace("[", " [ ").replace("]", " ] ")
        text = text.replace("⟨", " ⟨ ").replace("⟩", " ⟩ ")
        
        # Single-char operators (safe now that multi-char are placeholders)
        text = text.replace("<", " < ").replace(">", " > ")
        text = text.replace(".", " . ")
        text = text.replace("(", " ( ").replace(")", " ) ")
        text = text.replace(";", " ; ")
        text = text.replace("~", " ~ ")
        text = text.replace("?", " ? ")
        text = text.replace("*", " * ")
        text = text.replace("=", " = ")
        
        # Fix double spaces from replacements
        text = re.sub(r'\s+', ' ', text)
        
        # Restore multi-char operators from placeholders
        text = text.replace("ASSIGN_OP", ":=")
        text = text.replace("NOTEQ_OP", "!=")
        text = text.replace("LESSEQ_OP", "<=")
        text = text.replace("GREATEQ_OP", ">=")
        text = text.replace("BICONDITIONAL_OP", "<->")
        text = text.replace("IMPLIES_OP", "->")
        
        # Handle keywords (case-insensitive)
        text = re.sub(r"\biff\b", "<->", text, flags=re.IGNORECASE)
        text = re.sub(r"\bimplies\b", "->", text, flags=re.IGNORECASE)
        text = re.sub(r"\band\b", "&", text, flags=re.IGNORECASE)
        text = re.sub(r"\bor\b", "|", text, flags=re.IGNORECASE)
        text = re.sub(r"\bnot\b", "~", text, flags=re.IGNORECASE)
        
        # Handle truth constants
        text = re.sub(r"\btrue\b", "TOP", text, flags=re.IGNORECASE)
        text = re.sub(r"\bfalse\b", "BOT", text, flags=re.IGNORECASE)
        text = re.sub(r"\btop\b", "TOP", text, flags=re.IGNORECASE)
        text = re.sub(r"\bbot\b", "BOT", text, flags=re.IGNORECASE)
        text = re.sub(r"\bbottom\b", "BOT", text, flags=re.IGNORECASE)
        
        # Quantifier keywords
        text = re.sub(r"\bforall\b", "FORALL", text, flags=re.IGNORECASE)
        text = re.sub(r"\bexists\b", "EXISTS", text, flags=re.IGNORECASE)
        text = re.sub(r"∀", "FORALL", text)
        text = re.sub(r"∃", "EXISTS", text)
        
        # Program keywords
        text = re.sub(r"\bif\b", "IF", text, flags=re.IGNORECASE)
        text = re.sub(r"\bthen\b", "THEN", text, flags=re.IGNORECASE)
        text = re.sub(r"\belse\b", "ELSE", text, flags=re.IGNORECASE)
        text = re.sub(r"\bwhile\b", "WHILE", text, flags=re.IGNORECASE)
        text = re.sub(r"\bdo\b", "DO", text, flags=re.IGNORECASE)
        text = re.sub(r"\bassert\b", "ASSERT", text, flags=re.IGNORECASE)
        text = re.sub(r"\btest\b", "TEST", text, flags=re.IGNORECASE)
        text = re.sub(r"\bskip\b", "SKIP", text, flags=re.IGNORECASE)
        text = re.sub(r"\bfor\b", "FOR", text, flags=re.IGNORECASE)
        
        # Authorization logic keywords
        text = re.sub(r"\bsays\b", "SAYS", text)
        text = re.sub(r"\baff\b", "AFF", text)
        
        return text.split()

    def parse(self, text):
        self.tokens = self.tokenize(text)
        self.pos = 0
        if not self.tokens:
            return None
        return self.parse_iff()

    def peek(self, offset=0):
        """Look at a token without consuming it."""
        idx = self.pos + offset
        if idx < len(self.tokens):
            return self.tokens[idx]
        return None

    def parse_iff(self):
        left = self.parse_implies()
        if self.pos < len(self.tokens) and self.tokens[self.pos] == "<->":
            self.pos += 1
            right = self.parse_iff()
            return Iff(left, right)
        return left

    def parse_implies(self):
        left = self.parse_or()
        if self.pos < len(self.tokens) and self.tokens[self.pos] == "->":
            self.pos += 1
            right = self.parse_implies()
            return Implies(left, right)
        return left

    def parse_or(self):
        left = self.parse_and()
        while self.pos < len(self.tokens) and self.tokens[self.pos] == "|":
            self.pos += 1
            right = self.parse_and()
            left = Or(left, right)
        return left

    def parse_and(self):
        left = self.parse_comparison()
        while self.pos < len(self.tokens) and self.tokens[self.pos] == "&":
            self.pos += 1
            right = self.parse_comparison()
            left = And(left, right)
        return left

    def parse_comparison(self):
        """Parse comparison operators: =, !=, <, <=, >, >="""
        left = self.parse_not()
        if self.pos < len(self.tokens):
            op = self.tokens[self.pos]
            if op == "=" and self.peek(1) not in [None, ")", "]", ",", "&", "|", "->", "<->"]:
                # This might be an equality comparison
                self.pos += 1
                right = self.parse_not()
                return Equals(left, right)
            elif op == "!=":
                self.pos += 1
                right = self.parse_not()
                return NotEquals(left, right)
            elif op == "<" and self.peek(1) not in ["-"]:  # Not part of <->
                self.pos += 1
                right = self.parse_not()
                return LessThan(left, right)
            elif op == "<=":
                self.pos += 1
                right = self.parse_not()
                return LessEq(left, right)
            elif op == ">":
                self.pos += 1
                right = self.parse_not()
                return GreaterThan(left, right)
            elif op == ">=":
                self.pos += 1
                right = self.parse_not()
                return GreaterEq(left, right)
        return left

    def parse_not(self):
        if self.pos < len(self.tokens) and self.tokens[self.pos] == "~":
            self.pos += 1
            return Not(self.parse_not())
        return self.parse_quantifier()

    def parse_quantifier(self):
        """Parse universal and existential quantifiers."""
        if self.pos < len(self.tokens):
            token = self.tokens[self.pos]
            if token == "FORALL":
                self.pos += 1
                var = self.tokens[self.pos]
                self.pos += 1
                # Skip the dot if present
                if self.pos < len(self.tokens) and self.tokens[self.pos] == ".":
                    self.pos += 1
                inner = self.parse_iff()  # Parse the body
                return Forall(var, inner)
            elif token == "EXISTS":
                self.pos += 1
                var = self.tokens[self.pos]
                self.pos += 1
                # Skip the dot if present
                if self.pos < len(self.tokens) and self.tokens[self.pos] == ".":
                    self.pos += 1
                inner = self.parse_iff()
                return Exists(var, inner)
        return self.parse_modality()

    def parse_modality(self):
        """Parse box [α]P and diamond ⟨α⟩P modalities."""
        if self.pos < len(self.tokens) and self.tokens[self.pos] == "[":
            self.pos += 1  # consume [
            program = self.parse_program()
            if self.pos < len(self.tokens) and self.tokens[self.pos] == "]":
                self.pos += 1  # consume ]
            postcondition = self.parse_iff()  # The formula after ]
            return Box(program, postcondition)
        elif self.pos < len(self.tokens) and self.tokens[self.pos] == "⟨":
            self.pos += 1  # consume ⟨
            program = self.parse_program()
            if self.pos < len(self.tokens) and self.tokens[self.pos] == "⟩":
                self.pos += 1  # consume ⟩
            postcondition = self.parse_iff()
            return Diamond(program, postcondition)
        return self.parse_atom()

    def parse_program(self):
        """Parse program constructs for dynamic logic."""
        return self.parse_program_choice()

    def parse_program_choice(self):
        """Parse non-deterministic choice: α ∪ β"""
        left = self.parse_program_seq()
        while self.pos < len(self.tokens) and self.tokens[self.pos] in ["∪", "U", "++", "CHOICE"]:
            self.pos += 1
            right = self.parse_program_seq()
            left = Choice(left, right)
        return left

    def parse_program_seq(self):
        """Parse sequential composition: α; β"""
        left = self.parse_program_loop()
        if left is None:
            return None
        while self.pos < len(self.tokens) and self.tokens[self.pos] == ";":
            self.pos += 1
            right = self.parse_program_loop()
            if right is None:
                break
            left = Seq(left, right)
        return left

    def parse_program_loop(self):
        """Parse iteration: α*"""
        prog = self.parse_program_atom()
        if prog is None:
            return None
        if self.pos < len(self.tokens) and self.tokens[self.pos] == "*":
            self.pos += 1
            prog = Loop(prog)
        return prog

    def parse_program_atom(self):
        """Parse atomic programs: assignment, test, if, while."""
        if self.pos >= len(self.tokens):
            return None
        
        token = self.tokens[self.pos]
        
        # Stop at closing bracket - we've reached end of program
        if token == "]" or token == "⟩":
            return None
        
        # Test: ?P
        if token == "?" or token == "TEST":
            self.pos += 1
            # For test, parse a simple formula (not full iff to avoid consuming too much)
            formula = self.parse_simple_formula_for_program()
            return Test(formula)
        
        # Assert
        if token == "ASSERT":
            self.pos += 1
            formula = self.parse_simple_formula_for_program()
            return Test(formula)  # Assert is similar to test for our purposes
        
        # If-then-else
        if token == "IF":
            self.pos += 1
            guard = self.parse_simple_formula_for_program()
            if self.pos < len(self.tokens) and self.tokens[self.pos] == "THEN":
                self.pos += 1
            then_branch = self.parse_program_atom()
            if self.pos < len(self.tokens) and self.tokens[self.pos] == "ELSE":
                self.pos += 1
            else_branch = self.parse_program_atom()
            return IfProg(guard, then_branch, else_branch)
        
        # While loop (with optional invariant)
        # Syntax: "while P do α" or "while_{J} P do α" for invariant J
        if token == "WHILE":
            self.pos += 1
            invariant = None
            # Check for invariant annotation: while_{J} or while_J
            if self.pos < len(self.tokens) and self.tokens[self.pos].startswith("_"):
                inv_token = self.tokens[self.pos]
                # Extract invariant (remove leading underscore and any braces)
                inv_str = inv_token[1:].strip("{}")
                invariant = Atom(inv_str)
                self.pos += 1
            guard = self.parse_simple_formula_for_program()
            if self.pos < len(self.tokens) and self.tokens[self.pos] == "DO":
                self.pos += 1
            body = self.parse_program_atom()
            return WhileProg(guard, body, invariant)
        
        # For loop: for 0 ≤ i < n do α
        # Syntax variants: "for 0 <= i < n do α" or "for 0 ≤ i < n do α"
        if token == "FOR":
            self.pos += 1
            # Expect: 0 ≤ i < n do α
            # Skip the "0"
            if self.pos < len(self.tokens) and self.tokens[self.pos] == "0":
                self.pos += 1
            # Skip the "≤" or "<="
            if self.pos < len(self.tokens) and self.tokens[self.pos] in ["<=", "≤"]:
                self.pos += 1
            # Get loop variable
            loop_var = self.tokens[self.pos] if self.pos < len(self.tokens) else "i"
            self.pos += 1
            # Skip the "<"
            if self.pos < len(self.tokens) and self.tokens[self.pos] == "<":
                self.pos += 1
            # Get bound variable
            bound_var = self.tokens[self.pos] if self.pos < len(self.tokens) else "n"
            self.pos += 1
            # Skip "DO"
            if self.pos < len(self.tokens) and self.tokens[self.pos] == "DO":
                self.pos += 1
            # Parse body
            body = self.parse_program_atom()
            return ForProg(loop_var, bound_var, body)
        
        # Skip program
        if token == "SKIP":
            self.pos += 1
            return Skip()
        
        # Parenthesized program
        if token == "(":
            self.pos += 1
            prog = self.parse_program()
            if self.pos < len(self.tokens) and self.tokens[self.pos] == ")":
                self.pos += 1
            return prog
        
        # Assignment: x := e (look ahead for :=)
        if self.pos + 1 < len(self.tokens) and self.tokens[self.pos + 1] == ":=":
            var = token
            self.pos += 2  # consume var and :=
            # Parse a simple expression (stop at special tokens)
            if self.pos < len(self.tokens) and self.tokens[self.pos] not in ["]", "⟩", ";", "*"]:
                expr_token = self.tokens[self.pos]
                self.pos += 1
                expr = Atom(expr_token)
            else:
                expr = Atom("")
            return Assign(var, expr)
        
        # Default: treat as a simple variable/action
        self.pos += 1
        return Assign(token, Atom(token))  # Fallback

    def parse_simple_formula_for_program(self):
        """Parse a simple formula inside a program (stops at program keywords)."""
        if self.pos >= len(self.tokens):
            return Atom("")
        token = self.tokens[self.pos]
        # Stop tokens for program context
        if token in ["]", "⟩", ";", "THEN", "ELSE", "DO", "*"]:
            return Atom("")
        self.pos += 1
        return Atom(token)

    def parse_atom(self):
        if self.pos >= len(self.tokens):
            return Atom("")
        token = self.tokens[self.pos]
        self.pos += 1
        if token == "(":
            expr = self.parse_iff()
            if self.pos < len(self.tokens) and self.tokens[self.pos] == ")":
                self.pos += 1
            return expr
        elif token == "TOP":
            return Top()
        elif token == "BOT":
            return Bottom()
        elif token == "[":
            # Handle box modality at atom level
            self.pos -= 1  # Put back the [
            return self.parse_modality()
        # Check if this is "principal says P" or "principal aff P"
        if self.pos < len(self.tokens) and self.tokens[self.pos] == "SAYS":
            self.pos += 1
            inner = self.parse_iff()
            return Says(token, inner)
        elif self.pos < len(self.tokens) and self.tokens[self.pos] == "AFF":
            self.pos += 1
            inner = self.parse_iff()
            return Aff(token, inner)
        return Atom(token)


class Sequent:
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def __str__(self):
        l = ", ".join(str(f) for f in self.lhs)
        r = ", ".join(str(f) for f in self.rhs)
        return f"{l} ⊢ {r}"

    def to_latex(self):
        # Filter out dots (which mean nothing and shouldn't appear)
        lhs_filtered = [f for f in self.lhs if not (isinstance(f, Atom) and f.name == ".")]
        rhs_filtered = [f for f in self.rhs if not (isinstance(f, Atom) and f.name == ".")]
        
        l = ", ".join(f.to_latex() for f in lhs_filtered)
        r = ", ".join(f.to_latex() for f in rhs_filtered)
        return f"{l if l else '\\cdot'} \\vdash {r if r else '\\cdot'}"


class ProofNode:
    def __init__(self, sequent, parent=None):
        self.sequent = sequent
        self.parent = parent
        self.children = []
        self.rule_applied = None
        self.is_closed = False

    def add_child(self, sequent):
        child = ProofNode(sequent, self)
        self.children.append(child)
        return child

class SequentProverApp:
    CUSTOM_RULES_FILE = "custom_rules.json"
    
    def __init__(self, root):
        self.root = root
        self.root.title("Sequent Calculus Assistant")
        self.root.geometry("1100x850")

        # --- 1. Theming & Styles ---
        self.style = ttk.Style()
        self.style.theme_use("clam")

        # Define fonts
        self.main_font = ("Segoe UI", 11)
        self.mono_font = ("Consolas", 11)
        self.header_font = ("Segoe UI", 12, "bold")
        self.symbol_font = ("Segoe UI", 14)

        # Configure Widget Styles
        self.style.configure("TButton", font=self.main_font, padding=5)
        self.style.configure("TLabel", font=self.main_font)
        self.style.configure("Treeview", font=self.main_font, rowheight=25)
        self.style.configure("Treeview.Heading", font=self.header_font)

        # Logic State
        self.parser = LogicParser()
        self.root_node = None
        self.selected_node_id = None
        self.selected_formula_index = None
        self.selected_side = None
        self.node_map = {}
        self.current_proof_node = None
        self.current_tree_id = None
        
        # Custom rules storage
        self.custom_rules = self._load_custom_rules()
        
        # Trust context for authorization logic (A ≤ B pairs)
        self.trust_facts = []  # list of (A_name, B_name) strings

        self._setup_ui()

    def _load_custom_rules(self):
        """Load custom rules from JSON file."""
        if os.path.exists(self.CUSTOM_RULES_FILE):
            try:
                with open(self.CUSTOM_RULES_FILE, 'r', encoding='utf-8') as f:
                    return json.load(f)
            except (json.JSONDecodeError, IOError):
                return []
        return []

    def _save_custom_rules(self):
        """Save custom rules to JSON file."""
        with open(self.CUSTOM_RULES_FILE, 'w', encoding='utf-8') as f:
            json.dump(self.custom_rules, f, indent=2, ensure_ascii=False)

    def _setup_ui(self):
        main_container = ttk.Frame(self.root, padding="15")
        main_container.pack(fill=tk.BOTH, expand=True)

        # --- SECTION: Header & Input ---
        header_frame = ttk.Frame(main_container)
        header_frame.pack(fill=tk.X, pady=(0, 15))

        lbl_instr = ttk.Label(
            header_frame, text="Enter Sequent:", font=self.header_font
        )
        lbl_instr.pack(side=tk.LEFT)

        self.input_var = tk.StringVar(value="p implies q, p |- q")
        entry = ttk.Entry(
            header_frame, textvariable=self.input_var, font=self.mono_font
        )
        entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=10)
        entry.bind("<Return>", lambda e: self.start_proof())

        btn_start = ttk.Button(
            header_frame, text="▶ Start Proof", command=self.start_proof
        )
        btn_start.pack(side=tk.LEFT, padx=5)

        btn_export = ttk.Button(
            header_frame, text="⬇ Export LaTeX", command=self.export_latex
        )
        btn_export.pack(side=tk.RIGHT)

        # --- SECTION: Split Pane (Tree vs Workspace) ---
        self.paned = ttk.PanedWindow(main_container, orient=tk.HORIZONTAL)
        self.paned.pack(fill=tk.BOTH, expand=True)

        # -- LEFT PANE: Proof Tree --
        tree_frame = ttk.LabelFrame(self.paned, text=" 🌳 Proof Tree ", padding=10)
        self.paned.add(tree_frame, weight=1)

        tree_scroll = ttk.Scrollbar(tree_frame)
        tree_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        self.tree = ttk.Treeview(
            tree_frame, selectmode="browse", yscrollcommand=tree_scroll.set
        )
        self.tree.pack(fill=tk.BOTH, expand=True)
        tree_scroll.config(command=self.tree.yview)

        self.tree.heading("#0", text="Sequent Structure", anchor=tk.W)
        self.tree.bind("<<TreeviewSelect>>", self.on_tree_select)

        # -- RIGHT PANE: Workspace & Controls --
        work_frame = ttk.Frame(self.paned)
        self.paned.add(work_frame, weight=2)

        # 1. Formula Lists
        lists_container = ttk.LabelFrame(
            work_frame, text=" 📝 Current Sequent Selection ", padding=10
        )
        lists_container.pack(fill=tk.BOTH, expand=True, padx=(10, 0))

        lists_container.columnconfigure(0, weight=1)
        lists_container.columnconfigure(2, weight=1)
        lists_container.rowconfigure(1, weight=1)

        # LHS
        ttk.Label(
            lists_container, text="Antecedent (LHS)", font=("Segoe UI", 10, "italic")
        ).grid(row=0, column=0, sticky="w")
        lhs_scroll = ttk.Scrollbar(lists_container)
        self.lhs_listbox = tk.Listbox(
            lists_container,
            font=self.main_font,
            borderwidth=0,
            highlightthickness=1,
            selectbackground="#cce8ff",
            selectforeground="black",
            yscrollcommand=lhs_scroll.set,
        )
        self.lhs_listbox.grid(row=1, column=0, sticky="nsew")
        lhs_scroll.grid(row=1, column=0, sticky="nse", padx=(0, 1))
        lhs_scroll.config(command=self.lhs_listbox.yview)
        self.lhs_listbox.bind(
            "<<ListboxSelect>>", lambda e: self.on_formula_select("lhs")
        )

        # Turnstile
        ttk.Label(lists_container, text="⊢", font=("Times New Roman", 24)).grid(
            row=1, column=1, padx=10
        )

        # RHS
        ttk.Label(
            lists_container, text="Succedent (RHS)", font=("Segoe UI", 10, "italic")
        ).grid(row=0, column=2, sticky="w")
        rhs_scroll = ttk.Scrollbar(lists_container)
        self.rhs_listbox = tk.Listbox(
            lists_container,
            font=self.main_font,
            borderwidth=0,
            highlightthickness=1,
            selectbackground="#cce8ff",
            selectforeground="black",
            yscrollcommand=rhs_scroll.set,
        )
        self.rhs_listbox.grid(row=1, column=2, sticky="nsew")
        rhs_scroll.grid(row=1, column=2, sticky="nse", padx=(0, 1))
        rhs_scroll.config(command=self.rhs_listbox.yview)
        self.rhs_listbox.bind(
            "<<ListboxSelect>>", lambda e: self.on_formula_select("rhs")
        )

        # 2. Rule Controls with Tabbed Interface
        controls_frame = ttk.LabelFrame(
            work_frame, text=" 🛠 Rule Application ", padding=5
        )
        controls_frame.pack(fill=tk.BOTH, expand=True, padx=(10, 0), pady=(10, 0))

        # Create Notebook (Tabbed Interface) for organizing rules
        rule_notebook = ttk.Notebook(controls_frame)
        rule_notebook.pack(fill=tk.BOTH, expand=True)

        # =====================================================================
        # TAB 1: Propositional Logic Rules
        # =====================================================================
        prop_frame = ttk.Frame(rule_notebook, padding=10)
        rule_notebook.add(prop_frame, text="📐 Propositional")

        # Grid Headers for propositional rules
        ttk.Label(prop_frame, text="Connective", font=("Segoe UI", 9, "bold"), foreground="#666").grid(row=0, column=0, pady=5)
        ttk.Label(prop_frame, text="Left Rule (Antecedent)", font=("Segoe UI", 9, "bold"), foreground="#666").grid(row=0, column=1, pady=5)
        ttk.Label(prop_frame, text="Right Rule (Succedent)", font=("Segoe UI", 9, "bold"), foreground="#666").grid(row=0, column=2, pady=5)

        def create_rule_row(parent, row, symbol, name, cmd_l, cmd_r):
            ttk.Label(parent, text=f"{symbol} ({name})", font=self.symbol_font).grid(row=row, column=0, padx=10, pady=2)
            ttk.Button(parent, text=f"{symbol}L", command=cmd_l, width=10).grid(row=row, column=1, sticky="ew", padx=5, pady=2)
            ttk.Button(parent, text=f"{symbol}R", command=cmd_r, width=10).grid(row=row, column=2, sticky="ew", padx=5, pady=2)

        create_rule_row(prop_frame, 1, "∧", "And", self.rule_and_l, self.rule_and_r)
        create_rule_row(prop_frame, 2, "∨", "Or", self.rule_or_l, self.rule_or_r)
        create_rule_row(prop_frame, 3, "→", "Implies", self.rule_imp_l, self.rule_imp_r)
        create_rule_row(prop_frame, 4, "¬", "Not", self.rule_not_l, self.rule_not_r)
        create_rule_row(prop_frame, 5, "↔", "Iff", self.rule_iff_l, self.rule_iff_r)

        # Constants section
        ttk.Separator(prop_frame, orient="horizontal").grid(row=6, column=0, columnspan=3, sticky="ew", pady=5)
        ttk.Label(prop_frame, text="Constants", font=("Segoe UI", 9, "bold"), foreground="#666").grid(row=7, column=0, pady=2)
        
        # Bottom (⊥) buttons
        bot_frame = ttk.Frame(prop_frame)
        bot_frame.grid(row=7, column=1, sticky="ew", padx=5, pady=2)
        ttk.Button(bot_frame, text="⊥L", command=self.rule_bot_l, width=5).pack(side=tk.LEFT, padx=1)
        ttk.Button(bot_frame, text="⊥R", command=self.rule_bot_r, width=5).pack(side=tk.LEFT, padx=1)
        
        # Top (⊤) buttons
        top_frame = ttk.Frame(prop_frame)
        top_frame.grid(row=7, column=2, sticky="ew", padx=5, pady=2)
        ttk.Button(top_frame, text="⊤L", command=self.rule_top_l, width=5).pack(side=tk.LEFT, padx=1)
        ttk.Button(top_frame, text="⊤R", command=self.rule_top_r, width=5).pack(side=tk.LEFT, padx=1)

        prop_frame.columnconfigure(1, weight=1)
        prop_frame.columnconfigure(2, weight=1)

        # =====================================================================
        # TAB 2: Quantifier Rules
        # =====================================================================
        quant_frame = ttk.Frame(rule_notebook, padding=10)
        rule_notebook.add(quant_frame, text="∀∃ Quantifiers")

        ttk.Label(quant_frame, text="Quantifier", font=("Segoe UI", 9, "bold"), foreground="#666").grid(row=0, column=0, pady=5)
        ttk.Label(quant_frame, text="Left Rule", font=("Segoe UI", 9, "bold"), foreground="#666").grid(row=0, column=1, pady=5)
        ttk.Label(quant_frame, text="Right Rule", font=("Segoe UI", 9, "bold"), foreground="#666").grid(row=0, column=2, pady=5)

        create_rule_row(quant_frame, 1, "∀", "Forall", self.rule_forall_l, self.rule_forall_r)
        create_rule_row(quant_frame, 2, "∃", "Exists", self.rule_exists_l, self.rule_exists_r)

        # Help text for quantifier rules
        ttk.Label(quant_frame, text="∀R/∃L: Uses fresh variable", font=("Segoe UI", 9, "italic"), foreground="#666").grid(row=3, column=0, columnspan=3, pady=10, sticky="w")
        ttk.Label(quant_frame, text="∀L/∃R: Prompts for instantiation term", font=("Segoe UI", 9, "italic"), foreground="#666").grid(row=4, column=0, columnspan=3, sticky="w")

        quant_frame.columnconfigure(1, weight=1)
        quant_frame.columnconfigure(2, weight=1)

        # =====================================================================
        # TAB 3: Dynamic Logic Rules (Box Modality)
        # =====================================================================
        dyn_frame = ttk.Frame(rule_notebook, padding=10)
        rule_notebook.add(dyn_frame, text="[α] Dynamic Logic")

        ttk.Label(dyn_frame, text="Program Construct", font=("Segoe UI", 9, "bold"), foreground="#666").grid(row=0, column=0, pady=5)
        ttk.Label(dyn_frame, text="Rule", font=("Segoe UI", 9, "bold"), foreground="#666").grid(row=0, column=1, pady=5)
        ttk.Label(dyn_frame, text="Description", font=("Segoe UI", 9, "bold"), foreground="#666").grid(row=0, column=2, pady=5, sticky="w")

        # Assignment Rule
        ttk.Label(dyn_frame, text="[:=] Assign", font=self.symbol_font).grid(row=1, column=0, padx=5, pady=2)
        ttk.Button(dyn_frame, text="[:=]R", command=self.rule_assign_r, width=12).grid(row=1, column=1, padx=5, pady=2)
        ttk.Label(dyn_frame, text="[x := e]Q → x' = e ⊢ Q[x'/x]", font=("Consolas", 9)).grid(row=1, column=2, sticky="w", padx=5)

        # Test Rule
        ttk.Label(dyn_frame, text="[?] Test", font=self.symbol_font).grid(row=2, column=0, padx=5, pady=2)
        test_btn_frame = ttk.Frame(dyn_frame)
        test_btn_frame.grid(row=2, column=1, padx=5, pady=2)
        ttk.Button(test_btn_frame, text="[?]L", command=self.rule_test_l, width=5).pack(side=tk.LEFT, padx=1)
        ttk.Button(test_btn_frame, text="[?]R", command=self.rule_test_r, width=5).pack(side=tk.LEFT, padx=1)
        ttk.Label(dyn_frame, text="[?P]Q ↔ (P → Q)", font=("Consolas", 9)).grid(row=2, column=2, sticky="w", padx=5)

        # Sequence Rule
        ttk.Label(dyn_frame, text="[;] Sequence", font=self.symbol_font).grid(row=3, column=0, padx=5, pady=2)
        seq_btn_frame = ttk.Frame(dyn_frame)
        seq_btn_frame.grid(row=3, column=1, padx=5, pady=2)
        ttk.Button(seq_btn_frame, text="[;]L", command=self.rule_seq_l, width=5).pack(side=tk.LEFT, padx=1)
        ttk.Button(seq_btn_frame, text="[;]R", command=self.rule_seq_r, width=5).pack(side=tk.LEFT, padx=1)
        ttk.Label(dyn_frame, text="[α;β]Q → [α][β]Q", font=("Consolas", 9)).grid(row=3, column=2, sticky="w", padx=5)

        # Skip Rule
        ttk.Label(dyn_frame, text="[skip] Skip", font=self.symbol_font).grid(row=4, column=0, padx=5, pady=2)
        skip_btn_frame = ttk.Frame(dyn_frame)
        skip_btn_frame.grid(row=4, column=1, padx=5, pady=2)
        ttk.Button(skip_btn_frame, text="[skip]L", command=self.rule_skip_l, width=5).pack(side=tk.LEFT, padx=1)
        ttk.Button(skip_btn_frame, text="[skip]R", command=self.rule_skip_r, width=5).pack(side=tk.LEFT, padx=1)
        ttk.Label(dyn_frame, text="[skip]Q → Q", font=("Consolas", 9)).grid(row=4, column=2, sticky="w", padx=5)

        # Choice Rule
        ttk.Label(dyn_frame, text="[∪] Choice", font=self.symbol_font).grid(row=5, column=0, padx=5, pady=2)
        ttk.Button(dyn_frame, text="[∪]R", command=self.rule_choice_r, width=12).grid(row=5, column=1, padx=5, pady=2)
        ttk.Label(dyn_frame, text="[α∪β]Q → [α]Q ∧ [β]Q", font=("Consolas", 9)).grid(row=5, column=2, sticky="w", padx=5)

        # Loop Rule
        ttk.Label(dyn_frame, text="[*] Loop", font=self.symbol_font).grid(row=6, column=0, padx=5, pady=2)
        ttk.Button(dyn_frame, text="[*]unfold", command=self.rule_loop_unfold_r, width=12).grid(row=6, column=1, padx=5, pady=2)
        ttk.Label(dyn_frame, text="Unfold loop once", font=("Consolas", 9)).grid(row=6, column=2, sticky="w", padx=5)

        # Conditional Rule
        ttk.Label(dyn_frame, text="[if] Conditional", font=self.symbol_font).grid(row=7, column=0, padx=5, pady=2)
        ttk.Button(dyn_frame, text="[if]R", command=self.rule_if_r, width=12).grid(row=7, column=1, padx=5, pady=2)
        ttk.Label(dyn_frame, text="Split on guard P", font=("Consolas", 9)).grid(row=7, column=2, sticky="w", padx=5)

        # While Rules
        ttk.Label(dyn_frame, text="[while] Loop", font=self.symbol_font).grid(row=8, column=0, padx=5, pady=2)
        while_btn_frame = ttk.Frame(dyn_frame)
        while_btn_frame.grid(row=8, column=1, padx=5, pady=2)
        ttk.Button(while_btn_frame, text="unfold", command=self.rule_while_unfold_r, width=6).pack(side=tk.LEFT, padx=1)
        ttk.Button(while_btn_frame, text="inv", command=self.rule_while_inv_r, width=5).pack(side=tk.LEFT, padx=1)
        ttk.Label(dyn_frame, text="unfold or use invariant", font=("Consolas", 9)).grid(row=8, column=2, sticky="w", padx=5)

        # For Loop Rule
        ttk.Label(dyn_frame, text="[for] Bounded Loop", font=self.symbol_font).grid(row=9, column=0, padx=5, pady=2)
        ttk.Button(dyn_frame, text="[for]R", command=self.rule_for_r, width=12).grid(row=9, column=1, padx=5, pady=2)
        ttk.Label(dyn_frame, text="Desugar to while loop", font=("Consolas", 9)).grid(row=9, column=2, sticky="w", padx=5)

        dyn_frame.columnconfigure(2, weight=1)

        # =====================================================================
        # TAB 4: Structural Rules
        # =====================================================================
        struct_frame = ttk.Frame(rule_notebook, padding=10)
        rule_notebook.add(struct_frame, text="⚙ Structural")

        ttk.Label(struct_frame, text="Structural rules modify sequent structure", font=("Segoe UI", 10, "italic"), foreground="#666").grid(row=0, column=0, columnspan=2, pady=10, sticky="w")

        # Weakening
        ttk.Label(struct_frame, text="Weakening", font=("Segoe UI", 10, "bold")).grid(row=1, column=0, sticky="w", padx=5, pady=5)
        weak_frame = ttk.Frame(struct_frame)
        weak_frame.grid(row=1, column=1, sticky="w", padx=5, pady=5)
        ttk.Button(weak_frame, text="WL (Add to LHS)", command=self.rule_weaken_l, width=15).pack(side=tk.LEFT, padx=2)
        ttk.Button(weak_frame, text="WR (Add to RHS)", command=self.rule_weaken_r, width=15).pack(side=tk.LEFT, padx=2)

        # Contraction
        ttk.Label(struct_frame, text="Contraction", font=("Segoe UI", 10, "bold")).grid(row=2, column=0, sticky="w", padx=5, pady=5)
        contr_frame = ttk.Frame(struct_frame)
        contr_frame.grid(row=2, column=1, sticky="w", padx=5, pady=5)
        ttk.Button(contr_frame, text="CL (Contract LHS)", command=self.rule_contract_l, width=15).pack(side=tk.LEFT, padx=2)
        ttk.Button(contr_frame, text="CR (Contract RHS)", command=self.rule_contract_r, width=15).pack(side=tk.LEFT, padx=2)

        # Cut
        ttk.Label(struct_frame, text="Cut", font=("Segoe UI", 10, "bold")).grid(row=3, column=0, sticky="w", padx=5, pady=5)
        ttk.Button(struct_frame, text="Cut (Introduce formula)", command=self.rule_cut, width=20).grid(row=3, column=1, sticky="w", padx=5, pady=5)

        # Help text
        ttk.Separator(struct_frame, orient="horizontal").grid(row=4, column=0, columnspan=2, sticky="ew", pady=10)
        help_text = """• Weakening: Adds extra (unused) formula to the sequent
• Contraction: Removes duplicate formula (must appear 2+ times)
• Cut: Introduces a lemma to split the proof into two branches"""
        ttk.Label(struct_frame, text=help_text, font=("Segoe UI", 9), foreground="#555", justify=tk.LEFT).grid(row=5, column=0, columnspan=2, sticky="w", padx=5)

        struct_frame.columnconfigure(1, weight=1)

        # =====================================================================
        # TAB 5: Authorization Logic Rules (Lectures 15-17)
        # =====================================================================
        auth_outer = ttk.Frame(rule_notebook, padding=0)
        rule_notebook.add(auth_outer, text="🔐 Auth Logic")

        # Scrollable canvas for the auth tab
        auth_canvas = tk.Canvas(auth_outer, highlightthickness=0)
        auth_scrollbar = ttk.Scrollbar(auth_outer, orient="vertical", command=auth_canvas.yview)
        auth_frame = ttk.Frame(auth_canvas, padding=10)

        auth_frame.bind("<Configure>", lambda e: auth_canvas.configure(scrollregion=auth_canvas.bbox("all")))
        canvas_window = auth_canvas.create_window((0, 0), window=auth_frame, anchor="nw")
        auth_canvas.configure(yscrollcommand=auth_scrollbar.set)

        # Make the inner frame stretch to fill the canvas width
        def _on_canvas_configure(event):
            auth_canvas.itemconfig(canvas_window, width=event.width)
        auth_canvas.bind("<Configure>", _on_canvas_configure)

        auth_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        auth_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # Enable mousewheel scrolling when hovering over the auth tab
        def _on_auth_mousewheel(event):
            auth_canvas.yview_scroll(int(-1*(event.delta/120)), "units")
        auth_canvas.bind_all("<MouseWheel>", _on_auth_mousewheel, add="+")

        # --- Row counter for compact layout ---
        r = 0

        ttk.Label(auth_frame, text="Lectures 15-17 — Authorization Logic Rules",
                  font=("Segoe UI", 10, "bold")).grid(
            row=r, column=0, columnspan=3, pady=(0, 5), sticky="w")
        r += 1

        # Column headers
        ttk.Label(auth_frame, text="Rule", font=("Segoe UI", 9, "bold"), foreground="#666").grid(row=r, column=0, pady=2)
        ttk.Label(auth_frame, text="Left / Action", font=("Segoe UI", 9, "bold"), foreground="#666").grid(row=r, column=1, pady=2)
        ttk.Label(auth_frame, text="Right / Action", font=("Segoe UI", 9, "bold"), foreground="#666").grid(row=r, column=2, pady=2)
        r += 1

        # ── Lecture 15: Affirmation ──
        ttk.Separator(auth_frame, orient="horizontal").grid(row=r, column=0, columnspan=3, sticky="ew", pady=3); r += 1
        ttk.Label(auth_frame, text="Lecture 15 — Affirmation", font=("Segoe UI", 9, "bold"), foreground="#333").grid(
            row=r, column=0, columnspan=3, sticky="w", padx=5); r += 1

        ttk.Label(auth_frame, text="says", font=self.symbol_font).grid(row=r, column=0, padx=10, pady=1)
        ttk.Button(auth_frame, text="saysL", command=self.rule_says_l, width=10).grid(row=r, column=1, sticky="ew", padx=5, pady=1)
        ttk.Button(auth_frame, text="saysR", command=self.rule_says_r, width=10).grid(row=r, column=2, sticky="ew", padx=5, pady=1)
        r += 1

        ttk.Label(auth_frame, text="aff", font=self.symbol_font).grid(row=r, column=0, padx=10, pady=1)
        ttk.Button(auth_frame, text="aff", command=self.rule_aff, width=10).grid(row=r, column=1, sticky="ew", padx=5, pady=1)
        r += 1

        # ── Lecture 15: Intuitionistic ∨ ──
        ttk.Separator(auth_frame, orient="horizontal").grid(row=r, column=0, columnspan=3, sticky="ew", pady=3); r += 1
        ttk.Label(auth_frame, text="Lecture 15 — Intuitionistic ∨", font=("Segoe UI", 9, "bold"), foreground="#333").grid(
            row=r, column=0, columnspan=3, sticky="w", padx=5); r += 1

        ttk.Label(auth_frame, text="∨ choice", font=self.symbol_font).grid(row=r, column=0, padx=10, pady=1)
        or_btn = ttk.Frame(auth_frame)
        or_btn.grid(row=r, column=1, columnspan=2, sticky="ew", padx=5, pady=1)
        ttk.Button(or_btn, text="∨R₁ (pick left)", command=self.rule_or_r1, width=14).pack(side=tk.LEFT, padx=2)
        ttk.Button(or_btn, text="∨R₂ (pick right)", command=self.rule_or_r2, width=14).pack(side=tk.LEFT, padx=2)
        r += 1

        # ── Trust Preorder ──
        ttk.Separator(auth_frame, orient="horizontal").grid(row=r, column=0, columnspan=3, sticky="ew", pady=3); r += 1
        ttk.Label(auth_frame, text="Trust Preorder (A ≤ B)", font=("Segoe UI", 9, "bold"), foreground="#333").grid(
            row=r, column=0, columnspan=3, sticky="w", padx=5); r += 1

        ttk.Label(auth_frame, text="≤", font=self.symbol_font).grid(row=r, column=0, padx=10, pady=1)
        ttk.Button(auth_frame, text="≤-says", command=self.rule_trust_says, width=10).grid(row=r, column=1, sticky="ew", padx=5, pady=1)
        ttk.Button(auth_frame, text="Set trust...", command=self.rule_trust_add, width=10).grid(row=r, column=2, sticky="ew", padx=5, pady=1)
        r += 1

        # ── Lecture 16: Cut variant ──
        ttk.Separator(auth_frame, orient="horizontal").grid(row=r, column=0, columnspan=3, sticky="ew", pady=3); r += 1
        ttk.Label(auth_frame, text="Lecture 16 — Proof Search", font=("Segoe UI", 9, "bold"), foreground="#333").grid(
            row=r, column=0, columnspan=3, sticky="w", padx=5); r += 1

        ttk.Label(auth_frame, text="cut'", font=self.symbol_font).grid(row=r, column=0, padx=10, pady=1)
        ttk.Button(auth_frame, text="cut' (split Γ)", command=self.rule_cut_prime, width=15).grid(row=r, column=1, columnspan=2, sticky="ew", padx=5, pady=1)
        r += 1

        # ── Help / Reference ──
        ttk.Separator(auth_frame, orient="horizontal").grid(row=r, column=0, columnspan=3, sticky="ew", pady=3); r += 1
        ttk.Label(auth_frame, text="Quick Reference", font=("Segoe UI", 9, "bold"), foreground="#333").grid(
            row=r, column=0, columnspan=3, sticky="w", padx=5); r += 1

        help_lines = [
            ("Syntax:", "A says P  |  A aff P"),
            ("saysR:", "Γ ⊢ A says P  →  Γ ⊢ A aff P"),
            ("saysL:", "Γ, A says P ⊢ A aff Q  →  Γ, P ⊢ A aff Q"),
            ("aff:", "Γ ⊢ A aff P  →  Γ ⊢ P"),
            ("∨R₁:", "Γ ⊢ P ∨ Q  →  Γ ⊢ P  (pick left)"),
            ("∨R₂:", "Γ ⊢ P ∨ Q  →  Γ ⊢ Q  (pick right)"),
            ("≤-says:", "B says P → A says P  (when A ≤ B)"),
            ("cut':", "Γ₁,Γ₂ ⊢ δ  from  Γ₁ ⊢ P  and  Γ₂,P ⊢ δ"),
        ]
        for label, desc in help_lines:
            ttk.Label(auth_frame, text=label, font=("Consolas", 8, "bold"), foreground="#444").grid(
                row=r, column=0, sticky="e", padx=(5, 2), pady=0)
            ttk.Label(auth_frame, text=desc, font=("Consolas", 8), foreground="#555").grid(
                row=r, column=1, columnspan=2, sticky="w", padx=2, pady=0)
            r += 1

        ttk.Label(auth_frame, text="Example: admin says (p -> q), admin says p |- admin says q",
                  font=("Consolas", 8, "italic"), foreground="#888").grid(
            row=r, column=0, columnspan=3, sticky="w", padx=5, pady=(5, 0))
        r += 1

        auth_frame.columnconfigure(1, weight=1)
        auth_frame.columnconfigure(2, weight=1)

        # =====================================================================
        # TAB 6: Custom Rules
        # =====================================================================
        custom_tab_frame = ttk.Frame(rule_notebook, padding=10)
        rule_notebook.add(custom_tab_frame, text="✨ Custom")
        
        custom_header = ttk.Frame(custom_tab_frame)
        custom_header.pack(fill=tk.X, pady=(0, 10))
        
        ttk.Label(custom_header, text="User-defined rules (saved to custom_rules.json)", font=("Segoe UI", 10, "italic"), foreground="#666").pack(side=tk.LEFT)
        ttk.Button(custom_header, text="+ Add Rule", command=self.open_custom_rule_dialog).pack(side=tk.RIGHT, padx=5)
        
        # Frame to hold custom rule buttons
        self.custom_rules_frame = ttk.Frame(custom_tab_frame)
        self.custom_rules_frame.pack(fill=tk.BOTH, expand=True)
        
        # Load and display any existing custom rules
        self._refresh_custom_rules_ui()

        # =====================================================================
        # Action Buttons (Always visible below tabs)
        # =====================================================================
        action_frame = ttk.Frame(controls_frame)
        action_frame.pack(fill=tk.X, pady=(10, 5))

        ttk.Button(action_frame, text="✔ Identity (Axiom)", command=self.rule_id).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=2)
        ttk.Button(action_frame, text="↶ Undo Step", command=self.undo_step).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=2)

        # Status Bar
        self.status_var = tk.StringVar(value="Ready. Enter a sequent to begin.")
        status_bar = ttk.Label(
            self.root,
            textvariable=self.status_var,
            relief=tk.SUNKEN,
            anchor=tk.W,
            font=("Segoe UI", 9),
        )
        status_bar.pack(side=tk.BOTTOM, fill=tk.X)

    def parse_sequent_input(self, text):
        if "|-" in text:
            parts = text.split("|-")
        elif "entails" in text:
            parts = text.split("entails")
        else:
            parts = ["", text]

        # Strip dots and other trailing punctuation from parts
        parts = [p.rstrip('.,;:') for p in parts]

        lhs_strs = [s.strip() for s in parts[0].split(",")] if parts[0].strip() else []
        rhs_strs = (
            [s.strip() for s in parts[1].split(",")]
            if len(parts) > 1 and parts[1].strip()
            else []
        )
        lhs_forms = [self.parser.parse(s) for s in lhs_strs if s]
        rhs_forms = [self.parser.parse(s) for s in rhs_strs if s]
        return Sequent(lhs_forms, rhs_forms)

    def start_proof(self):
        try:
            raw = self.input_var.get()
            sequent = self.parse_sequent_input(raw)
            self.root_node = ProofNode(sequent)

            self.tree.delete(*self.tree.get_children())
            self.node_map = {}
            self.lhs_listbox.delete(0, tk.END)
            self.rhs_listbox.delete(0, tk.END)

            tree_id = self.tree.insert("", "end", text=str(sequent), open=True)
            self.node_map[tree_id] = self.root_node

            self.tree.selection_set(tree_id)
            self.status_var.set("Proof started. Select a formula to apply a rule.")

        except Exception as e:
            messagebox.showerror("Error", f"Failed to parse: {e}")

    def update_tree_display(self, parent_node, parent_id):
        for child in self.tree.get_children(parent_id):
            self.tree.delete(child)

        for child_node in parent_node.children:
            txt = str(child_node.sequent)
            if child_node.is_closed:
                txt = "✔ " + txt
            cid = self.tree.insert(parent_id, "end", text=txt, open=True)
            self.node_map[cid] = child_node
            self.update_tree_display(child_node, cid)

    def on_tree_select(self, event):
        sel = self.tree.selection()
        if not sel:
            return
        node = self.node_map.get(sel[0])
        if node:
            self.current_proof_node = node
            self.current_tree_id = sel[0]
            self.refresh_listboxes(node.sequent)
            self.selected_formula_index = None
            self.selected_side = None

            status = "Closed Branch." if node.is_closed else "Active Branch."
            self.status_var.set(f"{status} Select a formula from the lists below.")

    def refresh_listboxes(self, sequent):
        self.lhs_listbox.delete(0, tk.END)
        self.rhs_listbox.delete(0, tk.END)
        for f in sequent.lhs:
            self.lhs_listbox.insert(tk.END, "  " + str(f))
        for f in sequent.rhs:
            self.rhs_listbox.insert(tk.END, "  " + str(f))

    def on_formula_select(self, side):
        if side == "lhs":
            self.rhs_listbox.selection_clear(0, tk.END)
            sel = self.lhs_listbox.curselection()
        else:
            self.lhs_listbox.selection_clear(0, tk.END)
            sel = self.rhs_listbox.curselection()

        if sel:
            self.selected_side = side
            self.selected_formula_index = sel[0]
            self.status_var.set(
                f"Selected formula index {sel[0]} on {side.upper()}. Click a rule button."
            )

    def get_target(self):
        if self.selected_formula_index is None:
            messagebox.showwarning(
                "Selection", "Please select a formula from the lists first."
            )
            return None, None, None

        node = self.current_proof_node
        if node.children:
            messagebox.showwarning(
                "Error", "Rule already applied to this node. Select a leaf node."
            )
            return None, None, None

        if node.is_closed:
            messagebox.showwarning("Error", "This branch is already closed.")
            return None, None, None

        seq = node.sequent
        if self.selected_side == "lhs":
            target = seq.lhs[self.selected_formula_index]
        else:
            target = seq.rhs[self.selected_formula_index]
        return node, seq, target

    # --- Rule Logic Wrappers ---

    def apply_unary_rule(self, rule_name, new_lhs_list, new_rhs_list):
        node, seq, target = self.get_target()
        if not node:
            return

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
        self.update_tree_display(node, self.current_tree_id)
        self.tree.item(self.current_tree_id, open=True)

    def apply_binary_rule(self, rule_name, branch1_add, branch2_add):
        node, seq, target = self.get_target()
        if not node:
            return

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
        self.update_tree_display(node, self.current_tree_id)
        self.tree.item(self.current_tree_id, open=True)

    # --- Specific Rules ---

    def rule_and_l(self):
        node, seq, f = self.get_target()
        if not node or not isinstance(f, And) or self.selected_side != "lhs":
            return
        self.apply_unary_rule("∧L", [f.left, f.right], [])

    def rule_and_r(self):
        node, seq, f = self.get_target()
        if not node or not isinstance(f, And) or self.selected_side != "rhs":
            return
        self.apply_binary_rule("∧R", ([], [f.left]), ([], [f.right]))

    def rule_or_l(self):
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Or) or self.selected_side != "lhs":
            return
        self.apply_binary_rule("∨L", ([f.left], []), ([f.right], []))

    def rule_or_r(self):
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Or) or self.selected_side != "rhs":
            return
        self.apply_unary_rule("∨R", [], [f.left, f.right])

    def rule_imp_l(self):
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Implies) or self.selected_side != "lhs":
            return
        self.apply_binary_rule("→L", ([], [f.left]), ([f.right], []))

    def rule_imp_r(self):
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Implies) or self.selected_side != "rhs":
            return
        self.apply_unary_rule("→R", [f.left], [f.right])

    def rule_not_l(self):
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Not) or self.selected_side != "lhs":
            return
        self.apply_unary_rule("¬L", [], [f.inner])

    def rule_not_r(self):
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Not) or self.selected_side != "rhs":
            return
        self.apply_unary_rule("¬R", [f.inner], [])

    def rule_iff_l(self):
        """Bi-implication Left: Γ, F ↔ G ⊢ Δ becomes two branches:
           Branch 1: Γ, F, G ⊢ Δ (both true)
           Branch 2: Γ ⊢ F, G, Δ (both false)
        """
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Iff) or self.selected_side != "lhs":
            return
        self.apply_binary_rule("↔L", ([f.left, f.right], []), ([], [f.left, f.right]))

    def rule_iff_r(self):
        """Bi-implication Right: Γ ⊢ F ↔ G, Δ becomes two branches:
           Branch 1: Γ, F ⊢ G, Δ (F implies G)
           Branch 2: Γ, G ⊢ F, Δ (G implies F)
        """
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Iff) or self.selected_side != "rhs":
            return
        self.apply_binary_rule("↔R", ([f.left], [f.right]), ([f.right], [f.left]))

    def rule_top_r(self):
        """⊤R: Γ ⊢ ⊤, Δ is automatically closed (true is always provable on the right)"""
        if not self.current_proof_node:
            return
        node = self.current_proof_node
        
        # Check if Top (⊤) is in the succedent
        has_top = any(isinstance(f, Top) for f in node.sequent.rhs)
        
        if has_top:
            node.is_closed = True
            node.rule_applied = "⊤R"
            self.tree.item(self.current_tree_id, text="✔ " + str(node.sequent))
            self.status_var.set("Branch Closed by ⊤R (True is always provable).")
        else:
            messagebox.showinfo("⊤R", "No ⊤ (True) found in the succedent.")

    def rule_bot_l(self):
        """⊥L: Γ, ⊥ ⊢ Δ is automatically closed (false in antecedent proves anything)"""
        if not self.current_proof_node:
            return
        node = self.current_proof_node
        
        # Check if Bottom (⊥) is in the antecedent
        has_bot = any(isinstance(f, Bottom) for f in node.sequent.lhs)
        
        if has_bot:
            node.is_closed = True
            node.rule_applied = "⊥L"
            self.tree.item(self.current_tree_id, text="✔ " + str(node.sequent))
            self.status_var.set("Branch Closed by ⊥L (False implies anything).")
        else:
            messagebox.showinfo("⊥L", "No ⊥ (False/Bottom) found in the antecedent.")

    def rule_bot_r(self):
        """⊥R: Γ ⊢ ⊥, Δ ---> Γ ⊢ Δ (removes ⊥ from succedent, cannot prove false directly)"""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Bottom) or self.selected_side != "rhs":
            messagebox.showinfo("⊥R", "Select ⊥ (False/Bottom) in the succedent.")
            return
        # Remove ⊥ from the RHS
        self.apply_unary_rule("⊥R", [], [])
        self.status_var.set("Applied ⊥R (removed ⊥ from succedent).")

    def rule_top_l(self):
        """⊤L: Γ, ⊤ ⊢ Δ ---> Γ ⊢ Δ (removes vacuous ⊤ from antecedent)"""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Top) or self.selected_side != "lhs":
            messagebox.showinfo("⊤L", "Select ⊤ (True/Top) in the antecedent.")
            return
        # Remove ⊤ from the LHS
        self.apply_unary_rule("⊤L", [], [])
        self.status_var.set("Applied ⊤L (removed vacuous ⊤ from antecedent).")

    def rule_id(self):
        if not self.current_proof_node:
            return
        node = self.current_proof_node

        lhs_set = {str(x) for x in node.sequent.lhs}
        rhs_set = {str(x) for x in node.sequent.rhs}

        if not lhs_set.isdisjoint(rhs_set):
            node.is_closed = True
            node.rule_applied = "id"
            self.tree.item(self.current_tree_id, text="✔ " + str(node.sequent))
            self.status_var.set("Branch Closed successfully.")
        else:
            messagebox.showinfo(
                "Identity", "No common formula found in antecedent and succedent."
            )

    def undo_step(self):
        if not self.current_proof_node:
            return
        node = self.current_proof_node
        if node.parent:
            parent = node.parent
            parent.children = []
            parent.rule_applied = None

            parent_id = next((k for k, v in self.node_map.items() if v == parent), None)

            if parent_id:
                self.update_tree_display(parent, parent_id)
                self.tree.selection_set(parent_id)
                self.on_tree_select(None)
                self.status_var.set("Undid last step.")

    # =========================================================================
    # QUANTIFIER RULES
    # =========================================================================

    def rule_forall_r(self):
        """∀R: Γ ⊢ ∀x.P(x), Δ  --->  Γ ⊢ P(x'), Δ where x' is fresh"""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Forall) or self.selected_side != "rhs":
            return
        # Generate a fresh variable
        fresh_var = self.parser.get_fresh_var(f.var)
        # Substitute fresh variable in the body (simplified - just renames in display)
        new_body = self._substitute(f.inner, f.var, Atom(fresh_var))
        self.apply_unary_rule("∀R", [], [new_body])
        self.status_var.set(f"Applied ∀R with fresh variable {fresh_var}")

    def rule_forall_l(self):
        """∀L: Γ, ∀x.P(x) ⊢ Δ  --->  Γ, ∀x.P(x), P(e) ⊢ Δ (instantiate with term)
           For simplicity, prompts user for the instantiation term."""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Forall) or self.selected_side != "lhs":
            return
        # Ask user for the instantiation term
        term = self._ask_for_term(f"Instantiate {f.var} with:")
        if term is None:
            return
        # Keep the original formula and add the instantiated version
        new_body = self._substitute(f.inner, f.var, self.parser.parse(term))
        self.apply_unary_rule("∀L", [f, new_body], [])
        self.status_var.set(f"Applied ∀L with {f.var} = {term}")

    def rule_exists_r(self):
        """∃R: Γ ⊢ ∃x.P(x), Δ  --->  Γ ⊢ P(e), ∃x.P(x), Δ (instantiate with term)"""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Exists) or self.selected_side != "rhs":
            return
        term = self._ask_for_term(f"Instantiate {f.var} with:")
        if term is None:
            return
        new_body = self._substitute(f.inner, f.var, self.parser.parse(term))
        self.apply_unary_rule("∃R", [], [new_body, f])
        self.status_var.set(f"Applied ∃R with {f.var} = {term}")

    def rule_exists_l(self):
        """∃L: Γ, ∃x.P(x) ⊢ Δ  --->  Γ, P(x') ⊢ Δ where x' is fresh"""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Exists) or self.selected_side != "lhs":
            return
        fresh_var = self.parser.get_fresh_var(f.var)
        new_body = self._substitute(f.inner, f.var, Atom(fresh_var))
        self.apply_unary_rule("∃L", [new_body], [])
        self.status_var.set(f"Applied ∃L with fresh variable {fresh_var}")

    def _ask_for_term(self, prompt):
        """Show dialog to ask for a term."""
        from tkinter import simpledialog
        return simpledialog.askstring("Input Required", prompt, parent=self.root)

    def _substitute(self, formula, var, replacement):
        """Substitute var with replacement in formula (simple implementation)."""
        if isinstance(formula, Atom):
            if formula.name == var:
                return replacement
            return formula
        elif isinstance(formula, Not):
            return Not(self._substitute(formula.inner, var, replacement))
        elif isinstance(formula, (And, Or, Implies, Iff)):
            return type(formula)(
                self._substitute(formula.left, var, replacement),
                self._substitute(formula.right, var, replacement)
            )
        elif isinstance(formula, (Equals, NotEquals, LessThan, LessEq, GreaterThan, GreaterEq)):
            return type(formula)(
                self._substitute(formula.left, var, replacement),
                self._substitute(formula.right, var, replacement)
            )
        elif isinstance(formula, Forall):
            if formula.var == var:
                return formula  # Bound variable, don't substitute
            return Forall(formula.var, self._substitute(formula.inner, var, replacement))
        elif isinstance(formula, Exists):
            if formula.var == var:
                return formula
            return Exists(formula.var, self._substitute(formula.inner, var, replacement))
        elif isinstance(formula, Box):
            return Box(formula.program, self._substitute(formula.postcondition, var, replacement))
        elif isinstance(formula, Diamond):
            return Diamond(formula.program, self._substitute(formula.postcondition, var, replacement))
        elif isinstance(formula, Says):
            return Says(formula.principal, self._substitute(formula.inner, var, replacement))
        elif isinstance(formula, Aff):
            return Aff(formula.principal, self._substitute(formula.inner, var, replacement))
        return formula

    # =========================================================================
    # DYNAMIC LOGIC - BOX MODALITY RULES
    # =========================================================================

    def rule_assign_r(self):
        """[:=]R: Γ ⊢ [x := e]Q, Δ  --->  Γ, x' = e ⊢ Q[x'/x], Δ where x' is fresh"""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Box) or self.selected_side != "rhs":
            return
        if not isinstance(f.program, Assign):
            messagebox.showinfo("[:=]R", "Selected formula must be [x := e]Q")
            return
        prog = f.program
        fresh_var = self.parser.get_fresh_var(prog.var)
        # Create equality: x' = e
        equality = Equals(Atom(fresh_var), prog.expr)
        # Substitute x with x' in postcondition
        new_post = self._substitute(f.postcondition, prog.var, Atom(fresh_var))
        self.apply_unary_rule("[:=]R", [equality], [new_post])
        self.status_var.set(f"Applied [:=]R with fresh variable {fresh_var}")

    def rule_test_r(self):
        """[?]R: Γ ⊢ [?P]Q, Δ  --->  Γ, P ⊢ Q, Δ"""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Box) or self.selected_side != "rhs":
            return
        if not isinstance(f.program, Test):
            messagebox.showinfo("[?]R", "Selected formula must be [?P]Q")
            return
        test_formula = f.program.formula
        self.apply_unary_rule("[?]R", [test_formula], [f.postcondition])
        self.status_var.set("Applied [?]R (test right)")

    def rule_test_l(self):
        """[?]L: Γ, [?P]Q ⊢ Δ  --->  (Γ ⊢ P, Δ) AND (Γ, Q ⊢ Δ)"""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Box) or self.selected_side != "lhs":
            return
        if not isinstance(f.program, Test):
            messagebox.showinfo("[?]L", "Selected formula must be [?P]Q")
            return
        test_formula = f.program.formula
        self.apply_binary_rule("[?]L", ([], [test_formula]), ([f.postcondition], []))
        self.status_var.set("Applied [?]L (test left)")

    def rule_seq_r(self):
        """[;]R: Γ ⊢ [α;β]Q, Δ  --->  Γ ⊢ [α][β]Q, Δ"""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Box) or self.selected_side != "rhs":
            return
        if not isinstance(f.program, Seq):
            messagebox.showinfo("[;]R", "Selected formula must be [α;β]Q")
            return
        prog = f.program
        # [α;β]Q becomes [α][β]Q
        inner_box = Box(prog.second, f.postcondition)
        outer_box = Box(prog.first, inner_box)
        self.apply_unary_rule("[;]R", [], [outer_box])
        self.status_var.set("Applied [;]R (sequence composition)")

    def rule_seq_l(self):
        """[;]L: Γ, [α;β]Q ⊢ Δ  --->  Γ, [α][β]Q ⊢ Δ"""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Box) or self.selected_side != "lhs":
            return
        if not isinstance(f.program, Seq):
            messagebox.showinfo("[;]L", "Selected formula must be [α;β]Q")
            return
        prog = f.program
        # [α;β]Q becomes [α][β]Q on the left
        inner_box = Box(prog.second, f.postcondition)
        outer_box = Box(prog.first, inner_box)
        self.apply_unary_rule("[;]L", [outer_box], [])
        self.status_var.set("Applied [;]L (sequence composition left)")

    def rule_skip_r(self):
        """[skip]R: Γ ⊢ [skip]Q, Δ  --->  Γ ⊢ Q, Δ"""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Box) or self.selected_side != "rhs":
            return
        if not isinstance(f.program, Skip):
            messagebox.showinfo("[skip]R", "Selected formula must be [skip]Q")
            return
        self.apply_unary_rule("[skip]R", [], [f.postcondition])
        self.status_var.set("Applied [skip]R")

    def rule_skip_l(self):
        """[skip]L: Γ, [skip]Q ⊢ Δ  --->  Γ, Q ⊢ Δ"""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Box) or self.selected_side != "lhs":
            return
        if not isinstance(f.program, Skip):
            messagebox.showinfo("[skip]L", "Selected formula must be [skip]Q")
            return
        self.apply_unary_rule("[skip]L", [f.postcondition], [])
        self.status_var.set("Applied [skip]L")

    def rule_choice_r(self):
        """[∪]R: Γ ⊢ [α∪β]Q, Δ  --->  (Γ ⊢ [α]Q, Δ) AND (Γ ⊢ [β]Q, Δ)"""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Box) or self.selected_side != "rhs":
            return
        if not isinstance(f.program, Choice):
            messagebox.showinfo("[∪]R", "Selected formula must be [α∪β]Q")
            return
        prog = f.program
        box_left = Box(prog.left, f.postcondition)
        box_right = Box(prog.right, f.postcondition)
        self.apply_binary_rule("[∪]R", ([], [box_left]), ([], [box_right]))
        self.status_var.set("Applied [∪]R (choice right)")

    def rule_loop_unfold_r(self):
        """[*]unfold: Γ ⊢ [α*]Q, Δ  --->  (Γ ⊢ Q, Δ) AND (Γ ⊢ [α][α*]Q, Δ)
           Loop unfolds to: (base case: exit loop) OR (step: do α then repeat)"""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Box) or self.selected_side != "rhs":
            return
        if not isinstance(f.program, Loop):
            messagebox.showinfo("[*]R", "Selected formula must be [α*]Q")
            return
        prog = f.program
        # Base case: Q holds immediately (zero iterations)
        # Step case: [α][α*]Q - do one iteration then continue
        step_box = Box(prog.body, f)
        self.apply_binary_rule("[*]unfold", ([], [f.postcondition]), ([], [step_box]))
        self.status_var.set("Applied [*]unfold (loop unfolding)")

    def rule_if_r(self):
        """[if]R: Γ ⊢ [if P then α else β]Q, Δ  --->  
           (Γ, P ⊢ [α]Q, Δ) AND (Γ, ¬P ⊢ [β]Q, Δ)"""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Box) or self.selected_side != "rhs":
            return
        if not isinstance(f.program, IfProg):
            messagebox.showinfo("[if]R", "Selected formula must be [if P then α else β]Q")
            return
        prog = f.program
        then_box = Box(prog.then_branch, f.postcondition)
        else_box = Box(prog.else_branch, f.postcondition)
        neg_guard = Not(prog.guard)
        self.apply_binary_rule("[if]R", ([prog.guard], [then_box]), ([neg_guard], [else_box]))
        self.status_var.set("Applied [if]R (conditional)")

    def rule_while_unfold_r(self):
        """[while]unfold: Γ ⊢ [while P do α]Q, Δ  --->
           (Γ, P ⊢ [α][while P do α]Q, Δ) AND (Γ, ¬P ⊢ Q, Δ)"""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Box) or self.selected_side != "rhs":
            return
        if not isinstance(f.program, WhileProg):
            messagebox.showinfo("[while]R", "Selected formula must be [while P do α]Q")
            return
        prog = f.program
        # Continue case: guard true, do body, then repeat
        continue_box = Box(prog.body, f)
        neg_guard = Not(prog.guard)
        self.apply_binary_rule("[while]unfold", ([prog.guard], [continue_box]), ([neg_guard], [f.postcondition]))
        self.status_var.set("Applied [while]unfold")

    def rule_while_inv_r(self):
        """[while]inv: Use loop invariant J
           Γ ⊢ [while_J P do α]Q, Δ  requires:
           1. Γ ⊢ J, Δ  (invariant holds initially)
           2. J, P ⊢ [α]J  (invariant preserved)
           3. J, ¬P ⊢ Q  (invariant implies postcondition when loop exits)"""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Box) or self.selected_side != "rhs":
            return
        if not isinstance(f.program, WhileProg) or f.program.invariant is None:
            messagebox.showinfo("[while]inv", 
                "This rule requires a loop with invariant: while_J P do α\n"
                "Use [while]unfold for loops without invariant annotation.")
            return
        prog = f.program
        J = prog.invariant
        neg_guard = Not(prog.guard)
        body_box = Box(prog.body, J)
        
        # Create three branches using a special ternary rule
        node, seq, target = self.get_target()
        if not node:
            return
        
        base_lhs = seq.lhs[:]
        base_rhs = seq.rhs[:]
        del base_rhs[self.selected_formula_index]
        
        # Branch 1: Γ ⊢ J, Δ
        b1_seq = Sequent(base_lhs[:], base_rhs + [J])
        node.add_child(b1_seq)
        
        # Branch 2: J, P ⊢ [α]J
        b2_seq = Sequent([J, prog.guard], [body_box])
        node.add_child(b2_seq)
        
        # Branch 3: J, ¬P ⊢ Q
        b3_seq = Sequent([J, neg_guard], [f.postcondition])
        node.add_child(b3_seq)
        
        node.rule_applied = "[while]inv"
        self.update_tree_display(node, self.current_tree_id)
        self.tree.item(self.current_tree_id, open=True)
        self.status_var.set("Applied [while]inv with 3 branches")

    def rule_for_r(self):
        """[for]R: Desugar for loop to while loop
           [for 0 ≤ i < n do α]Q  --->  [i := 0; while (i < n) do (α; i := i + 1)]Q
           
           This rule desugars the bounded for loop into an assignment followed by
           a while loop with the iteration variable being incremented after each body execution.
        """
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Box) or self.selected_side != "rhs":
            return
        if not isinstance(f.program, ForProg):
            messagebox.showinfo("[for]R", "Selected formula must be [for 0 ≤ i < n do α]Q")
            return
        
        prog = f.program
        i = prog.loop_var
        n = prog.bound_var
        alpha = prog.body
        Q = f.postcondition
        
        # Build the desugared program:
        # i := 0; while (i < n) do (α; i := i + 1)
        
        # i := 0
        init_assign = Assign(i, Atom("0"))
        
        # i < n (guard)
        guard = LessThan(Atom(i), Atom(n))
        
        # i := i + 1 (increment) - simplified as i := i+1 atom
        increment = Assign(i, Atom(f"{i}+1"))
        
        # α; i := i + 1 (body with increment)
        body_with_inc = Seq(alpha, increment)
        
        # while (i < n) do (α; i := i + 1)
        while_prog = WhileProg(guard, body_with_inc)
        
        # i := 0; while_loop
        full_prog = Seq(init_assign, while_prog)
        
        # [full_prog]Q
        desugared_box = Box(full_prog, Q)
        
        self.apply_unary_rule("[for]R", [], [desugared_box])
        self.status_var.set("Applied [for]R (desugared to while loop)")

    # =========================================================================
    # STRUCTURAL RULES
    # =========================================================================

    def rule_weaken_l(self):
        """WL (Weakening Left): Add a formula to the antecedent"""
        if not self.current_proof_node:
            return
        node = self.current_proof_node
        if node.children or node.is_closed:
            messagebox.showwarning("Error", "Can only apply to leaf node.")
            return
        formula_str = self._ask_for_term("Formula to add to antecedent (LHS):")
        if formula_str is None:
            return
        formula = self.parser.parse(formula_str)
        if formula:
            new_lhs = node.sequent.lhs[:] + [formula]
            new_seq = Sequent(new_lhs, node.sequent.rhs[:])
            node.add_child(new_seq)
            node.rule_applied = "WL"
            self.update_tree_display(node, self.current_tree_id)
            self.status_var.set(f"Applied WL: added {formula}")

    def rule_weaken_r(self):
        """WR (Weakening Right): Add a formula to the succedent"""
        if not self.current_proof_node:
            return
        node = self.current_proof_node
        if node.children or node.is_closed:
            messagebox.showwarning("Error", "Can only apply to leaf node.")
            return
        formula_str = self._ask_for_term("Formula to add to succedent (RHS):")
        if formula_str is None:
            return
        formula = self.parser.parse(formula_str)
        if formula:
            new_rhs = node.sequent.rhs[:] + [formula]
            new_seq = Sequent(node.sequent.lhs[:], new_rhs)
            node.add_child(new_seq)
            node.rule_applied = "WR"
            self.update_tree_display(node, self.current_tree_id)
            self.status_var.set(f"Applied WR: added {formula}")

    def rule_contract_l(self):
        """CL (Contraction Left): Remove duplicate formula from antecedent"""
        node, seq, f = self.get_target()
        if not node or self.selected_side != "lhs":
            return
        # Check if formula appears more than once
        count = sum(1 for x in seq.lhs if str(x) == str(f))
        if count < 2:
            messagebox.showinfo("CL", "Formula must appear at least twice to contract.")
            return
        new_lhs = seq.lhs[:]
        del new_lhs[self.selected_formula_index]
        new_seq = Sequent(new_lhs, seq.rhs[:])
        node.add_child(new_seq)
        node.rule_applied = "CL"
        self.update_tree_display(node, self.current_tree_id)
        self.status_var.set("Applied CL (contraction left)")

    def rule_contract_r(self):
        """CR (Contraction Right): Remove duplicate formula from succedent"""
        node, seq, f = self.get_target()
        if not node or self.selected_side != "rhs":
            return
        count = sum(1 for x in seq.rhs if str(x) == str(f))
        if count < 2:
            messagebox.showinfo("CR", "Formula must appear at least twice to contract.")
            return
        new_rhs = seq.rhs[:]
        del new_rhs[self.selected_formula_index]
        new_seq = Sequent(seq.lhs[:], new_rhs)
        node.add_child(new_seq)
        node.rule_applied = "CR"
        self.update_tree_display(node, self.current_tree_id)
        self.status_var.set("Applied CR (contraction right)")

    def rule_cut(self):
        """Cut: Introduce a formula C to split the proof
           Γ ⊢ Δ  --->  (Γ ⊢ C, Δ) AND (Γ, C ⊢ Δ)"""
        if not self.current_proof_node:
            return
        node = self.current_proof_node
        if node.children or node.is_closed:
            messagebox.showwarning("Error", "Can only apply to leaf node.")
            return
        formula_str = self._ask_for_term("Cut formula (C):")
        if formula_str is None:
            return
        cut_formula = self.parser.parse(formula_str)
        if cut_formula:
            base_lhs = node.sequent.lhs[:]
            base_rhs = node.sequent.rhs[:]
            
            # Branch 1: Γ ⊢ C, Δ (prove C)
            b1_seq = Sequent(base_lhs[:], [cut_formula] + base_rhs[:])
            node.add_child(b1_seq)
            
            # Branch 2: Γ, C ⊢ Δ (use C)
            b2_seq = Sequent(base_lhs[:] + [cut_formula], base_rhs[:])
            node.add_child(b2_seq)
            
            node.rule_applied = "cut"
            self.update_tree_display(node, self.current_tree_id)
            self.tree.item(self.current_tree_id, open=True)
            self.status_var.set(f"Applied cut with formula: {cut_formula}")

    # =========================================================================
    # AUTHORIZATION LOGIC RULES (Lectures 15-17)
    # =========================================================================

    def rule_says_r(self):
        """saysR: Γ ⊢ (A says P), Δ  --->  Γ ⊢ (A aff P), Δ
           To prove A says P, switch to proving A aff P."""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Says) or self.selected_side != "rhs":
            messagebox.showinfo("saysR", "Select a 'says' formula in the succedent (RHS).\n\nSyntax: principal says P")
            return
        # Replace (A says P) with (A aff P) in the RHS
        self.apply_unary_rule("saysR", [], [Aff(f.principal, f.inner)])
        self.status_var.set(f"Applied saysR: now prove {f.principal} aff {f.inner}")

    def rule_says_l(self):
        """saysL: Γ, A says P ⊢ A aff Q  --->  Γ, P ⊢ A aff Q
           Unwrap A says P when the goal is A aff Q (same principal)."""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Says) or self.selected_side != "lhs":
            messagebox.showinfo("saysL", "Select a 'says' formula in the antecedent (LHS).\n\nSyntax: principal says P")
            return
        # Check that the succedent contains an 'aff' for the same principal
        has_matching_aff = False
        for rhs_f in seq.rhs:
            if isinstance(rhs_f, Aff) and rhs_f.principal == f.principal:
                has_matching_aff = True
                break
        if not has_matching_aff:
            messagebox.showinfo("saysL",
                f"saysL requires the succedent to contain '{f.principal} aff Q'\n"
                f"for the same principal '{f.principal}'.\n\n"
                f"Current succedent: {', '.join(str(x) for x in seq.rhs)}")
            return
        # Remove (A says P), add P
        self.apply_unary_rule("saysL", [f.inner], [])
        self.status_var.set(f"Applied saysL: unwrapped {f.principal} says into {f.inner}")

    def rule_aff(self):
        """aff: Γ ⊢ (A aff P), Δ  --->  Γ ⊢ P, Δ
           Switch from affirmation judgment back to truth."""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Aff) or self.selected_side != "rhs":
            messagebox.showinfo("aff", "Select an 'aff' formula in the succedent (RHS).\n\nSyntax: principal aff P")
            return
        # Replace (A aff P) with P in the RHS
        self.apply_unary_rule("aff", [], [f.inner])
        self.status_var.set(f"Applied aff: now prove {f.inner} (from {f.principal}'s perspective)")

    def rule_or_r1(self):
        """∨R₁ (intuitionistic): Γ ⊢ P ∨ Q  --->  Γ ⊢ P
           Choose the LEFT disjunct only."""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Or) or self.selected_side != "rhs":
            messagebox.showinfo("∨R₁", "Select a disjunction (P ∨ Q) in the succedent (RHS).")
            return
        self.apply_unary_rule("∨R₁", [], [f.left])
        self.status_var.set(f"Applied ∨R₁: chose left disjunct {f.left}")

    def rule_or_r2(self):
        """∨R₂ (intuitionistic): Γ ⊢ P ∨ Q  --->  Γ ⊢ Q
           Choose the RIGHT disjunct only."""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Or) or self.selected_side != "rhs":
            messagebox.showinfo("∨R₂", "Select a disjunction (P ∨ Q) in the succedent (RHS).")
            return
        self.apply_unary_rule("∨R₂", [], [f.right])
        self.status_var.set(f"Applied ∨R₂: chose right disjunct {f.right}")

    def rule_trust_add(self):
        """Declare a trust relationship A ≤ B."""
        from tkinter import simpledialog
        input_str = simpledialog.askstring(
            "Set Trust Relationship",
            "Enter trust fact (format: A <= B):\n\n"
            "Example: admin <= fp\n"
            "Meaning: admin trusts fp",
            parent=self.root)
        if input_str is None:
            return
        input_str = input_str.strip()
        if "<=" not in input_str:
            messagebox.showinfo("Trust", "Format: A <= B\nExample: admin <= fp")
            return
        parts = input_str.split("<=")
        a = parts[0].strip()
        b = parts[1].strip()
        if not a or not b:
            messagebox.showinfo("Trust", "Both principal names are required.")
            return
        self.trust_facts.append((a, b))
        self.status_var.set(f"Trust added: {a} ≤ {b}  (total: {len(self.trust_facts)} facts)")

    def _trust_holds(self, a, b):
        """Check if a ≤ b via reflexivity + transitivity."""
        if a == b:
            return True
        visited = set()
        stack = [a]
        while stack:
            cur = stack.pop()
            if cur == b:
                return True
            if cur in visited:
                continue
            visited.add(cur)
            for (x, y) in self.trust_facts:
                if x == cur:
                    stack.append(y)
        return False

    def rule_trust_says(self):
        """≤-says: If A ≤ B and (B says P) is in the LHS, rewrite it to (A says P).
           Select the (B says P) formula on the LHS."""
        node, seq, f = self.get_target()
        if not node or not isinstance(f, Says) or self.selected_side != "lhs":
            messagebox.showinfo("≤-says", "Select a 'says' formula in the antecedent.\n\nThis rule rewrites (B says P) → (A says P) when A ≤ B.")
            return
        if not self.trust_facts:
            messagebox.showinfo("≤-says", "No trust relationships set.\n\nUse 'Set trust...' to declare A ≤ B first.")
            return
        # Find all principals A such that A ≤ f.principal (A trusts B)
        from tkinter import simpledialog
        eligible = []
        for (a, b) in self.trust_facts:
            if self._trust_holds(a, f.principal) and a != f.principal:
                eligible.append(a)
        # Remove duplicates
        eligible = list(set(eligible))
        if not eligible:
            messagebox.showinfo("≤-says",
                f"No principal A found with A ≤ {f.principal}.\n\n"
                f"Current trust facts: {', '.join(a + ' ≤ ' + b for a, b in self.trust_facts)}")
            return
        if len(eligible) == 1:
            target_principal = eligible[0]
        else:
            target_principal = simpledialog.askstring(
                "≤-says",
                f"Multiple principals trust {f.principal}:\n"
                f"  {', '.join(eligible)}\n\n"
                f"Which principal A to use for A says {f.inner}?",
                parent=self.root)
            if target_principal is None or target_principal.strip() not in eligible:
                return
            target_principal = target_principal.strip()
        # Replace (B says P) with (A says P)
        new_formula = Says(target_principal, f.inner)
        self.apply_unary_rule("≤-says", [new_formula], [])
        self.status_var.set(f"Applied ≤-says: {f.principal} says → {target_principal} says (via {target_principal} ≤ {f.principal})")

    def rule_cut_prime(self):
        """cut' (Lecture 16): Γ₁,Γ₂ ⊢ δ  from  Γ₁ ⊢ P  and  Γ₂,P ⊢ δ
           Split-context variant of cut. User picks which LHS formulas go to Γ₁."""
        if not self.current_proof_node:
            return
        node = self.current_proof_node
        if node.children or node.is_closed:
            messagebox.showwarning("Error", "Can only apply to leaf node.")
            return
        from tkinter import simpledialog
        formula_str = simpledialog.askstring("cut'", "Cut formula P:", parent=self.root)
        if formula_str is None:
            return
        cut_formula = self.parser.parse(formula_str)
        if not cut_formula:
            return
        # Ask which LHS indices go to Γ₁ (the rest go to Γ₂)
        lhs_strs = [f"{i}: {f}" for i, f in enumerate(node.sequent.lhs)]
        indices_str = simpledialog.askstring(
            "cut' — split context",
            f"Current LHS:\n" + "\n".join(lhs_strs) + "\n\n"
            f"Enter indices for Γ₁ (comma-separated).\n"
            f"The rest go to Γ₂.\n\n"
            f"Example: 0,2",
            parent=self.root)
        if indices_str is None:
            return
        try:
            gamma1_indices = set(int(x.strip()) for x in indices_str.split(",") if x.strip())
        except ValueError:
            messagebox.showinfo("cut'", "Enter comma-separated integers.")
            return
        gamma1 = [f for i, f in enumerate(node.sequent.lhs) if i in gamma1_indices]
        gamma2 = [f for i, f in enumerate(node.sequent.lhs) if i not in gamma1_indices]
        # Branch 1: Γ₁ ⊢ P
        b1_seq = Sequent(gamma1, [cut_formula])
        node.add_child(b1_seq)
        # Branch 2: Γ₂, P ⊢ δ
        b2_seq = Sequent(gamma2 + [cut_formula], node.sequent.rhs[:])
        node.add_child(b2_seq)
        node.rule_applied = "cut'"
        self.update_tree_display(node, self.current_tree_id)
        self.tree.item(self.current_tree_id, open=True)
        self.status_var.set(f"Applied cut' with P = {cut_formula}")

    # --- Updated Export ---

    def export_latex(self):
        if not self.root_node:
            return

        # Pretty-print logic with indentation
        def recursive_build(node, depth=0):
            indent = "  " * depth
            rule = node.rule_applied if node.rule_applied else "?"
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

            sequent_tex = node.sequent.to_latex()

            # Leaf case
            if not node.children:
                if node.is_closed:
                    return f"{indent}\\infer[\\ms{{id}}]\n{indent}  {{{sequent_tex}}}\n{indent}  {{}}"
                else:
                    return f"{indent}\\deduce[?]\n{indent}  {{{sequent_tex}}}\n{indent}  {{}}"

            # Recursive case
            # Create premises strings
            premises = []
            for child in node.children:
                premises.append(recursive_build(child, depth + 1))

            # Join premises with '&' on new lines for readability
            joined_premises = f"\n{indent}  &\n".join(premises)

            return f"{indent}\\infer[{rule_tex}]\n{indent}  {{{sequent_tex}}}\n{indent}  {{\n{joined_premises}\n{indent}  }}"

        latex_code = (
            "\\begin{rules}\n" + recursive_build(self.root_node) + "\n\\end{rules}"
        )

        # -- Export Dialog --
        win = tk.Toplevel(self.root)
        win.title("LaTeX Code Export")
        win.geometry("700x500")

        # Buttons Frame
        btn_frame = ttk.Frame(win, padding=10)
        btn_frame.pack(side=tk.BOTTOM, fill=tk.X)

        def copy_to_clipboard():
            self.root.clipboard_clear()
            self.root.clipboard_append(latex_code)
            self.root.update()  # Required to prevent clipboard loss
            messagebox.showinfo("Copied", "LaTeX code copied to clipboard!")

        ttk.Button(
            btn_frame, text="📋 Copy to Clipboard", command=copy_to_clipboard
        ).pack(side=tk.RIGHT)
        ttk.Button(btn_frame, text="Close", command=win.destroy).pack(
            side=tk.RIGHT, padx=5
        )

        # Text Area with Scroll
        txt_frame = ttk.Frame(win)
        txt_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        scroll = ttk.Scrollbar(txt_frame)
        scroll.pack(side=tk.RIGHT, fill=tk.Y)

        txt = tk.Text(
            txt_frame, font=("Consolas", 10), yscrollcommand=scroll.set, wrap=tk.NONE
        )
        txt.pack(fill=tk.BOTH, expand=True)
        scroll.config(command=txt.yview)

        txt.insert(tk.END, latex_code)

    # --- Custom Rules System ---
    
    def _refresh_custom_rules_ui(self):
        """Refresh the custom rules buttons in the UI."""
        # Clear existing buttons
        for widget in self.custom_rules_frame.winfo_children():
            widget.destroy()
        
        if not self.custom_rules:
            ttk.Label(
                self.custom_rules_frame, 
                text="No custom rules defined. Click '+ Add Rule' to create one.",
                font=("Segoe UI", 9, "italic"),
                foreground="#888"
            ).pack(pady=5)
            return
        
        # Create buttons for each custom rule
        for i, rule in enumerate(self.custom_rules):
            rule_frame = ttk.Frame(self.custom_rules_frame)
            rule_frame.pack(fill=tk.X, pady=2)
            
            # Rule button
            btn = ttk.Button(
                rule_frame, 
                text=f"{rule['name']} ({rule['side'].upper()})",
                command=lambda r=rule: self._apply_custom_rule(r)
            )
            btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=2)
            
            # Delete button
            del_btn = ttk.Button(
                rule_frame,
                text="×",
                width=3,
                command=lambda idx=i: self._delete_custom_rule(idx)
            )
            del_btn.pack(side=tk.RIGHT, padx=2)
    
    def _delete_custom_rule(self, index):
        """Delete a custom rule by index."""
        if 0 <= index < len(self.custom_rules):
            rule_name = self.custom_rules[index]['name']
            if messagebox.askyesno("Delete Rule", f"Delete custom rule '{rule_name}'?"):
                del self.custom_rules[index]
                self._save_custom_rules()
                self._refresh_custom_rules_ui()
                self.status_var.set(f"Custom rule '{rule_name}' deleted.")
    
    def _apply_custom_rule(self, rule):
        """Apply a custom rule to the current sequent."""
        node, seq, f = self.get_target()
        if not node:
            return
        
        # Check if we're on the correct side
        if self.selected_side != rule['side']:
            messagebox.showwarning(
                "Wrong Side", 
                f"This rule applies to the {rule['side'].upper()} side. "
                f"Please select a formula from the {rule['side'].upper()}."
            )
            return
        
        # Parse what formulas to add to LHS and RHS
        try:
            # Replace placeholders with actual formula parts
            def parse_additions(additions_str, formula):
                if not additions_str.strip():
                    return []
                
                result = []
                parts = [p.strip() for p in additions_str.split(',')]
                for part in parts:
                    if not part:
                        continue
                    # Replace special placeholders
                    if part.upper() == 'LEFT' and hasattr(f, 'left'):
                        result.append(f.left)
                    elif part.upper() == 'RIGHT' and hasattr(f, 'right'):
                        result.append(f.right)
                    elif part.upper() == 'INNER' and hasattr(f, 'inner'):
                        result.append(f.inner)
                    elif part.upper() == 'FORMULA':
                        result.append(f)
                    else:
                        # Parse as a literal formula
                        parsed = self.parser.parse(part)
                        if parsed:
                            result.append(parsed)
                return result
            
            if rule['rule_type'] == 'unary':
                new_lhs = parse_additions(rule.get('add_to_lhs', ''), f)
                new_rhs = parse_additions(rule.get('add_to_rhs', ''), f)
                self.apply_unary_rule(rule['name'], new_lhs, new_rhs)
                self.status_var.set(f"Applied custom rule: {rule['name']}")
            
            elif rule['rule_type'] == 'binary':
                # Branch 1
                b1_lhs = parse_additions(rule.get('branch1_lhs', ''), f)
                b1_rhs = parse_additions(rule.get('branch1_rhs', ''), f)
                # Branch 2
                b2_lhs = parse_additions(rule.get('branch2_lhs', ''), f)
                b2_rhs = parse_additions(rule.get('branch2_rhs', ''), f)
                self.apply_binary_rule(rule['name'], (b1_lhs, b1_rhs), (b2_lhs, b2_rhs))
                self.status_var.set(f"Applied custom rule: {rule['name']}")
            
            elif rule['rule_type'] == 'close':
                # Check condition and close if met
                node.is_closed = True
                node.rule_applied = rule['name']
                self.tree.item(self.current_tree_id, text="✔ " + str(node.sequent))
                self.status_var.set(f"Branch closed by custom rule: {rule['name']}")
                
        except Exception as e:
            messagebox.showerror("Rule Error", f"Error applying rule: {e}")
    
    def open_custom_rule_dialog(self):
        """Open a dialog to create a new custom rule."""
        dialog = tk.Toplevel(self.root)
        dialog.title("Create Custom Rule")
        dialog.geometry("500x550")
        dialog.transient(self.root)
        dialog.grab_set()
        
        # Main frame with padding
        main_frame = ttk.Frame(dialog, padding=15)
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        # Rule Name
        ttk.Label(main_frame, text="Rule Name:", font=self.header_font).grid(
            row=0, column=0, sticky="w", pady=5
        )
        name_var = tk.StringVar()
        ttk.Entry(main_frame, textvariable=name_var, font=self.mono_font).grid(
            row=0, column=1, sticky="ew", pady=5
        )
        
        # Side (LHS or RHS)
        ttk.Label(main_frame, text="Applies to Side:", font=self.header_font).grid(
            row=1, column=0, sticky="w", pady=5
        )
        side_var = tk.StringVar(value="lhs")
        side_frame = ttk.Frame(main_frame)
        side_frame.grid(row=1, column=1, sticky="w", pady=5)
        ttk.Radiobutton(side_frame, text="LHS (Antecedent)", variable=side_var, value="lhs").pack(side=tk.LEFT)
        ttk.Radiobutton(side_frame, text="RHS (Succedent)", variable=side_var, value="rhs").pack(side=tk.LEFT)
        
        # Rule Type
        ttk.Label(main_frame, text="Rule Type:", font=self.header_font).grid(
            row=2, column=0, sticky="w", pady=5
        )
        type_var = tk.StringVar(value="unary")
        type_frame = ttk.Frame(main_frame)
        type_frame.grid(row=2, column=1, sticky="w", pady=5)
        ttk.Radiobutton(type_frame, text="Unary (1 branch)", variable=type_var, value="unary").pack(side=tk.LEFT)
        ttk.Radiobutton(type_frame, text="Binary (2 branches)", variable=type_var, value="binary").pack(side=tk.LEFT)
        ttk.Radiobutton(type_frame, text="Close Branch", variable=type_var, value="close").pack(side=tk.LEFT)
        
        # Separator
        ttk.Separator(main_frame, orient="horizontal").grid(
            row=3, column=0, columnspan=2, sticky="ew", pady=10
        )
        
        # Help text
        help_text = ttk.Label(
            main_frame,
            text="Use placeholders: LEFT, RIGHT (for binary formulas), INNER (for Not), FORMULA (entire formula)",
            font=("Segoe UI", 9, "italic"),
            foreground="#666",
            wraplength=450
        )
        help_text.grid(row=4, column=0, columnspan=2, sticky="w", pady=5)
        
        # Unary rule inputs
        unary_frame = ttk.LabelFrame(main_frame, text="Unary Rule (adds to sequent)", padding=10)
        unary_frame.grid(row=5, column=0, columnspan=2, sticky="ew", pady=5)
        
        ttk.Label(unary_frame, text="Add to LHS:").grid(row=0, column=0, sticky="w")
        add_lhs_var = tk.StringVar()
        ttk.Entry(unary_frame, textvariable=add_lhs_var, width=40).grid(row=0, column=1, sticky="ew", padx=5)
        
        ttk.Label(unary_frame, text="Add to RHS:").grid(row=1, column=0, sticky="w")
        add_rhs_var = tk.StringVar()
        ttk.Entry(unary_frame, textvariable=add_rhs_var, width=40).grid(row=1, column=1, sticky="ew", padx=5)
        
        # Binary rule inputs  
        binary_frame = ttk.LabelFrame(main_frame, text="Binary Rule (two branches)", padding=10)
        binary_frame.grid(row=6, column=0, columnspan=2, sticky="ew", pady=5)
        
        ttk.Label(binary_frame, text="Branch 1 - Add to LHS:").grid(row=0, column=0, sticky="w")
        b1_lhs_var = tk.StringVar()
        ttk.Entry(binary_frame, textvariable=b1_lhs_var, width=35).grid(row=0, column=1, sticky="ew", padx=5)
        
        ttk.Label(binary_frame, text="Branch 1 - Add to RHS:").grid(row=1, column=0, sticky="w")
        b1_rhs_var = tk.StringVar()
        ttk.Entry(binary_frame, textvariable=b1_rhs_var, width=35).grid(row=1, column=1, sticky="ew", padx=5)
        
        ttk.Label(binary_frame, text="Branch 2 - Add to LHS:").grid(row=2, column=0, sticky="w")
        b2_lhs_var = tk.StringVar()
        ttk.Entry(binary_frame, textvariable=b2_lhs_var, width=35).grid(row=2, column=1, sticky="ew", padx=5)
        
        ttk.Label(binary_frame, text="Branch 2 - Add to RHS:").grid(row=3, column=0, sticky="w")
        b2_rhs_var = tk.StringVar()
        ttk.Entry(binary_frame, textvariable=b2_rhs_var, width=35).grid(row=3, column=1, sticky="ew", padx=5)
        
        # Description
        ttk.Label(main_frame, text="Description (optional):").grid(row=7, column=0, sticky="w", pady=5)
        desc_var = tk.StringVar()
        ttk.Entry(main_frame, textvariable=desc_var, font=self.mono_font).grid(
            row=7, column=1, sticky="ew", pady=5
        )
        
        main_frame.columnconfigure(1, weight=1)
        
        # Buttons
        btn_frame = ttk.Frame(main_frame)
        btn_frame.grid(row=8, column=0, columnspan=2, pady=15)
        
        def save_rule():
            name = name_var.get().strip()
            if not name:
                messagebox.showwarning("Missing Name", "Please enter a rule name.")
                return
            
            # Check for duplicate names
            if any(r['name'] == name for r in self.custom_rules):
                messagebox.showwarning("Duplicate", f"A rule named '{name}' already exists.")
                return
            
            rule = {
                'name': name,
                'side': side_var.get(),
                'rule_type': type_var.get(),
                'description': desc_var.get(),
                'add_to_lhs': add_lhs_var.get(),
                'add_to_rhs': add_rhs_var.get(),
                'branch1_lhs': b1_lhs_var.get(),
                'branch1_rhs': b1_rhs_var.get(),
                'branch2_lhs': b2_lhs_var.get(),
                'branch2_rhs': b2_rhs_var.get(),
            }
            
            self.custom_rules.append(rule)
            self._save_custom_rules()
            self._refresh_custom_rules_ui()
            self.status_var.set(f"Custom rule '{name}' created and saved.")
            dialog.destroy()
        
        ttk.Button(btn_frame, text="Save Rule", command=save_rule).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Cancel", command=dialog.destroy).pack(side=tk.LEFT, padx=5)


if __name__ == "__main__":
    root = tk.Tk()
    app = SequentProverApp(root)
    root.mainloop()
