import tkinter as tk
from tkinter import ttk, messagebox, font
import re

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


class LogicParser:
    def __init__(self):
        self.tokens = []
        self.pos = 0

    def tokenize(self, text):
        text = text.replace("(", " ( ").replace(")", " ) ")
        text = re.sub(r"\bimplies\b", "->", text, flags=re.IGNORECASE)
        text = re.sub(r"\band\b", "&", text, flags=re.IGNORECASE)
        text = re.sub(r"\bor\b", "|", text, flags=re.IGNORECASE)
        text = re.sub(r"\bnot\b", "~", text, flags=re.IGNORECASE)
        return text.split()

    def parse(self, text):
        self.tokens = self.tokenize(text)
        self.pos = 0
        if not self.tokens:
            return None
        return self.parse_implies()

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
        left = self.parse_not()
        while self.pos < len(self.tokens) and self.tokens[self.pos] == "&":
            self.pos += 1
            right = self.parse_not()
            left = And(left, right)
        return left

    def parse_not(self):
        if self.pos < len(self.tokens) and self.tokens[self.pos] == "~":
            self.pos += 1
            return Not(self.parse_not())
        return self.parse_atom()

    def parse_atom(self):
        token = self.tokens[self.pos]
        self.pos += 1
        if token == "(":
            expr = self.parse_implies()
            if self.pos < len(self.tokens) and self.tokens[self.pos] == ")":
                self.pos += 1
            return expr
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
        l = ", ".join(f.to_latex() for f in self.lhs)
        r = ", ".join(f.to_latex() for f in self.rhs)
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
    def __init__(self, root):
        self.root = root
        self.root.title("Sequent Calculus Assistant")
        self.root.geometry("1100x750")

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

        self._setup_ui()

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

        # 2. Rule Controls
        controls_frame = ttk.LabelFrame(
            work_frame, text=" 🛠 Rule Application ", padding=10
        )
        controls_frame.pack(fill=tk.X, padx=(10, 0), pady=(10, 0))

        # Grid Headers
        ttk.Label(
            controls_frame,
            text="Connective",
            font=("Segoe UI", 9, "bold"),
            foreground="#666",
        ).grid(row=0, column=0, pady=5)
        ttk.Label(
            controls_frame,
            text="Left Rule (Antecedent)",
            font=("Segoe UI", 9, "bold"),
            foreground="#666",
        ).grid(row=0, column=1, pady=5)
        ttk.Label(
            controls_frame,
            text="Right Rule (Succedent)",
            font=("Segoe UI", 9, "bold"),
            foreground="#666",
        ).grid(row=0, column=2, pady=5)

        def create_rule_row(row, symbol, name, cmd_l, cmd_r):
            lbl = ttk.Label(
                controls_frame, text=f"{symbol} ({name})", font=self.symbol_font
            )
            lbl.grid(row=row, column=0, padx=10, pady=2)
            btn_l = ttk.Button(controls_frame, text=f"{symbol} Left", command=cmd_l)
            btn_l.grid(row=row, column=1, sticky="ew", padx=5, pady=2)
            btn_r = ttk.Button(controls_frame, text=f"{symbol} Right", command=cmd_r)
            btn_r.grid(row=row, column=2, sticky="ew", padx=5, pady=2)

        create_rule_row(1, "∧", "And", self.rule_and_l, self.rule_and_r)
        create_rule_row(2, "∨", "Or", self.rule_or_l, self.rule_or_r)
        create_rule_row(3, "→", "Implies", self.rule_imp_l, self.rule_imp_r)
        create_rule_row(4, "¬", "Not", self.rule_not_l, self.rule_not_r)

        sep = ttk.Separator(controls_frame, orient="horizontal")
        sep.grid(row=5, column=0, columnspan=3, sticky="ew", pady=10)

        action_frame = ttk.Frame(controls_frame)
        action_frame.grid(row=6, column=0, columnspan=3, sticky="ew")

        ttk.Button(
            action_frame, text="✔ Check Identity (Axiom)", command=self.rule_id
        ).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=2)
        ttk.Button(action_frame, text="↶ Undo Last Step", command=self.undo_step).pack(
            side=tk.LEFT, fill=tk.X, expand=True, padx=2
        )

        controls_frame.columnconfigure(1, weight=1)
        controls_frame.columnconfigure(2, weight=1)

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
            )

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


if __name__ == "__main__":
    root = tk.Tk()
    app = SequentProverApp(root)
    root.mainloop()
