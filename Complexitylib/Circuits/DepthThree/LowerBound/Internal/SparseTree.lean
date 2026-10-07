/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.SparsePrefix
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.SparseStreams
public import Mathlib.Data.Nat.Find

/-!
# Unrestricted depth-three lower bound: sparse tree

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/SparseTree.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

noncomputable section

namespace DepthThreeLowerBound

open scoped BigOperators

variable {V : Type uDepth1} [DecidableEq V]

/-- There exists an eligible sunflower in the current state. -/
def SparseEligible (r : ℕ → ℕ) (s : SparseState V) : Prop :=
  ∃ i, Nonempty (SignedSunflower s i (r i))

/-- There is no eligible sunflower left in the current state. -/
def SparseTerminal (r : ℕ → ℕ) (s : SparseState V) : Prop :=
  ∀ i, ¬ Nonempty (SignedSunflower s i (r i))

theorem sparseTerminal_of_not_eligible {r : ℕ → ℕ} {s : SparseState V}
    (h : ¬ SparseEligible r s) : SparseTerminal r s :=
  fun i hi => h ⟨i, hi⟩

/-- A smallest eligible sunflower selected for branching. -/
structure SparseSelection (r : ℕ → ℕ) (s : SparseState V) where
  /-- The common size of the selected clauses. -/
  size : ℕ
  /-- The selected signed sunflower. -/
  selected : SignedSunflower s size (r size)
  minimal : ∀ j, 2 ≤ j → j < size →
    ¬ Nonempty (SignedSunflower s j (r j))

/-- Choose a smallest eligible sunflower when one exists. -/
def sparseSelect (r : ℕ → ℕ) (s : SparseState V) (h : SparseEligible r s) :
    SparseSelection r s := by
  classical
  exact {
    size := Nat.find h
    selected := Classical.choice (Nat.find_spec h)
    minimal := fun _ _ hj => Nat.find_min h hj }

namespace SparseSelection

variable {r : ℕ → ℕ} {s : SparseState V} {b : ℕ}

/-- The successor state selected by the Boolean branch choice. -/
def branch (c : SparseSelection r s) (choice : Bool) : SparseState V :=
  c.selected.branch choice

/-- The certified sparsification step determined by a selected branch. -/
def step (c : SparseSelection r s) (choice : Bool) :
    SparseStep r s (c.branch choice) where
  size := c.size
  selected := c.selected
  minimal := c.minimal
  choice := choice
  target := rfl

/-- The clause-size label attached to a selected sunflower. -/
def label (c : SparseSelection r s) (hs : s.Valid b) : Fin (b + 1) :=
  ⟨c.size, Nat.lt_succ_of_le (c.selected.size_le hs)⟩

theorem branch_valid (c : SparseSelection r s) (hs : s.Valid b) (choice : Bool) :
    (c.branch choice).Valid b := c.selected.branch_valid choice hs

theorem branch_eval_imp (c : SparseSelection r s) (choice : Bool) (x : Cube V)
    (h : (c.branch choice).eval x = true) : s.eval x = true := by
  cases choice
  · change c.selected.coreBranch.eval x = true at h
    rw [c.selected.eval_coreBranch, Bool.and_eq_true] at h
    exact h.1
  · change c.selected.petalBranch.eval x = true at h
    rw [c.selected.eval_petalBranch, Bool.and_eq_true] at h
    exact h.1

end SparseSelection

namespace SparsePath

variable {r : ℕ → ℕ} {start middle finish : SparseState V}

/-- Prepend one step to a sparsification path. -/
def prepend (step : SparseStep r start middle) :
    {finish : SparseState V} → SparsePath r middle finish → SparsePath r start finish
  | _, .nil => .snoc .nil step
  | _, .snoc path next => .snoc (path.prepend step) next

theorem length_prepend (step : SparseStep r start middle)
    (path : SparsePath r middle finish) :
    (path.prepend step).length = 1 + path.length := by
  induction path with
  | nil => rfl
  | snoc path next ih => simp only [prepend, length, ih, Nat.add_assoc]

theorem processed_prepend (step : SparseStep r start middle)
    (path : SparsePath r middle finish) (i : ℕ) :
    (path.prepend step).processed i =
      (if step.size = i then 1 else 0) + path.processed i := by
  induction path with
  | nil => simp only [prepend, processed, Nat.zero_add, Nat.add_zero]
  | snoc path next ih => simp only [prepend, processed, ih, Nat.add_assoc]

theorem petalSteps_prepend (step : SparseStep r start middle)
    (path : SparsePath r middle finish) (i : ℕ) :
    (path.prepend step).petalSteps i =
      (if step.size = i ∧ step.choice = true then 1 else 0) + path.petalSteps i := by
  induction path with
  | nil => simp only [prepend, petalSteps, Nat.zero_add, Nat.add_zero]
  | snoc path next ih => simp only [prepend, petalSteps, ih, Nat.add_assoc]

end SparsePath

/-- A finite sparsification tree with valid paths and terminal leaves. -/
structure SparseTreeResult (r : ℕ → ℕ) (b : ℕ) (start : SparseState V) (fuel : ℕ) where
  /-- The binary sparsification decision tree. -/
  tree : SparseDecisionTree (Fin (b + 1))
  /-- The final state at each leaf. -/
  finish : tree.Leaf → SparseState V
  /-- The sequence of sparsification steps leading to each leaf. -/
  path : (p : tree.Leaf) → SparsePath r start (finish p)
  terminal_or_exhausted : ∀ p, SparseTerminal r (finish p) ∨ (path p).length = fuel
  stream_length : ∀ p i, (tree.stream p i).length = (path p).processed i.val
  stream_ones : ∀ p i, (tree.stream p i).count true = (path p).petalSteps i.val
  leaf_eval_imp : ∀ p x, (finish p).eval x = true → start.eval x = true
  indicator_eq_sum : ∀ x, indicator (start.eval x) = ∑ p, indicator ((finish p).eval x)
  disjoint : ∀ p q, p ≠ q → ∀ x,
    ¬ ((finish p).eval x = true ∧ (finish q).eval x = true)

namespace SparseTreeResult

variable {r : ℕ → ℕ} {b fuel : ℕ} {s : SparseState V}

/-- Construct a leaf tree when the current sparsification state is terminal. -/
def stop (r : ℕ → ℕ) (b : ℕ) (s : SparseState V) (fuel : ℕ)
    (h : SparseTerminal r s ∨ fuel = 0) : SparseTreeResult r b s fuel where
  tree := .leaf
  finish := fun _ => s
  path := fun _ => .nil
  terminal_or_exhausted := by
    intro _
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by simp only [SparsePath.length, h])
  stream_length := by intros; rfl
  stream_ones := by intros; rfl
  leaf_eval_imp := by intros _ _ h; exact h
  indicator_eq_sum := by
    intro x
    change indicator (s.eval x) = ∑ _ : Unit, indicator (s.eval x)
    exact (Fintype.sum_unique (fun _ : Unit => indicator (s.eval x))).symm
  disjoint := by intro p q hpq; exact (hpq (Subsingleton.elim (α := Unit) p q)).elim

/-- Join the two branch trees below a selected sunflower. -/
def join (c : SparseSelection r s) (hs : s.Valid b)
    (left : SparseTreeResult r b (c.branch false) fuel)
    (right : SparseTreeResult r b (c.branch true) fuel) :
    SparseTreeResult r b s (fuel + 1) where
  tree := .node (c.label hs) left.tree right.tree
  finish := Sum.elim left.finish right.finish
  path := fun p => match p with
    | .inl p => (left.path p).prepend (c.step false)
    | .inr p => (right.path p).prepend (c.step true)
  terminal_or_exhausted := by
    intro p
    cases p with
    | inl p =>
        rcases left.terminal_or_exhausted p with h | h
        · exact Or.inl h
        · exact Or.inr (by
            change ((left.path p).prepend (c.step false)).length = fuel + 1
            rw [SparsePath.length_prepend, h, Nat.add_comm])
    | inr p =>
        rcases right.terminal_or_exhausted p with h | h
        · exact Or.inl h
        · exact Or.inr (by
            change ((right.path p).prepend (c.step true)).length = fuel + 1
            rw [SparsePath.length_prepend, h, Nat.add_comm])
  stream_length := by
    intro p i
    cases p with
    | inl p =>
        by_cases hi : i = c.label hs
        · subst i
          simp [SparseDecisionTree.stream, SparsePath.processed_prepend,
            SparseSelection.step, SparseSelection.label, left.stream_length, Nat.add_comm]
        · have hiv : c.size ≠ i.val := by
            intro he
            exact hi (Fin.ext he.symm)
          simp [SparseDecisionTree.stream, hi, SparsePath.processed_prepend,
            SparseSelection.step, hiv, left.stream_length]
    | inr p =>
        by_cases hi : i = c.label hs
        · subst i
          simp [SparseDecisionTree.stream, SparsePath.processed_prepend,
            SparseSelection.step, SparseSelection.label, right.stream_length, Nat.add_comm]
        · have hiv : c.size ≠ i.val := by
            intro he
            exact hi (Fin.ext he.symm)
          simp [SparseDecisionTree.stream, hi, SparsePath.processed_prepend,
            SparseSelection.step, hiv, right.stream_length]
  stream_ones := by
    intro p i
    cases p with
    | inl p =>
        by_cases hi : i = c.label hs
        · subst i
          simp [SparseDecisionTree.stream, SparsePath.petalSteps_prepend,
            SparseSelection.step, SparseSelection.label, left.stream_ones]
        · have hiv : c.size ≠ i.val := by
            intro he
            exact hi (Fin.ext he.symm)
          simp [SparseDecisionTree.stream, hi, SparsePath.petalSteps_prepend,
            SparseSelection.step, hiv, left.stream_ones]
    | inr p =>
        by_cases hi : i = c.label hs
        · subst i
          simp [SparseDecisionTree.stream, SparsePath.petalSteps_prepend,
            SparseSelection.step, SparseSelection.label, right.stream_ones, Nat.add_comm]
        · have hiv : c.size ≠ i.val := by
            intro he
            exact hi (Fin.ext he.symm)
          simp [SparseDecisionTree.stream, hi, SparsePath.petalSteps_prepend,
            SparseSelection.step, hiv, right.stream_ones]
  leaf_eval_imp := by
    intro p x hp
    cases p with
    | inl p => exact c.branch_eval_imp false x (left.leaf_eval_imp p x hp)
    | inr p => exact c.branch_eval_imp true x (right.leaf_eval_imp p x hp)
  indicator_eq_sum := by
    intro x
    change indicator (s.eval x) =
      ∑ p : left.tree.Leaf ⊕ right.tree.Leaf,
        indicator ((Sum.elim left.finish right.finish p).eval x)
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← left.indicator_eq_sum x, ← right.indicator_eq_sum x]
    exact c.selected.branch_indicator x
  disjoint := by
    intro p q hpq x hpqx
    cases p with
    | inl p =>
        cases q with
        | inl q =>
            exact left.disjoint p q (fun h => hpq (congrArg Sum.inl h)) x hpqx
        | inr q =>
            exact c.selected.branch_disjoint x
              ⟨left.leaf_eval_imp p x hpqx.1, right.leaf_eval_imp q x hpqx.2⟩
    | inr p =>
        cases q with
        | inl q =>
            exact c.selected.branch_disjoint x
              ⟨left.leaf_eval_imp q x hpqx.2, right.leaf_eval_imp p x hpqx.1⟩
        | inr q =>
            exact right.disjoint p q (fun h => hpq (congrArg Sum.inr h)) x hpqx

/-- Build a sparsification tree recursively within the supplied fuel bound. -/
def build (r : ℕ → ℕ) (b : ℕ) :
    (fuel : ℕ) → (s : SparseState V) → s.Valid b → SparseTreeResult r b s fuel
  | 0, s, _ => stop r b s 0 (Or.inr rfl)
  | fuel + 1, s, hs => by
      classical
      exact if h : SparseEligible r s then
        let c := sparseSelect r s h
        join c hs
          (build r b fuel (c.branch false) (c.branch_valid hs false))
          (build r b fuel (c.branch true) (c.branch_valid hs true))
      else stop r b s (fuel + 1) (Or.inl (sparseTerminal_of_not_eligible h))

end SparseTreeResult

/-- A sufficient fuel bound for finite-width sparsification. -/
def sparseTreeFuel [Fintype V] (D : ℕ → ℕ) (b : ℕ) : ℕ :=
  (∑ u ∈ Finset.Ico 1 b, D u) * Fintype.card V

/-- The complete sparsification tree from an initial state. -/
def sparseTree [Fintype V] (r D : ℕ → ℕ) (b : ℕ) (s : SparseState V)
    (hs : s.Valid b) : SparseTreeResult r b s (sparseTreeFuel (V := V) D b) :=
  SparseTreeResult.build r b (sparseTreeFuel (V := V) D b) s hs

theorem sparseTree_terminal [Fintype V] {r e D : ℕ → ℕ} {b : ℕ}
    (hnum : SparseNumerics r e D b) (s : SparseState V) (hs : s.Valid b)
    (hadded : s.added = ∅) (p : (sparseTree r D b s hs).tree.Leaf) :
    SparseTerminal r ((sparseTree r D b s hs).finish p) := by
  classical
  let T := sparseTree r D b s hs
  rcases T.terminal_or_exhausted p with ht | hlen
  · exact ht
  · intro i hi
    let c := sparseSelect r (T.finish p) ⟨i, hi⟩
    have hbound := ((T.path p).snoc (c.step false)).length_budget hnum hs hadded
    change (T.path p).length + 1 ≤ sparseTreeFuel (V := V) D b at hbound
    rw [hlen] at hbound
    exact Nat.not_succ_le_self _ hbound

theorem sparseTree_stream_length [Fintype V] {r e D : ℕ → ℕ} {b : ℕ}
    (hnum : SparseNumerics r e D b) (s : SparseState V) (hs : s.Valid b)
    (hadded : s.added = ∅) (p : (sparseTree r D b s hs).tree.Leaf) (i : Fin (b + 1)) :
    ((sparseTree r D b s hs).tree.stream p i).length ≤
      (∑ u ∈ Finset.Ico 1 i.val, D u) * Fintype.card V := by
  rw [(sparseTree r D b s hs).stream_length]
  exact ((sparseTree r D b s hs).path p).processed_budget hnum hs hadded i.val
    (Nat.le_of_lt_succ i.isLt)

theorem sparseTree_stream_ones [Fintype V] {r e D : ℕ → ℕ} {b : ℕ}
    (hnum : SparseNumerics r e D b) (s : SparseState V) (hs : s.Valid b)
    (hadded : s.added = ∅) (p : (sparseTree r D b s hs).tree.Leaf) (i : Fin (b + 1)) :
    r i.val * ((sparseTree r D b s hs).tree.stream p i).count true ≤
      (∑ u ∈ Finset.Ico 1 i.val, D u) * Fintype.card V := by
  rw [(sparseTree r D b s hs).stream_ones]
  exact ((sparseTree r D b s hs).path p).petalSteps_budget hnum hs hadded i.val
    (Nat.le_of_lt_succ i.isLt)

end DepthThreeLowerBound

end

end Complexity
