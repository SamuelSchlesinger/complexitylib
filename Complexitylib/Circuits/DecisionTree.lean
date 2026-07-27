/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Data.Finset.Card
public import Complexitylib.Circuits.Formula
import Std.Tactic.BVDecide.Normalize.Bool

/-!
# Boolean decision trees

Decision trees over Boolean variables, with evaluation, depth, and leaf-count
measures (roadmap track L4). A decision tree queries one variable per internal
node and branches on its value; leaves carry the output bit. Decision trees are
the combinatorial substrate for restrictions and switching-lemma arguments, and
are distinct from the DAG-shaped `Circuit`.

## Main definitions and results

- `DecisionTree` — the tree syntax
- `DecisionTree.eval` — evaluation under an assignment
- `DecisionTree.depth`, `DecisionTree.numLeaves` — the query-depth and leaf-count
  measures
- `DecisionTree.numLeaves_le_two_pow_depth` — a depth-`d` tree has at most `2 ^ d`
  leaves
- `DecisionTree.vars`, `DecisionTree.eval_eq_of_agree` — the queried-variable set
  and the locality property: a tree's output depends only on the variables it
  queries (a decision tree is a junta on `vars`)
- `DecisionTree.toFormula`, `DecisionTree.toFormula_eval` — compilation to an
  equivalent Boolean formula (the decision-tree ⟹ formula direction)
-/

@[expose] public section

namespace Complexity

/-- A Boolean decision tree: a `leaf` carries an output bit; a `node i t₀ t₁`
    queries variable `i` and continues into `t₀` if it is `false`, `t₁` if
    `true`. -/
inductive DecisionTree where
  /-- A leaf carrying output bit `b`. -/
  | leaf (b : Bool)
  /-- Query variable `i`; branch to `t₀` on `false`, `t₁` on `true`. -/
  | node (i : ℕ) (t₀ t₁ : DecisionTree)
  deriving Repr, DecidableEq

namespace DecisionTree

/-- Evaluate a decision tree under an assignment `α : ℕ → Bool`. -/
def eval (α : ℕ → Bool) : DecisionTree → Bool
  | leaf b => b
  | node i t₀ t₁ => if α i then eval α t₁ else eval α t₀

/-- The query depth of a decision tree (the longest root-to-leaf path). -/
def depth : DecisionTree → ℕ
  | leaf _ => 0
  | node _ t₀ t₁ => max (depth t₀) (depth t₁) + 1

/-- The number of leaves of a decision tree. -/
def numLeaves : DecisionTree → ℕ
  | leaf _ => 1
  | node _ t₀ t₁ => numLeaves t₀ + numLeaves t₁

/-- The set of variables a decision tree queries. -/
def vars : DecisionTree → Finset ℕ
  | leaf _ => ∅
  | node i t₀ t₁ => insert i (vars t₀ ∪ vars t₁)

@[simp] theorem eval_leaf (α : ℕ → Bool) (b : Bool) : eval α (leaf b) = b := rfl

@[simp] theorem eval_node (α : ℕ → Bool) (i : ℕ) (t₀ t₁ : DecisionTree) :
    eval α (node i t₀ t₁) = if α i then eval α t₁ else eval α t₀ := rfl

@[simp] theorem depth_leaf (b : Bool) : depth (leaf b) = 0 := rfl

@[simp] theorem numLeaves_leaf (b : Bool) : numLeaves (leaf b) = 1 := rfl

/-- Every decision tree has at least one leaf. -/
theorem one_le_numLeaves (t : DecisionTree) : 1 ≤ numLeaves t := by
  induction t with
  | leaf b => simp [numLeaves]
  | node i t₀ t₁ ih₀ ih₁ => simp only [numLeaves]; omega

/-- **Locality (junta property).** A decision tree's output depends only on the
    variables it queries: if two assignments agree on `vars t`, they yield the same
    value. -/
theorem eval_eq_of_agree : ∀ (t : DecisionTree) {α β : ℕ → Bool},
    (∀ i ∈ vars t, α i = β i) → eval α t = eval β t := by
  intro t
  induction t with
  | leaf b => intro α β _; rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    intro α β h
    have hi : α i = β i := h i (Finset.mem_insert_self _ _)
    have h₀ : ∀ j ∈ vars t₀, α j = β j :=
      fun j hj => h j (Finset.mem_insert_of_mem (Finset.mem_union_left _ hj))
    have h₁ : ∀ j ∈ vars t₁, α j = β j :=
      fun j hj => h j (Finset.mem_insert_of_mem (Finset.mem_union_right _ hj))
    simp only [eval, hi, ih₀ h₀, ih₁ h₁]

/-- A depth-`d` decision tree queries fewer than `2 ^ d` distinct variables
    (`|vars t| < 2 ^ depth t`), the branching-count bound behind decision-tree
    complexity. -/
theorem card_vars_lt_two_pow_depth (t : DecisionTree) : (vars t).card < 2 ^ depth t := by
  induction t with
  | leaf b => simp [vars, depth]
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [vars, depth]
    have hins := Finset.card_insert_le i (vars t₀ ∪ vars t₁)
    have huni := Finset.card_union_le (vars t₀) (vars t₁)
    have h0 : (2 : ℕ) ^ depth t₀ ≤ 2 ^ max (depth t₀) (depth t₁) :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have h1 : (2 : ℕ) ^ depth t₁ ≤ 2 ^ max (depth t₀) (depth t₁) :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    rw [Nat.pow_succ, Nat.mul_two]
    omega

/-- A decision tree of depth `d` has at most `2 ^ d` leaves. -/
theorem numLeaves_le_two_pow_depth (t : DecisionTree) : numLeaves t ≤ 2 ^ depth t := by
  induction t with
  | leaf b => simp
  | node i t₀ t₁ ih₀ ih₁ =>
    have h₀ : numLeaves t₀ ≤ 2 ^ max (depth t₀) (depth t₁) :=
      le_trans ih₀ (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
    have h₁ : numLeaves t₁ ≤ 2 ^ max (depth t₀) (depth t₁) :=
      le_trans ih₁ (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
    simp only [numLeaves, depth, Nat.pow_succ, Nat.mul_two]
    omega

/-- Compile a decision tree into an equivalent Boolean formula: a leaf becomes a
    constant, and a query node `node i t₀ t₁` becomes
    `(x_i ∧ ⟦t₁⟧) ∨ (¬x_i ∧ ⟦t₀⟧)`. -/
def toFormula : DecisionTree → BoolFormula
  | leaf b => if b then BoolFormula.tru else BoolFormula.fls
  | node i t₀ t₁ =>
      BoolFormula.disj (BoolFormula.conj (BoolFormula.var i) (toFormula t₁))
        (BoolFormula.conj (BoolFormula.neg (BoolFormula.var i)) (toFormula t₀))

/-- **The compiled formula computes the same function as the tree.** -/
theorem toFormula_eval (α : ℕ → Bool) (t : DecisionTree) :
    BoolFormula.eval α (toFormula t) = eval α t := by
  induction t with
  | leaf b => cases b <;> rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [toFormula, BoolFormula.eval, eval, ih₀, ih₁]
    cases α i <;> simp

/-- The compiled formula has depth at most `2 · depth t + 1`: each query node
    expands to a two-level `∨`-of-`∧` gadget, and the negated literal adds one
    further level. -/
theorem toFormula_depth_le (t : DecisionTree) : (toFormula t).depth ≤ 2 * t.depth + 1 := by
  induction t with
  | leaf b => cases b <;> simp [toFormula, BoolFormula.depth, depth]
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [toFormula, BoolFormula.depth, depth]
    omega

end DecisionTree

end Complexity
