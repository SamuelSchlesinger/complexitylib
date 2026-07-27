/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Data.Finset.Union

/-!
# Boolean formulas and formula size

Boolean formulas as *trees* over `∧`, `∨`, `¬`, variables, and constants, with a
tree `size` (total node count) and `leaves` count (roadmap track L4). Formula
size is deliberately kept **separate** from DAG circuit size: a formula counts
every occurrence of a subformula, whereas a DAG-shaped `Circuit` may share a
subcircuit among several parents. Consequently formula size can be
exponentially larger than the size of an equivalent circuit, and the two
measures must not be conflated in lower-bound arguments.

## Main definitions and results

- `BoolFormula` — the tree syntax, `BoolFormula.eval` its semantics
- `BoolFormula.size`, `BoolFormula.leaves`, `BoolFormula.depth` — tree-size,
  leaf-count, and depth measures
- `BoolFormula.leaves_le_size`, `BoolFormula.one_le_size`,
  `BoolFormula.leaves_le_two_pow_depth`,
  `BoolFormula.size_lt_two_pow_depth_succ`, `BoolFormula.depth_le_size`
- `BoolFormula.vars`, `BoolFormula.eval_eq_of_agree` — the variable set and the
  locality property (evaluation depends only on the variables that occur)
-/

@[expose] public section

namespace Complexity

/-- A Boolean formula: a *tree* over variables, the constants `⊤`/`⊥`, and the
    connectives `¬`, `∧`, `∨`. Unlike a `Circuit`, subformulas are not shared. -/
inductive BoolFormula where
  /-- The variable `x_i`. -/
  | var (i : ℕ)
  /-- The constant `⊤`. -/
  | tru
  /-- The constant `⊥`. -/
  | fls
  /-- Negation. -/
  | neg (φ : BoolFormula)
  /-- Conjunction. -/
  | conj (φ ψ : BoolFormula)
  /-- Disjunction. -/
  | disj (φ ψ : BoolFormula)
  deriving Repr, DecidableEq

namespace BoolFormula

/-- Evaluate a formula under an assignment `α : ℕ → Bool`. -/
def eval (α : ℕ → Bool) : BoolFormula → Bool
  | var i => α i
  | tru => true
  | fls => false
  | neg φ => !(eval α φ)
  | conj φ ψ => eval α φ && eval α ψ
  | disj φ ψ => eval α φ || eval α ψ

/-- The **tree size**: the total number of nodes (leaves and connectives). -/
def size : BoolFormula → ℕ
  | var _ => 1
  | tru => 1
  | fls => 1
  | neg φ => size φ + 1
  | conj φ ψ => size φ + size ψ + 1
  | disj φ ψ => size φ + size ψ + 1

/-- The number of leaf nodes (variables and constants). -/
def leaves : BoolFormula → ℕ
  | var _ => 1
  | tru => 1
  | fls => 1
  | neg φ => leaves φ
  | conj φ ψ => leaves φ + leaves ψ
  | disj φ ψ => leaves φ + leaves ψ

/-- The **depth** of a formula: the longest root-to-leaf path (the `NC¹`
    complexity measure). Leaves have depth `0`; each connective adds `1`. -/
def depth : BoolFormula → ℕ
  | var _ => 0
  | tru => 0
  | fls => 0
  | neg φ => depth φ + 1
  | conj φ ψ => max (depth φ) (depth ψ) + 1
  | disj φ ψ => max (depth φ) (depth ψ) + 1

/-- The set of variables occurring in a formula. -/
def vars : BoolFormula → Finset ℕ
  | var i => {i}
  | tru => ∅
  | fls => ∅
  | neg φ => vars φ
  | conj φ ψ => vars φ ∪ vars ψ
  | disj φ ψ => vars φ ∪ vars ψ

/-- Every formula has at least one node. -/
theorem one_le_size (φ : BoolFormula) : 1 ≤ size φ := by
  cases φ <;> simp only [size] <;> omega

/-- The leaf count never exceeds the tree size (leaves are among the nodes). -/
theorem leaves_le_size (φ : BoolFormula) : leaves φ ≤ size φ := by
  induction φ with
  | var i => simp [leaves, size]
  | tru => simp [leaves, size]
  | fls => simp [leaves, size]
  | neg φ ih => simp only [leaves, size]; omega
  | conj φ ψ ihφ ihψ => simp only [leaves, size]; omega
  | disj φ ψ ihφ ihψ => simp only [leaves, size]; omega

/-- A formula of depth `d` has at most `2 ^ d` leaves (a depth-`d` binary tree has
    at most `2 ^ d` leaves). -/
theorem leaves_le_two_pow_depth (φ : BoolFormula) : leaves φ ≤ 2 ^ depth φ := by
  induction φ with
  | var i => simp [leaves, depth]
  | tru => simp [leaves, depth]
  | fls => simp [leaves, depth]
  | neg φ ih => simp only [leaves, depth, Nat.pow_succ, Nat.mul_two]; omega
  | conj φ ψ ihφ ihψ =>
    have h0 : (2 : ℕ) ^ depth φ ≤ 2 ^ max (depth φ) (depth ψ) :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have h1 : (2 : ℕ) ^ depth ψ ≤ 2 ^ max (depth φ) (depth ψ) :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    simp only [leaves, depth, Nat.pow_succ, Nat.mul_two]; omega
  | disj φ ψ ihφ ihψ =>
    have h0 : (2 : ℕ) ^ depth φ ≤ 2 ^ max (depth φ) (depth ψ) :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have h1 : (2 : ℕ) ^ depth ψ ≤ 2 ^ max (depth φ) (depth ψ) :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    simp only [leaves, depth, Nat.pow_succ, Nat.mul_two]; omega

/-- A formula of depth `d` has fewer than `2 ^ (d + 1)` total nodes. This is
the tree-size counterpart of `leaves_le_two_pow_depth`. -/
theorem size_lt_two_pow_depth_succ (φ : BoolFormula) :
    size φ < 2 ^ (depth φ + 1) := by
  induction φ with
  | var i => simp [size, depth]
  | tru => simp [size, depth]
  | fls => simp [size, depth]
  | neg φ ih =>
    have hpos : 0 < (2 : ℕ) ^ (depth φ + 1) := Nat.two_pow_pos _
    simp only [size, depth]
    rw [show depth φ + 1 + 1 = (depth φ + 1) + 1 by omega,
      Nat.pow_succ, Nat.mul_two]
    omega
  | conj φ ψ ihφ ihψ =>
    have hφ :
        (2 : ℕ) ^ (depth φ + 1) ≤
          2 ^ (max (depth φ) (depth ψ) + 1) :=
      Nat.pow_le_pow_right (by omega)
        (Nat.add_le_add_right (le_max_left _ _) 1)
    have hψ :
        (2 : ℕ) ^ (depth ψ + 1) ≤
          2 ^ (max (depth φ) (depth ψ) + 1) :=
      Nat.pow_le_pow_right (by omega)
        (Nat.add_le_add_right (le_max_right _ _) 1)
    have hpos :
        0 < (2 : ℕ) ^ (max (depth φ) (depth ψ) + 1) :=
      Nat.two_pow_pos _
    simp only [size, depth]
    rw [show max (depth φ) (depth ψ) + 1 + 1 =
        (max (depth φ) (depth ψ) + 1) + 1 by omega,
      Nat.pow_succ, Nat.mul_two]
    omega
  | disj φ ψ ihφ ihψ =>
    have hφ :
        (2 : ℕ) ^ (depth φ + 1) ≤
          2 ^ (max (depth φ) (depth ψ) + 1) :=
      Nat.pow_le_pow_right (by omega)
        (Nat.add_le_add_right (le_max_left _ _) 1)
    have hψ :
        (2 : ℕ) ^ (depth ψ + 1) ≤
          2 ^ (max (depth φ) (depth ψ) + 1) :=
      Nat.pow_le_pow_right (by omega)
        (Nat.add_le_add_right (le_max_right _ _) 1)
    have hpos :
        0 < (2 : ℕ) ^ (max (depth φ) (depth ψ) + 1) :=
      Nat.two_pow_pos _
    simp only [size, depth]
    rw [show max (depth φ) (depth ψ) + 1 + 1 =
        (max (depth φ) (depth ψ) + 1) + 1 by omega,
      Nat.pow_succ, Nat.mul_two]
    omega

/-- Depth never exceeds size: a longest path uses at most every node. -/
theorem depth_le_size (φ : BoolFormula) : depth φ ≤ size φ := by
  induction φ with
  | var i => simp [depth, size]
  | tru => simp [depth, size]
  | fls => simp [depth, size]
  | neg φ ih => simp only [depth, size]; omega
  | conj φ ψ ihφ ihψ => simp only [depth, size]; omega
  | disj φ ψ ihφ ihψ => simp only [depth, size]; omega

/-- **Locality.** A formula's value depends only on the variables that occur in
    it: if two assignments agree on `vars φ`, they give `φ` the same value. -/
theorem eval_eq_of_agree : ∀ (φ : BoolFormula) {α β : ℕ → Bool},
    (∀ i ∈ vars φ, α i = β i) → eval α φ = eval β φ := by
  intro φ
  induction φ with
  | var i => intro α β h; exact h i (Finset.mem_singleton_self i)
  | tru => intro α β _; rfl
  | fls => intro α β _; rfl
  | neg φ ih => intro α β h; simp only [eval, ih h]
  | conj φ ψ ihφ ihψ =>
    intro α β h
    have hφ : ∀ i ∈ vars φ, α i = β i := fun i hi => h i (Finset.mem_union_left _ hi)
    have hψ : ∀ i ∈ vars ψ, α i = β i := fun i hi => h i (Finset.mem_union_right _ hi)
    simp only [eval, ihφ hφ, ihψ hψ]
  | disj φ ψ ihφ ihψ =>
    intro α β h
    have hφ : ∀ i ∈ vars φ, α i = β i := fun i hi => h i (Finset.mem_union_left _ hi)
    have hψ : ∀ i ∈ vars ψ, α i = β i := fun i hi => h i (Finset.mem_union_right _ hi)
    simp only [eval, ihφ hφ, ihψ hψ]

/-- A formula with no variables evaluates to a constant: its value is
    assignment-independent (a corollary of locality). -/
theorem eval_const_of_vars_empty {φ : BoolFormula} (hv : vars φ = ∅) (α β : ℕ → Bool) :
    eval α φ = eval β φ := by
  apply eval_eq_of_agree
  intro i hi
  rw [hv] at hi
  simp at hi

end BoolFormula

end Complexity
