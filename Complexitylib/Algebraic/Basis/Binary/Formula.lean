/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Binary
public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Card

/-!
# Formulas over the full binary basis

A formula is a tree whose leaves are input variables or constants and whose
internal nodes apply one of the sixteen binary Boolean functions. Its size is
its number of variable leaves, the standard leaf-size measure; constants are
free, as they can be absorbed into the adjacent gate.

`leavesIn Y` counts the variable leaves whose index lies in a block `Y`. Over
pairwise disjoint blocks these counts add up to at most the total leaf count
(`sum_leavesIn_le_leaves`), and a formula with no leaf in `Y` does not depend
on the coordinates in `Y` (`eval_eq_of_leavesIn_eq_zero`). These are the two
facts Nechiporuk's argument uses.
-/

@[expose] public section

namespace Algebraic
namespace Binary

/-- A formula over the full binary basis. -/
inductive Formula (n : Nat)
  /-- An input variable. -/
  | var (index : Fin n)
  /-- A Boolean constant. -/
  | const (value : Bool)
  /-- A binary gate applied to two subformulas. -/
  | gate (op : Op) (left right : Formula n)

namespace Formula

variable {n : Nat}

/-- Evaluate a formula on an input. -/
def eval : Formula n → (Fin n → Bool) → Bool
  | var index, input => input index
  | const value, _ => value
  | gate op left right, input => op (left.eval input) (right.eval input)

@[simp] theorem eval_var (index : Fin n) (input : Fin n → Bool) :
    (var index).eval input = input index := rfl

@[simp] theorem eval_const (value : Bool) (input : Fin n → Bool) :
    (const value : Formula n).eval input = value := rfl

@[simp] theorem eval_gate (op : Op) (left right : Formula n) (input : Fin n → Bool) :
    (gate op left right).eval input = op (left.eval input) (right.eval input) := rfl

/-- The number of variable leaves: the leaf size of the formula. -/
def leaves : Formula n → Nat
  | var _ => 1
  | const _ => 0
  | gate _ left right => left.leaves + right.leaves

/-- The number of variable leaves whose index lies in `Y`. -/
def leavesIn (Y : Finset (Fin n)) : Formula n → Nat
  | var index => if index ∈ Y then 1 else 0
  | const _ => 0
  | gate _ left right => left.leavesIn Y + right.leavesIn Y

@[simp] theorem leavesIn_var (Y : Finset (Fin n)) (index : Fin n) :
    (var index).leavesIn Y = if index ∈ Y then 1 else 0 := rfl

@[simp] theorem leavesIn_const (Y : Finset (Fin n)) (value : Bool) :
    (const value : Formula n).leavesIn Y = 0 := rfl

@[simp] theorem leavesIn_gate (Y : Finset (Fin n)) (op : Op) (left right : Formula n) :
    (gate op left right).leavesIn Y = left.leavesIn Y + right.leavesIn Y := rfl

/-- A formula computes `f` when it agrees with `f` on every input. -/
def Computes (F : Formula n) (f : Cslib.BooleanFunction n) : Prop :=
  ∀ input, F.eval input = f input

theorem Computes.eval_eq {F : Formula n} {f : Cslib.BooleanFunction n} (h : F.Computes f) :
    F.eval = f :=
  funext h

theorem leavesIn_le_leaves (Y : Finset (Fin n)) : ∀ F : Formula n, F.leavesIn Y ≤ F.leaves
  | var index => by
    simp only [leavesIn, leaves]
    split_ifs <;> omega
  | const _ => le_rfl
  | gate _ left right =>
    Nat.add_le_add (leavesIn_le_leaves Y left) (leavesIn_le_leaves Y right)

/-- Over pairwise disjoint blocks, the block leaf counts add up to at most the
leaf size. -/
theorem sum_leavesIn_le_leaves {k : Nat} (Y : Fin k → Finset (Fin n))
    (disjoint : Pairwise fun i j => Disjoint (Y i) (Y j)) :
    ∀ F : Formula n, ∑ i, F.leavesIn (Y i) ≤ F.leaves
  | var index => by
    simp only [leavesIn, leaves]
    rw [Finset.sum_boole]
    apply Finset.card_le_one.mpr
    intro i hi j hj
    rw [Finset.mem_filter] at hi hj
    by_contra hne
    exact Finset.disjoint_left.mp (disjoint hne) hi.2 hj.2
  | const _ => by simp [leavesIn, leaves]
  | gate _ left right => by
    simp only [leavesIn, leaves, Finset.sum_add_distrib]
    exact Nat.add_le_add (sum_leavesIn_le_leaves Y disjoint left)
      (sum_leavesIn_le_leaves Y disjoint right)

/-- A formula without leaves in `Y` ignores the coordinates in `Y`. -/
theorem eval_eq_of_leavesIn_eq_zero {Y : Finset (Fin n)} {x x' : Fin n → Bool}
    (agree : ∀ i, i ∉ Y → x i = x' i) :
    ∀ F : Formula n, F.leavesIn Y = 0 → F.eval x = F.eval x'
  | var index, h => by
    have hmem : index ∉ Y := by
      intro hmem
      simp [leavesIn, hmem] at h
    exact agree index hmem
  | const _, _ => rfl
  | gate op left right, h => by
    simp only [leavesIn] at h
    simp only [eval]
    rw [eval_eq_of_leavesIn_eq_zero agree left (by omega),
      eval_eq_of_leavesIn_eq_zero agree right (by omega)]

end Formula

end Binary
end Algebraic
