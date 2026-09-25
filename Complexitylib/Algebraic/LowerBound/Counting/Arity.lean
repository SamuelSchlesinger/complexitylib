/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Counting.Syntax
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Arity profiles for circuit counting

This file records the basis information used by closed-form counting bounds.
The exact counting theorems remain independent of these estimates.
-/

@[expose] public section

namespace Algebraic

/-- Every symbol in a signature has arity at most `r`. -/
def _root_.Cslib.Circuits.Signature.ArityAtMost (σ : Signature) (r : Nat) : Prop :=
  ∀ op, σ.Arity op ≤ r

export Cslib.Circuits (Signature.ArityAtMost)

/-- The finite signature has maximum arity exactly `r`. Packaging the upper
bound and an operation attaining it gives the closed Shannon theorem a natural
basis-level hypothesis. -/
structure _root_.Cslib.Circuits.Signature.HasMaximumArity (σ : Signature) (r : Nat) : Prop where
  /-- No primitive operation has arity greater than `r`. -/
  arity_le : σ.ArityAtMost r
  /-- Some primitive operation has arity `r`. -/
  attained : ∃ op, σ.Arity op = r

export Cslib.Circuits (Signature.HasMaximumArity)

/-- Arity-only upper bound for the number of lines. The successor on `w`
handles zero wires and nullary operations uniformly. -/
theorem _root_.Cslib.Circuits.Signature.lineCount_le_card_mul_pow
    (σ : Signature) [Fintype σ.Op]
    {r : Nat}
    (arity : σ.ArityAtMost r)
    (w : Nat) :
    σ.lineCount w ≤ Fintype.card σ.Op * (w + 1) ^ r := by
  unfold Signature.lineCount
  calc
    (∑ op : σ.Op, w ^ σ.Arity op) ≤
        ∑ _op : σ.Op, (w + 1) ^ r := by
      exact Finset.sum_le_sum fun op _ =>
        (Nat.pow_le_pow_left (Nat.le_succ w) _).trans
          (pow_le_pow_right' (by omega) (arity op))
    _ = Fintype.card σ.Op * (w + 1) ^ r := by simp

export Cslib.Circuits (Signature.lineCount_le_card_mul_pow)

/-- The number of available lines is monotone in the number of wires. -/
theorem _root_.Cslib.Circuits.Signature.lineCount_mono (σ : Signature) [Fintype σ.Op] :
    Monotone σ.lineCount := by
  intro left right bounded
  unfold Signature.lineCount
  exact Finset.sum_le_sum fun _ _ => Nat.pow_le_pow_left bounded _

export Cslib.Circuits (Signature.lineCount_mono)

/-- A signature with a positive maximum arity has at least as many possible
lines as available wires. -/
theorem _root_.Cslib.Circuits.Signature.HasMaximumArity.wires_le_lineCount
    {σ : Signature} [Fintype σ.Op]
    {r : Nat}
    (maximum : σ.HasMaximumArity r)
    (positive : 0 < r)
    (w : Nat) :
    w ≤ σ.lineCount w := by
  obtain ⟨op, hop⟩ := maximum.attained
  unfold Signature.lineCount
  calc
    w ≤ w ^ r := Nat.le_pow positive
    _ = w ^ σ.Arity op := by rw [hop]
    _ ≤ ∑ op : σ.Op, w ^ σ.Arity op := by
      exact Finset.single_le_sum
        (s := Finset.univ) (f := fun op : σ.Op => w ^ σ.Arity op)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ op)

export Cslib.Circuits (Signature.HasMaximumArity.wires_le_lineCount)

end Algebraic
