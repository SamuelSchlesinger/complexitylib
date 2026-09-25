/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Semantics
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Exact circuit syntax counts

This file equips lines, programs, and circuits over a finite signature with
finite enumerations and proves exact formulas for their cardinalities.
-/

@[expose] public section

namespace Algebraic

/-- A line is an operation symbol together with one wire for each argument. -/
def lineEquiv (σ : Signature) (n g : Nat) :
    Line σ n g ≃ Σ op : σ.Op, Fin (σ.Arity op) → Wire n g where
  toFun line := ⟨line.op, line.wires⟩
  invFun line := ⟨line.1, line.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instFintypeLine [Fintype σ.Op] : Fintype (Line σ n g) :=
  Fintype.ofEquiv (Σ op : σ.Op, Fin (σ.Arity op) → Wire n g)
    (lineEquiv σ n g).symm

/-- Exact number of possible lines with `n` inputs and `g` available gates. -/
theorem card_line [Fintype σ.Op] :
    Fintype.card (Line σ n g) =
      ∑ op : σ.Op, (n + g) ^ σ.Arity op := by
  rw [Fintype.card_congr (lineEquiv σ n g), Fintype.card_sigma]
  simp

/-- A zero-gate program carries no data. -/
def programZeroEquiv (σ : Signature) (n : Nat) : Program σ n 0 ≃ Unit where
  toFun _ := ()
  invFun _ := .empty
  left_inv program := by cases program; rfl
  right_inv value := by cases value; rfl

/-- A program with one additional gate is its prefix paired with its last line. -/
def programSuccEquiv (σ : Signature) (n g : Nat) :
    Program σ n (g + 1) ≃ Program σ n g × Line σ n g where
  toFun program := by cases program with | gate program line => exact (program, line)
  invFun pair := .gate pair.1 pair.2
  left_inv program := by cases program; rfl
  right_inv pair := by cases pair; rfl

/-- Recursive finite enumeration of straight-line programs. -/
@[instance_reducible]
noncomputable def _root_.Cslib.Circuits.Program.fintype [Fintype σ.Op] (n : Nat) :
    (g : Nat) → Fintype (Program σ n g)
  | 0 => Fintype.ofEquiv Unit (programZeroEquiv σ n).symm
  | g + 1 =>
      letI := Cslib.Circuits.Program.fintype (σ := σ) n g
      Fintype.ofEquiv (Program σ n g × Line σ n g)
        (programSuccEquiv σ n g).symm

export Cslib.Circuits (Program.fintype)

noncomputable instance instFintypeProgram [Fintype σ.Op] : Fintype (Program σ n g) :=
  Program.fintype n g

/-- Exact number of topologically ordered programs. -/
theorem card_program [Fintype σ.Op] :
    Fintype.card (Program σ n g) =
      ∏ j ∈ Finset.range g,
        ∑ op : σ.Op, (n + j) ^ σ.Arity op := by
  induction g with
  | zero =>
      rw [Fintype.card_congr (programZeroEquiv σ n)]
      simp
  | succ g ih =>
      rw [Fintype.card_congr (programSuccEquiv σ n g), Fintype.card_prod,
        ih, card_line]
      simp [Finset.prod_range_succ]

/-- A circuit is its program paired with its designated output wires. -/
def circuitEquiv (σ : Signature) (n g m : Nat) :
    Circuit σ n g m ≃ Program σ n g × (Fin m → Wire n g) where
  toFun circuit := (circuit.program, circuit.outputs)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instFintypeCircuit [Fintype σ.Op] : Fintype (Circuit σ n g m) :=
  Fintype.ofEquiv (Program σ n g × (Fin m → Wire n g))
    (circuitEquiv σ n g m).symm

/-- Exact number of circuits with `g` gates and `m` designated outputs. -/
theorem card_circuit [Fintype σ.Op] :
    Fintype.card (Circuit σ n g m) =
      (∏ j ∈ Finset.range g,
        ∑ op : σ.Op, (n + j) ^ σ.Arity op) *
      (n + g) ^ m := by
  rw [Fintype.card_congr (circuitEquiv σ n g m), Fintype.card_prod,
    card_program, Fintype.card_fun]
  simp

/-- Number of functions from `U^n` to `U^m`. -/
noncomputable def Target.count (U : Type*) (n m : Nat) : Nat :=
  Nat.card (Target U n m)

theorem Target.count_eq [Finite U] :
    Target.count U n m = Nat.card U ^ (m * Nat.card U ^ n) := by
  simp only [Target.count, Target, Nat.card_fun, Nat.card_fin]
  rw [← Nat.pow_mul]

/-- Exact number of functions from `U^n` to `U^m`. -/
theorem card_target [Finite U] :
    Nat.card (Target U n m) = Nat.card U ^ (m * Nat.card U ^ n) :=
  Target.count_eq

/-- Number of possible lines when `w` wires are available. -/
def _root_.Cslib.Circuits.Signature.lineCount (σ : Signature) [Fintype σ.Op] (w : Nat) : Nat :=
  ∑ op : σ.Op, w ^ σ.Arity op

export Cslib.Circuits (Signature.lineCount)

theorem card_line_eq_lineCount [Fintype σ.Op] :
    Fintype.card (Line σ n g) = σ.lineCount (n + g) :=
  card_line

end Algebraic
