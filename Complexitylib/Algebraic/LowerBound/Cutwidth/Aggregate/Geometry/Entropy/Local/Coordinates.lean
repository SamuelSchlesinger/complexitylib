/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Finite.Uniform
public import Mathlib.Data.Fin.VecNotation

/-!+# Coordinate witnesses for the local conjunction cases

Two incident edges use at most three coordinates, and a chord with two parent
edges uses at most four. These embeddings let finite truth-table certificates
apply to arbitrary finite Boolean cubes.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

/-- Reverse an edge while retaining the same Boolean conjunction. -/
def SignedEdge.reverse {V : Type*} (e : SignedEdge V) : SignedEdge V :=
  ⟨e.right, e.left, e.distinct.symm, e.rightSign, e.leftSign⟩

@[simp] theorem SignedEdge.eval_reverse {V : Type*} (e : SignedEdge V) :
    e.reverse.eval = e.eval := by
  funext x
  exact Bool.and_comm _ _

/-- Two distinct chosen coordinates. -/
def pairCoordinates {V : Type*} (a b : V) (hab : a ≠ b) : Fin 2 ↪ V where
  toFun := ![a, b]
  inj' := by
    intro i j same
    fin_cases i <;> fin_cases j <;> simp_all

/-- Three distinct chosen coordinates. -/
def tripleCoordinates {V : Type*} (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Fin 3 ↪ V where
  toFun := ![a, b, c]
  inj' := by
    intro i j same
    fin_cases i <;> fin_cases j <;> simp_all

/-- Four distinct chosen coordinates. -/
def quadCoordinates {V : Type*} (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Fin 4 ↪ V where
  toFun := ![a, b, c, d]
  inj' := by
    intro i j same
    fin_cases i <;> fin_cases j <;> simp_all

/-- A conditional certificate may ignore an additional right-hand parent. -/
noncomputable def ConditionalWeightBound.withRightParent {X Y Z W : Type*}
    [Fintype X] [Fintype Y] {key : X → Y} {parent : X → Z} {cost : ℝ}
    (bound : ConditionalWeightBound key parent cost) (extra : X → W) :
    ConditionalWeightBound key (fun x => (parent x, extra x)) cost where
  weight z := bound.weight z.1
  nonneg z := bound.nonneg z.1
  mass z := bound.mass z.1
  positive := bound.positive
  log_bound := bound.log_bound

/-- A conditional certificate may ignore an additional left-hand parent. -/
noncomputable def ConditionalWeightBound.withLeftParent {X Y Z W : Type*}
    [Fintype X] [Fintype Y] {key : X → Y} {parent : X → Z} {cost : ℝ}
    (bound : ConditionalWeightBound key parent cost) (extra : X → W) :
    ConditionalWeightBound key (fun x => (extra x, parent x)) cost where
  weight z := bound.weight z.2
  nonneg z := bound.nonneg z.2
  mass z := bound.mass z.2
  positive := bound.positive
  log_bound := bound.log_bound

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
