/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Message

/-!
# Retained original conjunction classes

Exact-two gates keep their original two primary inputs in the selected cut.
Wider gates retain at least three primary inputs. These classes are disjoint,
and the definitions refer to actual lines and their literal-set messages.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

open Algebraic.Aggregate.Geometry

/-- An original exact-two conjunction retains both primary inputs in the cut. -/
def RetainedTwo {n g : ℕ} (line : Line signature n g) (U : Finset (Fin n)) : Prop :=
  line.op.isConjunction = true ∧ (primaryInputs line).card = 2 ∧ primaryInputs line ⊆ U

/-- A conjunction retains at least three distinct primary inputs in the cut. -/
def RetainedWide {n g : ℕ} (line : Line signature n g) (U : Finset (Fin n)) : Prop :=
  line.op.isConjunction = true ∧ 3 ≤ (literalVars (lineLiterals line U)).card

/-- Actual original exact-two gates retained by the selected cut. -/
noncomputable def retainedTwo {n g : ℕ} (p : Program signature n g)
    (U : Finset (Fin n)) : Finset (Fin g) := by
  classical
  exact Finset.univ.filter fun i => RetainedTwo (p.lines i) U

/-- Actual gates retaining at least three primary inputs in the selected cut. -/
noncomputable def retainedWide {n g : ℕ} (p : Program signature n g)
    (U : Finset (Fin n)) : Finset (Fin g) := by
  classical
  exact Finset.univ.filter fun i => RetainedWide (p.lines i) U

end Algebraic.Cutwidth.Aggregate.Geometry.Joint
