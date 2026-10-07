/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Substitution

/-!
# Semantic and width guarantees for CNF input substitution

These lemmas transport OpenAI's hard-slice correlation bounds to representations
of its full language. Constants and repeated target variables are both allowed.
-/

public section

namespace Complexity.DepthThreeLowerBound

/-- A substituted clause agrees with the original on the induced assignment. -/
theorem Clause.eval_subst {V W : Type*} (α : V → Sum W Bool) (C : Clause V) (x : Cube W) :
    ((C.subst α).map (fun D => D.eval x)).getD true = C.eval (GateInput.assignment α x) :=
  C.eval_subst_proof α x

/-- Substituting constants or identifying variables cannot increase clause width. -/
theorem Clause.width_subst_le {V W : Type*} (α : V → Sum W Bool) (C : Clause V)
    (D : Clause W) (h : C.subst α = some D) : D.width ≤ C.width :=
  C.width_subst_le_proof α D h

/-- A substituted CNF agrees with the original on the induced assignment. -/
theorem CNF.eval_subst {V W : Type*} (H : CNF V) (α : V → Sum W Bool) (x : Cube W) :
    (H.subst α).eval x = H.eval (GateInput.assignment α x) :=
  H.eval_subst_proof α x

/-- Input substitution preserves every clause-width bound. -/
theorem CNF.WidthAtMost.subst {V W : Type*} {H : CNF V} {k : ℕ}
    (h : H.WidthAtMost k) (α : V → Sum W Bool) : (H.subst α).WidthAtMost k :=
  h.subst_proof α

end Complexity.DepthThreeLowerBound
