/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.CircuitNormalization

/-!
# Substitution of variables and constants into clauses and CNFs

Normalize substituted clauses and discard clauses that become identically true.
-/

@[expose] public section

namespace Complexity.DepthThreeLowerBound

namespace Clause

/-- Substitute inputs and normalize a clause; `none` denotes a tautology. -/
noncomputable def subst {V W : Type*} (α : V → Sum W Bool) (C : Clause V) : Option (Clause W) :=
  RawClause.normalize ((C.toList.map Sum.inl).map (GateInput.subst α))

end Clause

namespace CNF

/-- Substitute inputs into every clause and discard resulting tautologies. -/
noncomputable def subst {V W : Type*} (H : CNF V) (α : V → Sum W Bool) : CNF W :=
  H.filterMap (Clause.subst α)

end CNF

end Complexity.DepthThreeLowerBound
