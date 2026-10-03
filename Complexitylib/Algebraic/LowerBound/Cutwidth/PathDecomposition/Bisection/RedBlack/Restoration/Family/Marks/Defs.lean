/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Defs
public import Mathlib.Data.Finsupp.Weight

/-!
# Endpoint marks for isolated regions

Every edge of a region's black cut assigns one mark to its outside endpoint.
The finite map retains multiplicity when several boundary edges meet the
same vertex. A restoration family's endpoint marks sum these contributions
over its regions. For the shaded subfamily, apply this definition to
`F.restrict shaded`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack

open scoped Classical

/-- One mark on the outside endpoint of each boundary edge of `P`. -/
noncomputable def boundaryMarks {V : Type} [Fintype V] (B : SimpleGraph V)
    (P : Finset V) : V →₀ ℕ :=
  ∑ e ∈ B.cutFinset P, ∑ v ∈ e.toFinset \ P, Finsupp.single v 1

/-- Endpoint marks created by isolating all regions of the family. -/
noncomputable def RestorationFamily.endpointMarks {V E ι : Type} [Fintype V] [Fintype ι]
    {B : SimpleGraph V} {R : Multigraph V E} (F : RestorationFamily B R ι) : V →₀ ℕ :=
  ∑ i, boundaryMarks B (F.region i)

end Algebraic.Cutwidth.Bisection.RedBlack
