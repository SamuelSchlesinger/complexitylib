/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.AndOr.Preimage
public import Complexitylib.Algebraic.LowerBound.Fusion.Comap
public import Complexitylib.Algebraic.LowerBound.Fusion.Neq

/-!
# Inequality lower bounds from preimages

If pulling a set problem back along a map gives the inequality problem, every
AND/OR circuit constructing the original problem also constructs inequality
after applying the preimage homomorphism.  The existing inequality lower bound
therefore applies without changing the circuit or its AND cost.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Neq

private theorem and_lowerBound_of_problem_eq
    {source : SetProblem (Ground (2 ^ n))}
    (same : source = problem (2 ^ n))
    (circuit : Circuit AndOr.signature source.inputCount 1)
    (constructs : source.Constructs circuit
      (AndOr.setInterpretation (Ground (2 ^ n)))) :
    n ≤ circuit.cost AndOr.andCost := by
  subst source
  exact and_lowerBound circuit constructs

/-- If the preimage of a set problem is the `2 ^ n`-vertex inequality
problem, every circuit constructing the source problem uses at least `n` AND
gates, even when OR gates are free. -/
theorem and_lowerBound_of_preimage
    {Γ : Type u}
    {source : SetProblem Γ}
    (f : Ground (2 ^ n) → Γ)
    (image :
      source.map (AndOr.preimageHomomorphism f).map =
        problem (2 ^ n))
    (circuit : Circuit AndOr.signature source.inputCount 1)
    (constructs : source.Constructs circuit
      (AndOr.setInterpretation Γ)) :
    n ≤ circuit.cost AndOr.andCost := by
  exact and_lowerBound_of_problem_eq image circuit
    (constructs.map (AndOr.preimageHomomorphism f))

end Neq
end Fusion
end Algebraic
