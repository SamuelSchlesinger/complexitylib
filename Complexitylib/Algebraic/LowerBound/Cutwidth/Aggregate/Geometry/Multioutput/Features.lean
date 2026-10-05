/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.Features.Internal

/-!
# Explicit affine-plus-conjunction representations of circuit outputs

Every output coordinate is an affine function of the primary bits plus a linear
combination of actual conjunction gate outputs. This representation allows arbitrary
arity, depth, and nonlinear reuse, including signed and constant gates.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

/-- Every output coordinate has an affine-plus-conjunction-feature representation,
using actual conjunction outputs without changing their Boolean polarity. -/
theorem output_affine_conjunction_representation {n m : ℕ} (c : Circuit signature n m)
    (j : Fin m) :
    ∃ (b : ZMod 2) (L : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
      (w : {i : Fin c.size // (c.program.lines i).op.isConjunction = true} → ZMod 2),
      ∀ x, bitValue (c.eval interpretation x j) = b + L (bitVector x) +
        ∑ i, w i * bitValue (c.program.gateFunction interpretation i x) := by
  obtain ⟨f, ⟨b, L, rfl⟩, g, ⟨w, rfl⟩, h⟩ :=
    Submodule.mem_sup.mp (output_mem_affine_sup_conjunctionRange c j)
  refine ⟨b, L, w, fun x => ?_⟩
  simpa only [Pi.add_apply, Fintype.linearCombination_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] using (congrFun h x).symm

end Algebraic.Aggregate.Geometry
