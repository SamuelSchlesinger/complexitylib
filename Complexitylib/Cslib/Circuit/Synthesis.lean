/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Synthesis
import Mathlib.Algebra.BigOperators.Fin

/-!
# Reusing circuits in synthesis arguments

A concrete circuit supplies a synthesis bound for its designated outputs.
This connects circuit composition with constructions using shared wires.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {U : Type} {n m : ℕ} {I : Interpretation σ U}

/-- Rebuild the circuit's outputs within its existing gate budget. -/
theorem Circuit.synthesis (c : Circuit σ n m) :
    Synthesis I (inputs n) (Set.range fun j x => c.eval I x j) c.size := by
  have h := c.program.synthesis_of_steps (I := I) (fun _ => 1)
    (fun j => c.program.synthesis_step j)
  apply h.mono Set.Subset.rfl ?_ (by simp)
  rintro f ⟨j, rfl⟩
  exact ⟨c.outputs j, rfl⟩

/-- A circuit computing `f` supplies a synthesis bound for all coordinates of `f`. -/
theorem Circuit.Computes.synthesis {c : Circuit σ n m}
    {f : (Fin n → U) → Fin m → U} (hc : c.Computes I f) :
    Synthesis I (inputs n) (Set.range fun j x => f x j) c.size := by
  have equal : (fun j x => c.eval I x j) = (fun j x => f x j) := by
    funext j x
    exact congrFun (hc x) j
  rw [← equal]
  exact c.synthesis

end Cslib.Circuits
