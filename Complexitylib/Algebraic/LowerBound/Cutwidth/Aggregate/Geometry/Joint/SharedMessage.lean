/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.SharedMessage.Internal

/-!
# Refined message bound for original narrow and wide conjunctions

The actual whole-program message pays the support-graph cost for retained
original exact-two conjunctions, and the sharper one-eighth entropy cost for
conjunctions retaining at least three primary inputs.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

open Algebraic.Aggregate.Geometry Entropy
open scoped Classical

/-- The actual output message retains the separate narrow and wide information savings. -/
noncomputable def outputKeyRefinedWeightBound {n g : ℕ} (p : Program signature n g)
    (U : Finset (Fin n)) (out : Wire n g) :
    WeightBound (fun x : U → Bool => outputKey p U out (glue U x (fun _ => false)))
      (((g : ℝ) + 1) * Real.log 2 -
        (retainedTwo p U).card * (Real.binEntropy (1 / 4) - 1 / 2 * Real.log 2) -
        (retainedWide p U).card * (Real.log 2 - Real.binEntropy (1 / 8)) +
        U.card * (Real.binEntropy (1 / 4) - 3 / 4 * Real.log 2)) := by
  apply outputKeyWeightBoundOfClasses p U out (retainedTwo p U) (retainedWide p U)
    (disjoint_retained p U)
  · intro i hi
    exact ((Finset.mem_filter.mp hi).2).selectedPair
  · intro i hi
    exact (Finset.mem_filter.mp hi).2.2

end Algebraic.Cutwidth.Aggregate.Geometry.Joint
