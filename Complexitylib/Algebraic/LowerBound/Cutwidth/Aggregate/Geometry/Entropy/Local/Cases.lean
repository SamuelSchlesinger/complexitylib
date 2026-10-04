/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local.Cases.Internal

/-!
# Exact conditional tables on at most four Boolean variables

Every local graph configuration is one of a seed, an extension, a parallel edge,
a triangle, or a path on four vertices. Finite enumeration checks the signed
Boolean tables; exact logarithmic inequalities certify their coding costs.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

/-- A signed two-variable conjunction costs exactly the quarter binary entropy. -/
noncomputable def pairSeed (a b : Bool) :
    WeightBound (pairBit (0 : Fin 2) 1 a b) (Real.binEntropy (1 / 4)) := by
  let cert := tableConditionalBound (pairBit (0 : Fin 2) 1 a b) (fun _ => ())
  exact ⟨cert.weight (), cert.nonneg (), cert.mass (), cert.positive,
    by simpa only [LocalCases.seed_cost] using cert.log_bound⟩


/-- One previously used endpoint gives a three-quarter-bit conditional cost. -/
noncomputable def pairExtension (a b c d : Bool) :
    ConditionalWeightBound (pairBit (0 : Fin 3) 1 a b) (pairBit 0 2 c d)
      ((3 / 4) * Real.log 2) := by
  exact (tableConditionalBound _ _).mono (by exact LocalCases.extension_cost a b c d)


/-- A repeated support obeys the remaining-edge charge. -/
noncomputable def pairParallel (a b c d : Bool) :
    ConditionalWeightBound (pairBit (0 : Fin 2) 1 a b) (pairBit 0 1 c d)
      ((3 / 2) * Real.log 2 - Real.binEntropy (1 / 4)) := by
  exact (tableConditionalBound _ _).mono (by exact LocalCases.parallel_cost a b c d)


/-- A triangle obeys the remaining-edge charge for every choice of literal signs. -/
noncomputable def pairTriangle (a b c d e f : Bool) :
    ConditionalWeightBound (pairBit (0 : Fin 3) 1 a b)
      (fun x => (pairBit 0 2 c d x, pairBit 1 2 e f x))
        ((3 / 2) * Real.log 2 - Real.binEntropy (1 / 4)) := by
  exact (tableConditionalBound _ _).mono (by exact LocalCases.triangle_cost a b c d e f)


/-- Two neighbors on four vertices obey the remaining-edge charge. -/
noncomputable def pairDisjoint (a b c d e f : Bool) :
    ConditionalWeightBound (pairBit (0 : Fin 4) 1 a b)
      (fun x => (pairBit 0 2 c d x, pairBit 1 3 e f x))
        ((3 / 2) * Real.log 2 - Real.binEntropy (1 / 4)) := by
  exact (tableConditionalBound _ _).mono (by exact LocalCases.disjoint_cost a b c d e f)

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
