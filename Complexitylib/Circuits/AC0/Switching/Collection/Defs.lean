/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.AC0.Switching.Defs

/-!
# Simultaneous switching for finite formula collections -- definitions

These are finite, nonuniform collections indexed by `Fin formulaCount`; they
are unrelated to uniform circuit-family generators.
-/

@[expose] public section

namespace Complexity

namespace DNF

/-- At least one DNF in a finite collection has a deep switching tree. -/
noncomputable def switchingAnyBad
    (formulas : Fin formulaCount → DNF N)
    (queryCount : ℕ) (restriction : Restriction.On N) : Prop :=
  ∃ index,
    switchingBad (formulas index) queryCount restriction

noncomputable instance switchingAnyBadDecidable
    (formulas : Fin formulaCount → DNF N)
    (queryCount : ℕ) :
    DecidablePred (switchingAnyBad formulas queryCount) :=
  fun restriction => by
    unfold switchingAnyBad
    infer_instance

/-- Clean every DNF in a finite collection. -/
noncomputable def consistentParts
    (formulas : Fin formulaCount → DNF N) :
    Fin formulaCount → DNF N :=
  fun index => (formulas index).consistentPart

end DNF

namespace CNF

/-- At least one CNF in a finite collection has a deep switching tree. -/
noncomputable def switchingAnyBad
    (formulas : Fin formulaCount → CNF N)
    (queryCount : ℕ) (restriction : Restriction.On N) : Prop :=
  ∃ index,
    switchingBad (formulas index) queryCount restriction

noncomputable instance switchingAnyBadDecidable
    (formulas : Fin formulaCount → CNF N)
    (queryCount : ℕ) :
    DecidablePred (switchingAnyBad formulas queryCount) :=
  fun restriction => by
    unfold switchingAnyBad
    infer_instance

/-- Clean every CNF in a finite collection. -/
noncomputable def consistentParts
    (formulas : Fin formulaCount → CNF N) :
    Fin formulaCount → CNF N :=
  fun index => (formulas index).consistentPart

end CNF

end Complexity
