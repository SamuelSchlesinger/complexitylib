/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.AC0.Switching
public import Complexitylib.Circuits.AC0.Switching.Collection.Defs
public import Complexitylib.Circuits.AC0.Switching.Collection.Internal

/-!
# Simultaneous switching for finite formula collections

The exact finite union bound turns the width-sensitive switching theorem into
a simultaneous bound for any `Fin formulaCount`-indexed collection. These
collections are finite nonuniform objects; no generator or uniformity
assumption is involved.
-/

@[expose] public section

namespace Complexity

namespace DNF

/-- Simultaneous width-sensitive switching bound for a finite collection of
consistent DNFs. -/
theorem switchingAnyBad_width_encoding_bound
    (formulas : Fin formulaCount → DNF N)
    (hconsistent :
      ∀ index, (formulas index).Consistent)
    (width : ℕ)
    (hwidth :
      ∀ index, (formulas index).width ≤ width)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingAnyBad formulas queryCount) *
        q ^ queryCount ≤
      formulaCount *
        ((2 * q + 1) ^ N *
          (4 * (width + 1)) ^ queryCount) :=
  switchingAnyBad_width_encoding_bound_internal
    formulas hconsistent width hwidth q queryCount

/-- Simultaneous switching bound for arbitrary DNFs after semantics-preserving
cleanup, under a common original-width bound. -/
theorem switchingAnyBad_consistentParts_width_encoding_bound
    (formulas : Fin formulaCount → DNF N)
    (width : ℕ)
    (hwidth :
      ∀ index, (formulas index).width ≤ width)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingAnyBad (DNF.consistentParts formulas) queryCount) *
        q ^ queryCount ≤
      formulaCount *
        ((2 * q + 1) ^ N *
          (4 * (width + 1)) ^ queryCount) :=
  switchingAnyBad_consistentParts_width_encoding_bound_internal
    formulas width hwidth q queryCount

end DNF

namespace CNF

/-- Simultaneous width-sensitive switching bound for a finite collection of
consistent CNFs. -/
theorem switchingAnyBad_width_encoding_bound
    (formulas : Fin formulaCount → CNF N)
    (hconsistent :
      ∀ index, (formulas index).Consistent)
    (width : ℕ)
    (hwidth :
      ∀ index, (formulas index).width ≤ width)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingAnyBad formulas queryCount) *
        q ^ queryCount ≤
      formulaCount *
        ((2 * q + 1) ^ N *
          (4 * (width + 1)) ^ queryCount) :=
  switchingAnyBad_width_encoding_bound_internal
    formulas hconsistent width hwidth q queryCount

/-- Simultaneous switching bound for arbitrary CNFs after semantics-preserving
cleanup, under a common original-width bound. -/
theorem switchingAnyBad_consistentParts_width_encoding_bound
    (formulas : Fin formulaCount → CNF N)
    (width : ℕ)
    (hwidth :
      ∀ index, (formulas index).width ≤ width)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
          (switchingAnyBad (CNF.consistentParts formulas) queryCount) *
        q ^ queryCount ≤
      formulaCount *
        ((2 * q + 1) ^ N *
          (4 * (width + 1)) ^ queryCount) :=
  switchingAnyBad_consistentParts_width_encoding_bound_internal
    formulas width hwidth q queryCount

end CNF

end Complexity
