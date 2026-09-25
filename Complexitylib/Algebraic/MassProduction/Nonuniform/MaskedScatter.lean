/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BatchOrCircuit

/-!
# Shared scatter from distinct active incidences

Fixed invalid slots contribute false through free wiring. Batched OR then
routes an active incidence's entire payload to its resource, provided no
other active incidence has the same key. Empty resources may receive false.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.MaskedScatter

/-- Invalid slots contribute zero without any charged masking gates. -/
def values (valid : Fin sources → Bool)
    (payload : Fin sources → Fin valueWidth → DeMorgan.Wiring inputs)
    (source : Fin sources) (bit : Fin valueWidth) : DeMorgan.Wiring inputs :=
  if valid source then payload source bit else .constant false

/-- An active source is the only way a masked payload bit can be true. -/
theorem values_eval_iff (valid : Fin sources → Bool)
    (payload : Fin sources → Fin valueWidth → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool) (source : Fin sources) (bit : Fin valueWidth) :
    (values valid payload source bit).eval input = true ↔
      valid source = true ∧ (payload source bit).eval input = true := by
  cases active : valid source <;> simp [values, active]

/-- A fixed shared scatter circuit routes every unique active source's
payload to its matching resource. The bound counts all sources and resources
once, regardless of how many payload bits are returned. -/
theorem existsCircuit
    (valid : Fin sources → Bool)
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (payload : Fin sources → Fin valueWidth → DeMorgan.Wiring inputs)
    (resourceKeys : Fin resources → Fin keyWidth → Bool) :
    ∃ scattered : Circuit DeMorgan.signature inputs (resources * valueWidth),
      scattered.cost DeMorgan.standardCost ≤ 256 * (sources + resources + 1) *
        (FiniteParameters.binaryDepth (sources + resources + 1) + keyWidth + valueWidth + 2) ^ 5 ∧
      ∀ (input : Fin inputs → Bool) (source : Fin sources) (resource : Fin resources),
        valid source = true →
        (fun bit => (sourceKeys source bit).eval input) = resourceKeys resource →
        (∀ other, valid other = true →
          (fun bit => (sourceKeys other bit).eval input) =
            (fun bit => (sourceKeys source bit).eval input) → other = source) →
        ∀ bit, scattered.eval DeMorgan.interpretation input (finProdFinEquiv (resource, bit)) =
          (payload source bit).eval input := by
  obtain ⟨scattered, correct, bound⟩ := BatchOr.existsCircuit sourceKeys (values valid payload)
    (fun resource bit => .constant (resourceKeys resource bit))
  refine ⟨scattered, bound, ?_⟩
  intro input source resource active matching unique bit
  apply Bool.eq_iff_iff.mpr
  rw [correct]
  constructor
  · rintro ⟨other, sameKey, valueTrue⟩
    obtain ⟨otherActive, otherValue⟩ := (values_eval_iff valid payload input other bit).mp valueTrue
    have equal : other = source := unique other otherActive (sameKey.trans matching.symm)
    simpa only [equal] using otherValue
  · intro sourceValue
    exact ⟨source, matching, (values_eval_iff valid payload input source bit).mpr ⟨active, sourceValue⟩⟩

end Algebraic.MassProduction.Nonuniform.MaskedScatter
