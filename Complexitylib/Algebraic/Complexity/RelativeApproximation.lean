/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Complexity.Relative
public import Complexitylib.Algebraic.LowerBound.Approximation

/-!
# Approximation lower bounds relative to supplied functions

The approximation scheme starts with the supplied functions. Its existing
union-of-exceptions proof counts each shared gate once. Any uniform target
separation therefore bounds the minimum relative error cost.
-/

@[expose] public section

namespace Algebraic.Approximation.Scheme

/-- If every approximate value fails on at least `lower` samples, computing
the target from the initialized sources costs at least `lower` local errors. -/
theorem relativeCostComplexity_lowerBound
    [Fintype X] [DecidableEq X]
    {interpretation : Interpretation σ U} {approximation : Interpretation σ A}
    {decode : A → X → U} {sources : X → Fin n → U} {initial : Fin n → A}
    (scheme : Approximation.Scheme interpretation approximation decode sources initial)
    [DecidableRel scheme.relation]
    (target : X → U) (lower : Nat)
    (separated : ∀ value, lower ≤ (failures scheme.relation decode value target).card) :
    (lower : ℕ∞) ≤ Circuit.relativeCostComplexity interpretation scheme.errorCost
      (fun x (_ : Fin 1) => target x) sources := by
  apply Circuit.le_relativeCostComplexity
  intro circuit computes
  exact_mod_cast (separated (circuit.eval approximation initial 0)).trans
    (scheme.failures_card_le_cost circuit target (fun x => congrFun (computes x) 0))

/-- Construct the equality-based scheme directly from exact supplied
representatives and a bound on the number of local disagreements. -/
noncomputable def ofLocalErrors
    [Fintype X] [DecidableEq X] [DecidableEq U]
    (interpretation : Interpretation σ U) (approximation : Interpretation σ A)
    (decode : A → X → U) (sources : X → Fin n → U) (initial : Fin n → A)
    (errorCost : OperationCost σ)
    (inputExact : ∀ x i, sources x i = decode (initial i) x)
    (localErrors : ∀ op arguments,
      (Finset.univ.filter fun x =>
        interpretation op (fun i => decode (arguments i) x) ≠
          decode (approximation op arguments) x).card ≤ errorCost op) :
    Approximation.Scheme interpretation approximation decode sources initial where
  relation := Eq
  relation_trans := Eq.trans
  interpretation_preserves := by
    intro op exactArguments approxArguments agrees
    rw [funext agrees]
  errorCost := errorCost
  exceptions := fun op arguments => Finset.univ.filter fun x =>
    interpretation op (fun i => decode (arguments i) x) ≠
      decode (approximation op arguments) x
  input_correct := inputExact
  gate_correct := by
    intro op arguments x absent
    simpa using absent
  exceptions_card_le := localErrors

/-- The equality-based approximation bound stated directly in terms of
local disagreements and exact supplied representatives. -/
theorem relativeCostComplexity_lowerBound_of_localErrors
    [Fintype X] [DecidableEq X] [DecidableEq U]
    (interpretation : Interpretation σ U) (approximation : Interpretation σ A)
    (decode : A → X → U) (sources : X → Fin n → U) (initial : Fin n → A)
    (errorCost : OperationCost σ)
    (inputExact : ∀ x i, sources x i = decode (initial i) x)
    (localErrors : ∀ op arguments,
      (Finset.univ.filter fun x =>
        interpretation op (fun i => decode (arguments i) x) ≠
          decode (approximation op arguments) x).card ≤ errorCost op)
    (target : X → U) (lower : Nat)
    (separated : ∀ value,
      lower ≤ (Finset.univ.filter fun x => target x ≠ decode value x).card) :
    (lower : ℕ∞) ≤ Circuit.relativeCostComplexity interpretation errorCost
      (fun x (_ : Fin 1) => target x) sources := by
  classical
  exact (ofLocalErrors interpretation approximation decode sources initial
    errorCost inputExact localErrors).relativeCostComplexity_lowerBound target lower
      (by simpa only [ofLocalErrors, failures, ne_eq] using separated)

end Algebraic.Approximation.Scheme
