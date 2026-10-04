/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.BadSeeds.Internal

/-!
# Actual bad seeds from adaptive average discrepancy

An average-TV bound for every deterministic, seed-dependent choice of a
shift and tampered seeds implies the claimed bad-seed cardinality bound.
The counting theorem explicitly assumes that average bound; it does not
assert a correlation-breaker guarantee for an arbitrary supplied map.

This is the witness-selection and counting step in Chattopadhyay--Liao,
*Extractors for Sum of Two Sources* (2021), Lemma 5.3, printed pp.19--20:
<https://arxiv.org/pdf/2110.12652>.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual leaked output law preserves the normalization of its source. -/
theorem affineLeakageOutputWeight_probability {n d t : Nat} {Out : Type*} [Fintype Out]
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Out)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool)
    (b : Fin n → Bool) (y : Fin d → Bool) (ys : Fin t → Fin d → Bool)
    (probability : IsProbabilityWeight p) :
    IsProbabilityWeight (affineLeakageOutputWeight cb p leak advice b y ys) :=
  Internal.affineLeakageOutputWeight_probability cb p leak advice b y ys probability

/-- A bad honest seed has an actual shift and tampered tuple exceeding the strict threshold. -/
theorem mem_affineLeakageBadSeeds {n d t : Nat} {Out : Type*} [Fintype Out]
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Out)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool) (γ : ℝ) (y : Fin d → Bool) :
    y ∈ affineLeakageBadSeeds cb p leak advice γ ↔ ∃ b ys,
      γ < weightDist (affineLeakageOutputWeight cb p leak advice b y ys)
        (uniformSecondWeight (affineLeakageOutputWeight cb p leak advice b y ys)) :=
  Internal.mem_affineLeakageBadSeeds cb p leak advice γ y

/-- Outside the bad set, every actual shift and tampered tuple has discrepancy at most the threshold. -/
theorem not_mem_affineLeakageBadSeeds {n d t : Nat} {Out : Type*} [Fintype Out]
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Out)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool) (γ : ℝ) (y : Fin d → Bool) :
    y ∉ affineLeakageBadSeeds cb p leak advice γ ↔ ∀ b ys,
      weightDist (affineLeakageOutputWeight cb p leak advice b y ys)
        (uniformSecondWeight (affineLeakageOutputWeight cb p leak advice b y ys)) ≤ γ :=
  Internal.not_mem_affineLeakageBadSeeds cb p leak advice γ y

/-- All adaptive deterministic witness averages control the actual bad-seed cardinality. -/
theorem affineLeakageBadSeeds_card_le {n d t : Nat} {Out : Type*} [Fintype Out]
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Out)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool) {γ ε : ℝ} (positive : 0 < γ)
    (average : ∀ g : (Fin d → Bool) → Fin n → Bool,
      ∀ f : (Fin d → Bool) → Fin t → Fin d → Bool,
      (∑ y, uniformWeight (Fin d → Bool) y *
        weightDist (affineLeakageOutputWeight cb p leak advice (g y) y (f y))
          (uniformSecondWeight (affineLeakageOutputWeight cb p leak advice (g y) y (f y)))) ≤ ε) :
    ((affineLeakageBadSeeds cb p leak advice γ).card : ℝ) ≤
      (ε / γ) * Fintype.card (Fin d → Bool) :=
  Internal.affineLeakageBadSeeds_card_le cb p leak advice positive average

end Algebraic.Cutwidth.Extractor
