/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Reduction.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Reduction.Internal

/-!
# Parity bias of the actual XOR source reduction

Every product of outer-coordinate signs has exactly the absolute bias of
the product of its component-call signs. This identifies the quantity used
by the fourth-moment majority argument with the affine correlation-breaker
quantity in Chattopadhyay--Liao, Lemma 5.4, equation (5).
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Taking XORs within coordinates preserves the absolute bias of the full component parity. -/
theorem affineSourceReduction_parity_bias_eq {n N C : Nat} {α Seed Advice : Type*}
    (cb : (Fin n → Bool) → Seed → Advice → Bool)
    (sampler : (Fin n → Bool) → Fin N → Fin C → Seed)
    (advice : Fin N → Fin C → Advice)
    (s : Finset α) (w : α → ℝ) (input : α → Fin n → Bool) (U : Finset (Fin N)) :
    |weightedMean s w (fun x =>
      ∏ i ∈ U, if affineSourceReduction cb sampler advice (input x) i then (1 : ℝ) else -1)| =
      |weightedMean s w (fun x =>
        ∏ i ∈ U, ∏ z, if cb (input x) (sampler (input x) i z) (advice i z)
          then (1 : ℝ) else -1)| :=
  Internal.affineSourceReduction_parity_bias_eq cb sampler advice s w input U

end Algebraic.Cutwidth.Extractor
