/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Linear.Internal

/-!
# Parity bounds for actual linear-sampler affine calls

At a fixed second summand, one honest sampler value outside the actual
bad-seed set bounds the complete component parity by twice the requested
statistical error. This is the linearity step of Chattopadhyay--Liao,
*Extractors for Sum of Two Sources*, Lemma 5.4, equation (5):
<https://arxiv.org/abs/2110.12652>.

The sampler's linearity is explicit. No statistical guarantee or
polynomial-time implementation of a sampler is asserted here.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- One escaping honest seed controls the actual full component parity after fixing a summand. -/
theorem affineLeakage_linear_parity_le {n d t : Nat} {Out : Type*} [Fintype Out]
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Out)
    (p : (Fin n → Bool) → ℝ)
    (sampler : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool)
    (linear : ∀ x y i, sampler (xorInput x y) i = xorInput (sampler x i) (sampler y i))
    (bit : Out → Bool) (balanced : mapWeight bit (uniformWeight Out) = uniformWeight Bool)
    (γ : ℝ) (b : Fin n → Bool)
    (good : sampler b none ∉ affineLeakageBadSeeds cb p sampler advice γ) :
    |∑ x, p x * ∏ i, if bit (cb (xorInput x b) (sampler (xorInput x b) i) (advice i))
      then (1 : ℝ) else -1| ≤ 2 * γ :=
  Internal.affineLeakage_linear_parity_le cb p sampler advice linear bit balanced γ b good

end Algebraic.Cutwidth.Extractor
