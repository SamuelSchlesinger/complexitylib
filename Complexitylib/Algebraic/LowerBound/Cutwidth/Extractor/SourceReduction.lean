/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Majority.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments.Defs
public import Mathlib.Analysis.Real.Sqrt
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Internal

/-!
# The parity-bias target sufficient for a constant-error sumset extractor

For each qualifying pair of source sets `P, Q`, on at least half the inputs
in `Q`, select good output coordinates whose parities of orders one through
four have small absolute sign expectation. The checked
moment and majority arguments then give error `35/72`, strictly below one
half. Balanced padding supplies the density needed by the circuit theorem.

The intended source reduction is Chattopadhyay and Liao, *Extractors for Sum
of Two Sources* (2021), Lemma 5.4 through equation (5). Its linear sampler
must still be constructed and composed with the now-checked affine
correlation breaker to supply these parity bounds. This module proves the
implication from that target to extraction, not the existence or uniform
evaluation of `reduce`.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open scoped Classical

/-- Conditional low-order parity bias on enough good coordinates implies
sumset extraction after majority, with error `35/72`. The selected coordinates
may depend on both source sets and the second-source fixing, while `reduce`
is one fixed function of their XOR alone. The bound `δ` measures absolute
sign-parity expectation, twice the corresponding Boolean probability bias. -/
theorem majority_flatSumsetExtractor_of_parity_fibers {n N K : Nat}
    (reduce : (Fin n → Bool) → Fin N → Bool) (positive : 0 < K)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (fibers : ∀ P Q : Finset (Fin n → Bool), K ≤ P.card → K ≤ Q.card →
      ∃ G ⊆ Q, (1 / 2 : ℝ) * Q.card ≤ G.card ∧
        ∀ y ∈ G, ∃ (m : Nat) (good : Fin m ↪ Fin N), 0 < m ∧
          100 * (m : ℝ) ^ 2 * δ ≤ 1 ∧
          ParityBiasBound P (fun _ => 1 / (P.card : ℝ))
            (fun x i => if reduce (xorInput x y) (good i) then 1 else -1) δ ∧
          ((N - m : Nat) : ℝ) ≤ Real.sqrt (m : ℝ) / 8) :
    FlatSumsetExtractor (fun z => Complexity.majority (reduce z)) K (35 / 72) :=
  Internal.majority_flatSumsetExtractor_of_parity_fibers reduce positive hδ fibers

end Algebraic.Cutwidth.Extractor
