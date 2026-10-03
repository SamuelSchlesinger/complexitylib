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
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Conditioning
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Majority.Probability

/-!
# From conditional parity bias to sumset extraction

Apply the majority bound separately at each good second-source fixing,
then aggregate the ordered source pairs. This proves the final analytic
step of the constant-error route. The source-reduction construction that
must supply the parity-bias hypotheses is not assumed to have been built.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

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
    FlatSumsetExtractor (fun z => Complexity.majority (reduce z)) K (35 / 72) := by
  apply FlatSumsetExtractor.of_half_good_fibers positive
  intro P Q hP hQ
  obtain ⟨G, inside, many, goodFibers⟩ := fibers P Q hP hQ
  refine ⟨G, inside, many, ?_⟩
  intro y hy b
  obtain ⟨m, good, hm, budget, bias, bad⟩ := goodFibers y hy
  have hPpos : (0 : ℝ) < P.card := by exact_mod_cast positive.trans_le hP
  exact majority_mass_ge_of_parityBias good (fun x => reduce (xorInput x y))
    (fun _ _ => div_nonneg zero_le_one hPpos.le)
    (by simp [ne_of_gt hPpos]) hm hδ budget bias bad b

end Algebraic.Cutwidth.Extractor.Internal
