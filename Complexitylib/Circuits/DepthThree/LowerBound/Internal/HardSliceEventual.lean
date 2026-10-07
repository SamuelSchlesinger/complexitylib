/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.HardSliceExistence
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.HardSliceParameters
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.FinalParameterBounds
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.IrreducibleEncoding
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageSlice

/-!
# Unrestricted depth-three lower bound: hard slice eventual

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/HardSliceEventual.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

theorem exists_good_language_slice_eventually (b : ℕ) (hb : 1 ≤ b)
    (B : ℝ) (hB : 0 < B) :
    ∃ N : ℕ, 20480 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ α : Fin n → Sum (Fin (dataDimension n)) Bool,
        restrictionAvg (liveProbability B (dataDimension n)) (fun σ =>
          if ¬ goodRestriction (liveProbability B (dataDimension n))
            ((2 : ℝ) ^ (-(B * Real.sqrt (dataDimension n : ℝ)) / 16)) b
            (fun x => language (List.ofFn (GateInput.assignment α x))) σ
          then 1 else 0) ≤
          4 * (2 : ℝ) ^ (-(B * Real.sqrt (dataDimension n : ℝ)) / 16) := by
  obtain ⟨De, hDe, herr⟩ := actual_hard_slice_error_bound_eventually b hb B hB
  obtain ⟨Dp, hDp, hprob⟩ := exists_liveProbability_threshold B hB
  let D := max De Dp
  refine ⟨5 * D, ?_, ?_⟩
  · have hbig : 4096 ≤ D := hDe.trans (le_max_left _ _)
    omega
  intro n hn
  let d := dataDimension n
  have hDd : D ≤ d := by
    dsimp [d, dataDimension]
    omega
  have hde : De ≤ d := (le_max_left _ _).trans hDd
  have hdp : Dp ≤ d := (le_max_right _ _).trans hDd
  have hd4096 : 4096 ≤ d := hDe.trans hde
  have hdpos : 0 < d := by omega
  have hr : 0 < hashDimension d := hashDimension_pos hdpos
  have ht2 : 2 ≤ independenceOrder d := (independenceOrder_two_le_iff d).mpr (by omega)
  obtain ⟨h, hh⟩ := independenceOrder_even d
  have heven : 2 * h = independenceOrder d := by omega
  have hhpos : 0 < h := by omega
  obtain ⟨hq0, hqhalf⟩ := hprob d hdp
  have hq1 : liveProbability B d ≤ 1 := by linarith
  obtain ⟨p, hp⟩ := exists_irreducible_inputPolynomialBits (hashDimension d) hr
  let : Fact (Irreducible (BinaryAlgebra.inputPolynomialBits p)) := ⟨hp⟩
  have hbound (m : ℕ)
      (hmlo : (liveProbability B d * d) / 2 ≤ (m : ℝ))
      (hmhi : (m : ℝ) ≤ 2 * (liveProbability B d * d)) :
      (2 : ℝ) ^ m / (2 : ℝ) ^ hashDimension d +
        sparseMomentBound m b (hardSliceSparseConstant b hb * m) h
          ((2 : ℝ) ^ (-(m : ℝ) / 4)) ≤
        2 * (2 : ℝ) ^ (-(liveProbability B d * d) / 16) := by
    rw [liveProbability_mul_dimension B d hdpos] at hmlo hmhi ⊢
    exact herr d hde m h hmlo hmhi heven
  have hex : ∃ (u : Fin (d + hashDimension d - 1) → Bool)
      (β : Fin (independenceOrder d) → BinaryAlgebra.BitQuotient p),
      restrictionAvg (liveProbability B d) (fun σ =>
        if ¬ goodRestriction (liveProbability B d)
          ((2 : ℝ) ^ (-(B * Real.sqrt (d : ℝ)) / 16)) b
          (hashAcceptance p (independenceOrder d) u β) σ then 1 else 0) ≤
        4 * (2 : ℝ) ^ (-(B * Real.sqrt (d : ℝ)) / 16) := by
    rw [← heven]
    simpa only [liveProbability_mul_dimension B d hdpos] using
      exists_good_hash_coefficients p hr hb hhpos (liveProbability B d) hq0.le hq1 hbound
  obtain ⟨u, β, hβ⟩ := hex
  let c := coefficientInputBits p β
  let α : Fin n → Sum (Fin (dataDimension n)) Bool := canonicalSlice n u p c
  have hfit : blockLen d ≤ n :=
    (blockLen_le_five_mul d hd4096).trans (five_mul_dataDimension_le n)
  have heval : (fun x => language (List.ofFn (GateInput.assignment α x))) =
      hashAcceptance p (independenceOrder d) u β := by
    funext x
    rw [language_canonicalSlice_acceptEval n u p c x hdpos ht2 hfit]
    change hashAcceptance p (independenceOrder d) u
      (fun j => BinaryAlgebra.encode (fun i => BinaryAlgebra.bitValue (p i))
        (fun i => BinaryAlgebra.bitValue (coefficientInputBits p β j i))) x = _
    rw [hashAcceptance_coefficientInputBits]
  refine ⟨α, ?_⟩
  rw [heval]
  exact hβ

end DepthThreeLowerBound

end

end Complexity
