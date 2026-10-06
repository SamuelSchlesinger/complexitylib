/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Cutwidth
public import Complexitylib.Circuits.Frontier.Main
public import Complexitylib.Circuits.Frontier.Nondeterministic
public import Complexitylib.Circuits.Frontier.Ledger.Main
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding

/-!
# The frontier method for the explicit hard family

The cutwidth development constructs one uniformly polynomial-time Boolean family,
`Algebraic.Cutwidth.Extractor.sourceReductionHardFamily`: balanced padding of a flat-source
sumset extractor with sublinear entropy. Its accepted sets satisfy the three hypotheses of
the frontier method (`sourceReductionHardFamily_frontierHypotheses`): they are rectangle-free
with a threshold of logarithm `o(n)`, and they accept exactly half of the cube.

So every general lower bound of `Complexity.Frontier` applies to this explicit family:

* `sourceReductionHardFamily_lt_innerSize_gaussian`: every circuit of fan-in two, over
  any basis and with any accepting set, has more than `(L - ε) n` gates of positive arity,
  `L = 1 + π/(3 arccos ((1 + 2√2)/4)) ≈ 4.5625`. Constant gates are free.
* `sourceReductionHardFamily_lt_innerSize_degree`: for every fan-in `r ≥ 2`,
  `(r - 1) s > (1 + 1/A_(r+1) - ε) n` with the Gaussian degree coefficient
  `A_d = 3d/(2d-3) · arccos(2√(d-1)/d)/π < 3/4`; in particular more than `(7/4 - ε) n` gates
  at fan-in three (`sourceReductionHardFamily_lt_innerSize_fanInThree`), and the simpler
  spanning-tree bound `(r - 1) s > (2 - ε) n` (`sourceReductionHardFamily_lt_innerSize_all_fanIn`).
* `sourceReductionHardFamily_lt_innerSize_nondeterministic`: the Gaussian coefficient for
  verifier circuits over any basis, uniformly in the number of witness inputs.
* `sourceReductionHardFamily_lt_innerGates_aggregate`: the Gaussian coefficient with
  sublinearly many monoid-aggregate gates of unbounded fan-in, which are not counted.

The unpadded extractor `Algebraic.Cutwidth.Extractor.sourceReductionFamily`, which is also
uniformly polynomial-time computable, has signed sumset bias `2 · 35/72`
(`flatSumsetBias_of_flatSumsetExtractor` in `Frontier.Cutwidth`). The weighted frontier bound
then gives explicit average-case hardness (`sourceReductionFamily_agreement_le`): every
circuit of fan-in two over any basis with at most `(L - ε) n` gates of positive arity agrees
with it on at most a `71/72 + 2^(-γ n)` fraction of inputs.

The cutwidth development proves the first bound for the full binary basis, counting every gate
(`Algebraic.Cutwidth.sourceReductionHardFamily_eventually_lt_size_gaussian`).
`rectangleFree_setOf` (`Frontier.Cutwidth`) translates its Boolean rectangle-freeness to the
frontier method's. This module is maintained in the library, not mirrored from upstream.
-/

@[expose] public section

namespace Complexity.Frontier

open Cslib.Circuits Filter Asymptotics

/-- **The explicit family satisfies the hypotheses of the frontier method**: its accepted
sets are eventually rectangle-free with a threshold of logarithm `o(n)`, and their logarithmic
density deficit is `o(n)` (it is the constant `log 2`). -/
theorem sourceReductionHardFamily_frontierHypotheses :
    ∃ K : ℕ → ℕ,
      (∀ᶠ n in atTop,
        RectangleFree {x | Algebraic.Cutwidth.Extractor.sourceReductionHardFamily n x = true}
          (K n)) ∧
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) ∧
      (fun n => n * Real.log (Nat.card Bool) -
        Real.log {x | Algebraic.Cutwidth.Extractor.sourceReductionHardFamily n x = true}.ncard)
        =o[atTop] (fun n => (n : ℝ)) := by
  let E : ℕ → ℕ := fun m => Algebraic.Cutwidth.Extractor.sourceReductionEntropy m
    (Algebraic.Cutwidth.Extractor.sourceReductionFamilyScale m)
  refine ⟨fun n => 2 * 2 ^ E (n - 1), ?_, ?_, ?_⟩
  · filter_upwards [(tendsto_sub_atTop_nat 1).eventually
      Algebraic.Cutwidth.Extractor.sourceReductionFamily_eventually_flat,
      eventually_ge_atTop 1] with n hflat hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
    rw [Algebraic.Cutwidth.Extractor.sourceReductionHardFamily_succ]
    exact rectangleFree_setOf
      (hflat.balancePad_rectangleFree (by positivity) (by norm_num))
  · have hE : (fun n => (E (n - 1) : ℝ)) =o[atTop] (fun n => (n : ℝ)) := by
      refine (Algebraic.Cutwidth.Extractor.sourceReductionFamilyEntropy_isLittleO.comp_tendsto
        (tendsto_sub_atTop_nat 1)).trans_isBigO (IsBigO.of_bound 1 ?_)
      filter_upwards with n
      simp only [Function.comp_apply, Real.norm_natCast, one_mul, Nat.cast_le]
      lia
    have hconst : (fun _ : ℕ => Real.log 2) =o[atTop] (fun n => (n : ℝ)) :=
      (isLittleO_const_id_atTop (Real.log 2)).comp_tendsto tendsto_natCast_atTop_atTop
    refine (hconst.add (hE.const_mul_left (Real.log 2))).congr_left fun n => ?_
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    rw [Real.log_mul two_ne_zero (by positivity), Real.log_pow]
    ring
  · have hconst : (fun _ : ℕ => Real.log 2) =o[atTop] (fun n => (n : ℝ)) :=
      (isLittleO_const_id_atTop (Real.log 2)).comp_tendsto tendsto_natCast_atTop_atTop
    refine hconst.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
    rw [ncard_setOf_eq_card_accepting,
      Algebraic.Cutwidth.Extractor.sourceReductionHardFamily_card_accepting,
      Nat.card_eq_fintype_card, Fintype.card_bool]
    push_cast
    rw [Real.log_pow]
    ring

variable {ε : ℝ}

universe v

/-- **The Gaussian bound for the explicit family, over any basis.** For every `ε > 0` and all
large `n`, every circuit of fan-in at most two deciding the explicit family, over any basis on
`Bool` and with any accepting set, has more than `(L - ε) n` gates of positive arity, where
`L = 1 + π/(3 arccos ((1 + 2√2)/4)) ≈ 4.5625`. -/
theorem sourceReductionHardFamily_lt_innerSize_gaussian (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Cslib.Circuits.Circuit σ n 1), c.FanInAtMost 2 →
        Decides c I Acc {x | Algebraic.Cutwidth.Extractor.sourceReductionHardFamily n x = true} →
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n <
            c.innerSize := by
  obtain ⟨K, hfree, hK, hdense⟩ := sourceReductionHardFamily_frontierHypotheses
  exact lowerBound_gaussian _ K hfree hK hdense hε

/-- **Every fixed fan-in, for the explicit family.** For every `r ≥ 2`, every circuit of fan-in
at most `r` deciding the explicit family, over any basis on `Bool`, satisfies
`(r - 1) s > (2 - ε) n`, where `s` counts the gates of positive arity. -/
theorem sourceReductionHardFamily_lt_innerSize_all_fanIn {r : ℕ} (hr : 2 ≤ r) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Cslib.Circuits.Circuit σ n 1), c.FanInAtMost r →
        Decides c I Acc {x | Algebraic.Cutwidth.Extractor.sourceReductionHardFamily n x = true} →
          (2 - ε) * n < (r - 1) * c.innerSize := by
  obtain ⟨K, hfree, hK, hdense⟩ := sourceReductionHardFamily_frontierHypotheses
  exact lowerBound_all_fanIn hr _ K hfree hK hdense hε

/-- **Every fixed fan-in, with the Gaussian degree coefficient, for the explicit family.** For
every `r ≥ 2`, every circuit of fan-in at most `r` deciding the explicit family, over any basis
on `Bool`, satisfies `(r - 1) s > (1 + 1/A_(r+1) - ε) n`, where `s` counts the gates of positive
arity and `A_d = 3d/(2d-3) · arccos(2√(d-1)/d)/π` (`Gaussian.degreeCoefficient`). -/
theorem sourceReductionHardFamily_lt_innerSize_degree {r : ℕ} (hr : 2 ≤ r) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Cslib.Circuits.Circuit σ n 1), c.FanInAtMost r →
        Decides c I Acc {x | Algebraic.Cutwidth.Extractor.sourceReductionHardFamily n x = true} →
          (1 + 1 / Gaussian.degreeCoefficient (r + 1) - ε) * n < (r - 1) * c.innerSize := by
  obtain ⟨K, hfree, hK, hdense⟩ := sourceReductionHardFamily_frontierHypotheses
  exact lowerBound_degree hr _ K hfree hK hdense hε

/-- **Ternary gates, for the explicit family.** Every circuit of fan-in at most three deciding
the explicit family, over any basis on `Bool`, has more than `(7/4 - ε) n` gates of positive
arity. -/
theorem sourceReductionHardFamily_lt_innerSize_fanInThree (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Cslib.Circuits.Circuit σ n 1), c.FanInAtMost 3 →
        Decides c I Acc {x | Algebraic.Cutwidth.Extractor.sourceReductionHardFamily n x = true} →
          (7 / 4 - ε) * n < c.innerSize := by
  obtain ⟨K, hfree, hK, hdense⟩ := sourceReductionHardFamily_frontierHypotheses
  exact lowerBound_fanInThree _ K hfree hK hdense hε

/-- **Verifier circuits for the explicit family.** The Gaussian coefficient holds for
nondeterministic circuits of fan-in two over any basis on `Bool`, uniformly in the number `k`
of witness inputs, which are not counted in `n`. -/
theorem sourceReductionHardFamily_lt_innerSize_nondeterministic (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Cslib.Circuits.Circuit σ (n + k) 1), c.FanInAtMost 2 →
        NondeterministicDecides c I Acc
          {x | Algebraic.Cutwidth.Extractor.sourceReductionHardFamily n x = true} →
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n <
            c.innerSize := by
  obtain ⟨K, hfree, hK, hdense⟩ := sourceReductionHardFamily_frontierHypotheses
  exact lowerBound_nondeterministic_gaussian _ K hfree hK hdense hε

/-- **Aggregate gates for the explicit family.** The Gaussian coefficient holds for circuits
over any basis on `Bool` whose ordinary gates have fan-in at most two and whose special gates
of unbounded fan-in aggregate in a finite commutative monoid `T`, provided the special gates
carry `o(n)` bits of monoid state. Only the ordinary gates of positive arity are counted. -/
theorem sourceReductionHardFamily_lt_innerGates_aggregate {β : ℕ → ℝ}
    (hβ : β =o[atTop] fun n => (n : ℝ)) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Cslib.Circuits.Circuit σ n 1) (special : ℕ → Prop) (T : Type) [CommMonoid T] [Finite T],
        (∀ g : Fin c.size, ¬ special g → σ.Arity (c.program.lines g).op ≤ 2) →
        (∀ g : Fin c.size, special g → Aggregates (I (c.program.lines g).op) T) →
        Nat.card {g : Fin c.size // special g} * Real.log (Nat.card T) ≤ β n →
        Decides c I Acc {x | Algebraic.Cutwidth.Extractor.sourceReductionHardFamily n x = true} →
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n <
            (erase special c.program).innerGates.card := by
  obtain ⟨K, hfree, hK, hdense⟩ := sourceReductionHardFamily_frontierHypotheses
  exact lowerBound_aggregate_gaussian _ K hfree hK hdense hβ hε

/-- **Average-case hardness of the explicit extractor.** For every `ε > 0` there is `γ > 0`
such that for all large `n`, every circuit of fan-in two, over any basis on `Bool`, with at most
`(L - ε) n` gates of positive arity agrees with the explicit extractor on at most a
`71/72 + 2^(-γ n)` fraction of inputs, where `L = 1 + π/(3 arccos ((1 + 2√2)/4)) ≈ 4.5625`. -/
theorem sourceReductionFamily_agreement_le (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (c : Cslib.Circuits.Circuit σ n 1),
        c.FanInAtMost 2 →
        (c.innerSize : ℝ) ≤
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n →
        agreement (Algebraic.Cutwidth.Extractor.sourceReductionFamily n)
          (fun x => c.eval I x 0) ≤ 71 / 72 + (2 : ℝ) ^ (-γ * n) := by
  let E : ℕ → ℕ := fun m => Algebraic.Cutwidth.Extractor.sourceReductionEntropy m
    (Algebraic.Cutwidth.Extractor.sourceReductionFamilyScale m)
  have hlog : (fun n => Real.log ((2 * 2 ^ E n : ℕ) : ℝ)) =o[atTop] (fun n => (n : ℝ)) := by
    have hconst : (fun _ : ℕ => Real.log 2) =o[atTop] (fun n => (n : ℝ)) :=
      (isLittleO_const_id_atTop (Real.log 2)).comp_tendsto tendsto_natCast_atTop_atTop
    refine (hconst.add
      (Algebraic.Cutwidth.Extractor.sourceReductionFamilyEntropy_isLittleO.const_mul_left
        (Real.log 2))).congr_left fun n => ?_
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    rw [Real.log_mul two_ne_zero (by positivity), Real.log_pow]
    ring
  have hbias : ∀ᶠ n in atTop,
      FlatSumsetBias (Algebraic.Cutwidth.Extractor.sourceReductionFamily n)
        (2 * 2 ^ E n) (2 * (35 / 72)) := by
    filter_upwards [Algebraic.Cutwidth.Extractor.sourceReductionFamily_eventually_flat] with n hn
    refine flatSumsetBias_of_flatSumsetExtractor fun P Q hP hQ => hn P Q ?_ ?_
    · exact le_trans (Nat.le_mul_of_pos_left _ two_pos) hP
    · exact le_trans (Nat.le_mul_of_pos_left _ two_pos) hQ
  obtain ⟨γ, hγ, h⟩ := averageCase_sumset hε
    (fun n => Algebraic.Cutwidth.Extractor.sourceReductionFamily n)
    (fun n => 2 * 2 ^ E n) (fun _ => 35 / 72)
    (Eventually.of_forall fun n => by
      have : 1 ≤ 2 ^ E n := Nat.one_le_two_pow
      lia)
    hlog (Eventually.of_forall fun _ => by norm_num) hbias
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [h] with n hn σ I c hfan hsize
  have := hn σ I c hfan hsize
  norm_num at this ⊢
  linarith

end Complexity.Frontier
