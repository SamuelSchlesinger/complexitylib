/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Main
public import Complexitylib.Circuits.Frontier.Nondeterministic
public import Complexitylib.Circuits.Frontier.Ledger.Main
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Rectangle
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
* `sourceReductionHardFamily_lt_innerSize_all_fanIn`: for every fan-in `r ≥ 2`,
  `(r - 1) s > (2 - ε) n`.
* `sourceReductionHardFamily_lt_innerSize_nondeterministic`: the Gaussian coefficient for
  verifier circuits over any basis, uniformly in the number of witness inputs.
* `sourceReductionHardFamily_lt_innerGates_aggregate`: the Gaussian coefficient with
  sublinearly many monoid-aggregate gates of unbounded fan-in, which are not counted.

The cutwidth development proves the first bound for the full binary basis, counting every gate
(`Algebraic.Cutwidth.sourceReductionHardFamily_eventually_lt_size_gaussian`).
`rectangleFree_setOf` translates its Boolean rectangle-freeness to the frontier method's.
-/

@[expose] public section

namespace Complexity.Frontier

open Cslib.Circuits Filter Asymptotics

/-- **Boolean rectangle-freeness.** A Boolean function that is `K`-rectangle-free in the
sense of the cutwidth development accepts a `K`-rectangle-free set. -/
theorem rectangleFree_setOf {n K : ℕ} {f : Cslib.BooleanFunction n}
    (h : Algebraic.Cutwidth.RectangleFree f K) : RectangleFree {x | f x = true} K := by
  classical
  intro X A B hAB
  let U : Finset (Fin n) := X.toFinset
  have hU (i : Fin n) : i ∈ U ↔ i ∈ X := Set.mem_toFinset
  let left : (X → Bool) → (U → Bool) := fun a i => a ⟨i, (hU i).1 i.2⟩
  let right : (↥Xᶜ → Bool) → (↥Uᶜ → Bool) := fun b i =>
    b ⟨i, fun hi => Finset.mem_compl.1 i.2 ((hU i).2 hi)⟩
  have injL : left.Injective := by
    intro a a' haa'
    funext i
    simpa [left] using congrFun haa' ⟨i, (hU i).2 i.2⟩
  have injR : right.Injective := by
    intro b b' hbb'
    funext i
    simpa [right] using congrFun hbb' ⟨i, Finset.mem_compl.2 fun hi => i.2 ((hU i).1 hi)⟩
  have hglue {a : X → Bool} (ha : a ∈ A) {b : ↥Xᶜ → Bool} (hb : b ∈ B) :
      f (Algebraic.Cutwidth.glue U (left a) (right b)) = true := by
    refine hAB (mem_rectangle.2 ⟨?_, ?_⟩)
    · convert ha using 1
      funext i
      simp [Algebraic.Cutwidth.glue, left, (hU i).2 i.2]
    · convert hb using 1
      funext i
      have hi : (i : Fin n) ∉ U := fun h' => i.2 ((hU i).1 h')
      simp [Algebraic.Cutwidth.glue, right, hi]
  have hrect := h U ((Set.toFinite A).toFinset.image left) ((Set.toFinite B).toFinset.image right)
    (by
      intro p hp q hq
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
      exact hglue ((Set.Finite.mem_toFinset _).1 ha) ((Set.Finite.mem_toFinset _).1 hb))
  rw [Finset.card_image_of_injective _ injL, Finset.card_image_of_injective _ injR] at hrect
  rwa [Set.ncard_eq_toFinset_card A, Set.ncard_eq_toFinset_card B]

/-- The accepted set of a Boolean function has as many elements as its accepting inputs. -/
theorem ncard_setOf_eq_card_accepting {n : ℕ} (f : Cslib.BooleanFunction n) :
    {x | f x = true}.ncard = (Algebraic.Cutwidth.accepting f).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [Algebraic.Cutwidth.mem_accepting]

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

end Complexity.Frontier
