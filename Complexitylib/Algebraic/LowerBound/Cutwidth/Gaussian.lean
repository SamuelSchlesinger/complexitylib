/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Nondeterministic

/-!
# Circuit lower bounds from Gaussian layouts

Two Gaussian constructions improve the graph-ordering coefficient `1/3` of the cubic
pathwidth bound. The score layout (`Gaussian.Layout`) proves the cubic cutwidth bound with
coefficient `c = (3/π)(3 - 2√2) ≈ 0.16384`, giving the ordering coefficient
`2c ≈ 0.32768 ≤ 20/61`. The edge-score decomposition (`Gaussian.Frontier`) proves the cubic
pathwidth bound with coefficient `p = (3/π)(√2 - 1)/√(5 + 2√2) ≈ 0.14137`, giving the ordering
coefficient `2p ≈ 0.28274 ≤ 2/7`. The counting argument then gives circuit lower bounds with
coefficient `1 + 1/(2p) = 1 + π(√2 + 1)√(5 + 2√2)/6 ≈ 4.5368` for every dense rectangle-free
family whose threshold satisfies `log₂ K = o(n)`, for deterministic and nondeterministic
circuits.
-/

@[expose] public section

namespace Algebraic.Cutwidth

open Filter

/-- **The Gaussian graph-ordering bound.** The ordering hypothesis holds with coefficient
`(6/π)(3 - 2√2)` for every positive slack. -/
theorem Multigraph.exists_orderingBound_gaussian :
    ∀ η : ℝ, 0 < η →
      ∃ C : ℝ, Multigraph.OrderingBound (2 * Gaussian.cutwidthCoefficient) η C :=
  Multigraph.exists_orderingBound_of_cutwidthBound Gaussian.cutwidthCoefficient_pos.le
    fun _ hξ => Gaussian.exists_cutwidthBound hξ

/-- **A rational ordering coefficient below `1/3`.** The ordering hypothesis holds with
coefficient `20/61` for every positive slack. -/
theorem Multigraph.exists_orderingBound_twenty_div_sixtyOne :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound (20 / 61) η C := by
  intro η hη
  obtain ⟨C, hC⟩ := Multigraph.exists_orderingBound_gaussian η hη
  exact ⟨C, hC.mono (by linarith [Gaussian.two_mul_cutwidthCoefficient_le]) le_rfl⟩

/-- **The edge-score graph-ordering bound.** The ordering hypothesis holds with coefficient
`2 (3/π)(√2 - 1)/√(5 + 2√2)` for every positive slack. -/
theorem Multigraph.exists_orderingBound_frontier :
    ∀ η : ℝ, 0 < η →
      ∃ C : ℝ, Multigraph.OrderingBound (2 * Gaussian.frontierCoefficient) η C :=
  Multigraph.exists_orderingBound_of_pathwidthBound Gaussian.frontierCoefficient_pos.le
    fun _ hξ => Gaussian.exists_frontier_pathwidthBound hξ

/-- **The ordering coefficient `2/7`.** The ordering hypothesis holds with coefficient `2/7`
for every positive slack. -/
theorem Multigraph.exists_orderingBound_two_div_seven :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound (2 / 7) η C := by
  intro η hη
  obtain ⟨C, hC⟩ := Multigraph.exists_orderingBound_frontier η hη
  exact ⟨C, hC.mono (by linarith [Gaussian.two_mul_frontierCoefficient_le]) le_rfl⟩

/-- **Gaussian circuit bound.** A family with at least `2 ^ (n - 2)` accepting inputs that is
`K n`-rectangle-free with `log₂ K = o(n)` needs more than
`(1 + π(√2 + 1)√(5 + 2√2)/6 - ε) n` binary gates for all large `n`. -/
theorem eventually_lt_size_of_rectangleFree_gaussian
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => f n x) →
        (1 + Real.pi * (Real.sqrt 2 + 1) * Real.sqrt (5 + 2 * Real.sqrt 2) / 6 - ε) * n <
          circuit.size := by
  have bound := eventually_lt_size_of_pathwidthCoefficient Gaussian.frontierCoefficient_pos
    (fun _ hξ => Gaussian.exists_frontier_pathwidthBound hξ) f K hK hacc hrect hε
  rwa [Gaussian.one_add_inv_two_mul_frontierCoefficient] at bound

/-- **Gaussian bound for nondeterministic circuits.** Under the same hypotheses, every
nondeterministic circuit with any number of witness inputs needs more than
`(1 + π(√2 + 1)√(5 + 2√2)/6 - ε) n` gates, counting `n` ordinary inputs. -/
theorem nondet_eventually_lt_size_of_rectangleFree_gaussian
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (m : Nat) (circuit : Circuit Binary.signature (n + m) 1),
      NondetComputes circuit (f n) →
        (1 + Real.pi * (Real.sqrt 2 + 1) * Real.sqrt (5 + 2 * Real.sqrt 2) / 6 - ε) * n <
          circuit.size := by
  have bound := nondet_eventually_lt_size_of_pathwidthCoefficient
    Gaussian.frontierCoefficient_pos (fun _ hξ => Gaussian.exists_frontier_pathwidthBound hξ)
    f K hK hacc hrect hε
  rwa [Gaussian.one_add_inv_two_mul_frontierCoefficient] at bound

end Algebraic.Cutwidth
