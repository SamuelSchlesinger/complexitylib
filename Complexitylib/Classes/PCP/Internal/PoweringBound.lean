/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.KilledFirstMoment
public import Mathlib.Algebra.Order.Ring.Pow

/-!
# The powering bound, in closed form

`powering_soundness` states the second-moment argument exactly as it falls out
of the two moment estimates: a ratio of a first-moment lower bound squared to a
second-moment upper bound, with every count left explicit. This module turns it
into the statement the amplifier needs — a lower bound on the powered system's
value as a rational function of the original value, with all the constants
isolated:

`c² u / (c + 2 T² u + 2 T / (1 - λ)) ≤ unsatFrac (killedPow)`

where `u` is the decoded assignment's violated fraction and
`c = (q - 1) / (4 |α|²)`. For small `u` this is linear in `u` with slope of
order `(q - 1)² (1 - λ) / (|α|⁴ T)`, and since `T` need only be linear in
`q |α|`, the slope grows with `q`: that is the amplification. For large `u` it
is bounded below by a constant.

Two technical points are handled here. The first moment appears in the
denominator of the second-moment bound, so the ratio has to be made monotone
before the first-moment *lower* bound can be substituted in both places. And
the plurality loss must be at most half the total, which requires `T` large
enough relative to `q` and `|α|` — Bernoulli's inequality shows
`H + 1 = 4 |α| (q - 1)` suffices.

## Main results

- `Complexity.RegCSP.unsatFrac_killedPow_clean` — the closed-form bound
- `Complexity.RegCSP.le_unsatVal_killedPow_min` — the `min` form
- `Complexity.exists_powering_params` — a choice of `T` and `H` meeting every
  side condition
-/

@[expose] public section

namespace Complexity

/-! ### Monotonicity of the Paley–Zygmund ratio -/

/-- `m ↦ m² / (m + P)` is increasing on `m ≥ 0` for `P > 0`. -/
theorem sq_div_add_mono {m M P : ℝ} (hm : 0 ≤ m) (hmM : m ≤ M) (hP : 0 < P) :
    m ^ 2 / (m + P) ≤ M ^ 2 / (M + P) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have h1 : 0 ≤ m * M * (M - m) := by
    apply mul_nonneg (mul_nonneg hm (by linarith)) (by linarith)
  have h2 : 0 ≤ P * ((M - m) * (M + m)) := by
    apply mul_nonneg hP.le (mul_nonneg (by linarith) (by linarith))
  nlinarith [h1, h2]

/-! ### The algebra of the bound -/

/-- The powering bound's algebra, over opaque real quantities: `U` violated
darts among `N · d`, first moment at least `U (q - 1) (d^T q^T / 2)² / (K² d^(T+1) q^T)`,
second moment as in `sum_sq_goodCrossings_le`. -/
theorem powering_algebra {U N d K q lam C : ℝ} (T' : ℕ) (hN : 0 < N) (hd : 0 < d)
    (hK : 0 < K) (hq : 1 ≤ q) (hlam : lam < 1) (hU : 0 < U)
    (hcount : (U * ((q - 1) * (d ^ (T' + 2) * q ^ (T' + 2) / 2
          * (d ^ (T' + 2) * q ^ (T' + 2) / 2))) / (K ^ 2 * (d ^ (T' + 2 + 1) * q ^ (T' + 2)))) ^ 2
        / (U * ((q - 1) * (d ^ (T' + 2) * q ^ (T' + 2) / 2
          * (d ^ (T' + 2) * q ^ (T' + 2) / 2))) / (K ^ 2 * (d ^ (T' + 2 + 1) * q ^ (T' + 2)))
          + 2 * (q ^ (T' + 2) * (d ^ T' * (((T' + 2 : ℕ) : ℝ) * ((T' + 2 : ℕ) : ℝ) * (U * U / N)
            + ((T' + 2 : ℕ) : ℝ) * (1 / (1 - lam)) * (d * U)))))
      ≤ C) :
    ((q - 1) / (4 * K ^ 2)) ^ 2 * (U / (N * d))
        / ((q - 1) / (4 * K ^ 2) + 2 * ((T' + 2 : ℕ) : ℝ) ^ 2 * (U / (N * d))
          + 2 * ((T' + 2 : ℕ) : ℝ) / (1 - lam))
      ≤ C / (N * (d ^ (T' + 2) * q ^ (T' + 2))) := by
  have hlam' : 0 < 1 - lam := by linarith
  set c : ℝ := (q - 1) / (4 * K ^ 2) with hc
  set u : ℝ := U / (N * d) with hu
  set W : ℝ := N * (d ^ (T' + 2) * q ^ (T' + 2)) with hW
  set Tr : ℝ := ((T' + 2 : ℕ) : ℝ) with hTr
  set E : ℝ := 2 * Tr ^ 2 * u + 2 * Tr / (1 - lam) with hE
  have hW0 : 0 < W := by rw [hW]; positivity
  have hF : U * ((q - 1) * (d ^ (T' + 2) * q ^ (T' + 2) / 2
        * (d ^ (T' + 2) * q ^ (T' + 2) / 2))) / (K ^ 2 * (d ^ (T' + 2 + 1) * q ^ (T' + 2)))
      = c * u * W := by
    rw [hc, hu, hW]
    field_simp
    ring
  have hP : 2 * (q ^ (T' + 2) * (d ^ T' * (Tr * Tr * (U * U / N) + Tr * (1 / (1 - lam)) * (d * U))))
      = W * (u * E) := by
    rw [hE, hu, hW]
    field_simp
    ring
  rw [hF, hP] at hcount
  have hratio : (c * u * W) ^ 2 / (c * u * W + W * (u * E)) = W * (c ^ 2 * u / (c + E)) := by
    field_simp
  rw [hratio] at hcount
  have hgoal : c + 2 * Tr ^ 2 * u + 2 * Tr / (1 - lam) = c + E := by rw [hE]; ring
  rw [hgoal, div_le_div_iff₀ (by positivity) hW0]
  have hcE : 0 < c + E := by positivity
  have h := mul_le_mul_of_nonneg_right hcount hcE.le
  have heq : c ^ 2 * u * W = W * (c ^ 2 * u / (c + E)) * (c + E) := by
    rw [mul_assoc W, div_mul_cancel₀ _ hcE.ne']
    ring
  rw [heq]
  exact h

namespace RegCSP

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
variable (R : RegCSP α) (q T : ℕ) (hq : 0 < q)

/-- **The second-moment count, with the first-moment lower bound on both
sides.** -/
theorem card_unsatDarts_ge' (A : (R.killedPow q T hq).Assignment) {Alb P : ℝ}
    (hA0 : 0 ≤ Alb)
    (hA : Alb ≤ ∑ z : R.graph.V × R.KLabels q T, ((R.goodCrossings q T hq A z).card : ℝ))
    (hB : ∑ z : R.graph.V × R.KLabels q T, ((R.goodCrossings q T hq A z).card : ℝ) ^ 2
      ≤ (∑ z : R.graph.V × R.KLabels q T, ((R.goodCrossings q T hq A z).card : ℝ)) + P)
    (hP : 0 < P) :
    Alb ^ 2 / (Alb + P) ≤ (((R.killedPow q T hq).unsatDarts A).card : ℝ) := by
  classical
  have hS0 : 0 ≤ ∑ z : R.graph.V × R.KLabels q T, ((R.goodCrossings q T hq A z).card : ℝ) :=
    Finset.sum_nonneg fun z _ => by positivity
  refine le_trans (sq_div_add_mono hA0 hA hP) ?_
  exact R.card_unsatDarts_ge q T hq A hS0 le_rfl hB (by linarith)

/-- The slope constant of the powering bound. -/
noncomputable def powConst (q : ℕ) (α : Type) [Fintype α] : ℝ :=
  ((q : ℝ) - 1) / (4 * (Fintype.card α : ℝ) ^ 2)

/-- **The powering bound in closed form.** Under the side conditions of
`powering_soundness` and with the plurality loss at most half the total, the
powered system's violated fraction is at least
`c² u / (c + 2 T² u + 2 T / (1 - λ))`, `u` the decoded assignment's violated
fraction. -/
theorem unsatFrac_killedPow_clean (A : (R.killedPow q T hq).Assignment) {H : ℕ}
    (hH : 2 * H + 1 < T) (hHT : H + 1 ≤ T)
    (hsq : ∀ i ∈ Finset.range (H + 1), ∀ j ∈ Finset.range (H + 1), i + j + 1 < T)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hspec : R.graph.SpectralBound lam)
    (hn : 0 < R.graph.order) (hq1 : 1 ≤ q)
    (hloss : 2 * (Fintype.card α * pluralityLoss R.graph.deg q T H) ≤ R.graph.deg ^ T * q ^ T) :
    powConst q α ^ 2 * (((R.unsatFrac (R.kDecode q T hq A) : ℚ) : ℝ))
        / (powConst q α + 2 * (T : ℝ) ^ 2 * (((R.unsatFrac (R.kDecode q T hq A) : ℚ) : ℝ))
          + 2 * (T : ℝ) / (1 - lam))
      ≤ (((R.killedPow q T hq).unsatFrac A : ℚ) : ℝ) := by
  classical
  have hN0 : (0 : ℝ) < R.graph.order := by exact_mod_cast hn
  have hd0 : (0 : ℝ) < R.graph.deg := by exact_mod_cast R.graph.deg_pos
  have hK0 : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  -- the violated fraction of the decoded assignment
  have hu : (((R.unsatFrac (R.kDecode q T hq A) : ℚ) : ℝ))
      = ((R.unsatDarts (R.kDecode q T hq A)).card : ℝ) / ((R.graph.order : ℝ) * R.graph.deg) := by
    rw [RegCSP.unsatFrac]
    push_cast
    rfl
  have hfrac : (((R.killedPow q T hq).unsatFrac A : ℚ) : ℝ)
      = (((R.killedPow q T hq).unsatDarts A).card : ℝ)
        / ((R.graph.order : ℝ) * ((R.graph.deg : ℝ) ^ T * (q : ℝ) ^ T)) := by
    rw [RegCSP.unsatFrac, R.card_dart_killedPow q T hq, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_natCast]
    push_cast
    ring
  rw [hu, hfrac, powConst]
  -- the case of no violated darts is trivial
  by_cases hU0 : ((R.unsatDarts (R.kDecode q T hq A)).card : ℝ) = 0
  · rw [hU0]
    simp only [zero_div, mul_zero]
    positivity
  have hUpos : (0 : ℝ) < ((R.unsatDarts (R.kDecode q T hq A)).card : ℝ) :=
    lt_of_le_of_ne (by positivity) (Ne.symm hU0)
  -- the first-moment lower bound, simplified using the loss condition
  have hle : Fintype.card α * pluralityLoss R.graph.deg q T H ≤ R.graph.deg ^ T * q ^ T := by
    omega
  have hhalf : (((R.graph.deg ^ T * q ^ T - Fintype.card α * pluralityLoss R.graph.deg q T H
      : ℕ)) : ℝ) ≥ (R.graph.deg : ℝ) ^ T * (q : ℝ) ^ T / 2 := by
    rw [Nat.cast_sub hle]
    push_cast
    have h2 : (2 : ℝ) * (Fintype.card α * pluralityLoss R.graph.deg q T H : ℕ)
        ≤ (R.graph.deg ^ T * q ^ T : ℕ) := by exact_mod_cast hloss
    push_cast at h2
    linarith
  have hden : (0 : ℝ) < ((Fintype.card α ^ 2 * (R.graph.deg ^ (T + 1) * q ^ T) : ℕ) : ℝ) := by
    have : 0 < Fintype.card α ^ 2 * (R.graph.deg ^ (T + 1) * q ^ T) := by
      have := R.graph.deg_pos
      have := (Fintype.card_pos : 0 < Fintype.card α)
      positivity
    exact_mod_cast this
  have hF : ((R.unsatDarts (R.kDecode q T hq A)).card : ℝ) * (((q : ℝ) - 1)
        * ((R.graph.deg : ℝ) ^ T * (q : ℝ) ^ T / 2 * ((R.graph.deg : ℝ) ^ T * (q : ℝ) ^ T / 2)))
        / ((Fintype.card α : ℝ) ^ 2 * ((R.graph.deg : ℝ) ^ (T + 1) * (q : ℝ) ^ T))
      ≤ ∑ z : R.graph.V × R.KLabels q T, ((R.goodCrossings q T hq A z).card : ℝ) := by
    have h := (div_le_iff₀' hden).2 (R.sum_goodCrossings_ge q T hq A hH hHT hsq)
    refine le_trans ?_ h
    have hden' : (0 : ℝ)
        < (Fintype.card α : ℝ) ^ 2 * ((R.graph.deg : ℝ) ^ (T + 1) * (q : ℝ) ^ T) := by
      positivity
    have hcastden : ((Fintype.card α ^ 2 * (R.graph.deg ^ (T + 1) * q ^ T) : ℕ) : ℝ)
        = (Fintype.card α : ℝ) ^ 2 * ((R.graph.deg : ℝ) ^ (T + 1) * (q : ℝ) ^ T) := by
      push_cast; ring
    rw [hcastden]
    refine div_le_div_of_nonneg_right ?_ hden'.le
    push_cast
    rw [Nat.cast_sub hq1]
    push_cast
    refine mul_le_mul_of_nonneg_left ?_ hUpos.le
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    exact mul_le_mul hhalf hhalf (by positivity) (by positivity)
  have hB := R.sum_sq_goodCrossings_le q T hq A hlam0 hlam1 hspec hn
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 2 := ⟨T - 2, by omega⟩
  have hP0 : (0 : ℝ) < 2 * ((q : ℝ) ^ (T' + 2) * ((R.graph.deg : ℝ) ^ (T' + 2 - 2)
      * (((T' + 2 : ℕ) : ℝ) * ((T' + 2 : ℕ) : ℝ)
          * (((R.unsatDarts (R.kDecode q (T' + 2) hq A)).card : ℝ)
            * ((R.unsatDarts (R.kDecode q (T' + 2) hq A)).card : ℝ) / (R.graph.order : ℝ))
        + ((T' + 2 : ℕ) : ℝ) * (1 / (1 - lam)) * ((R.graph.deg : ℝ)
            * ((R.unsatDarts (R.kDecode q (T' + 2) hq A)).card : ℝ))))) := by
    positivity
  have hcount := R.card_unsatDarts_ge' q (T' + 2) hq A (by positivity) hF hB hP0
  have hsub : T' + 2 - 2 = T' := by omega
  rw [hsub] at hcount
  exact powering_algebra T' hN0 hd0 hK0 hq1' hlam1 hUpos hcount

/-! ### The `min` form -/

/-- The slope of the powering bound for small values. -/
noncomputable def powSlope (c T lam : ℝ) : ℝ := c ^ 2 / (c + 2 + 2 * T / (1 - lam))

/-- The floor of the powering bound for large values. -/
noncomputable def powFloor (c T lam : ℝ) : ℝ :=
  (c ^ 2 / T ^ 2) / (c + 2 * T ^ 2 + 2 * T / (1 - lam))

/-- **The rational bound dominates a `min`.** For values up to `1 / T²` the
bound is linear with slope `powSlope`; beyond that it is at least `powFloor`. -/
theorem min_le_powBound {c T lam u : ℝ} (hc : 0 ≤ c) (hT : 1 ≤ T) (hlam : lam < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    min (powSlope c T lam * u) (powFloor c T lam)
      ≤ c ^ 2 * u / (c + 2 * T ^ 2 * u + 2 * T / (1 - lam)) := by
  have hlam' : 0 < 1 - lam := by linarith
  have hD : 0 < c + 2 * T ^ 2 * u + 2 * T / (1 - lam) := by positivity
  by_cases h : u ≤ 1 / T ^ 2
  · refine le_trans (min_le_left _ _) ?_
    rw [powSlope, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_left (by positivity) hD ?_
    have : 2 * T ^ 2 * u ≤ 2 := by
      rw [le_div_iff₀ (by positivity)] at h
      linarith
    linarith
  · refine le_trans (min_le_right _ _) ?_
    rw [powFloor]
    push Not at h
    have hT2 : 0 < T ^ 2 := by positivity
    have hnum : c ^ 2 / T ^ 2 ≤ c ^ 2 * u := by
      rw [div_le_iff₀ hT2]
      have : 1 / T ^ 2 * T ^ 2 ≤ u * T ^ 2 :=
        mul_le_mul_of_nonneg_right h.le hT2.le
      rw [one_div, inv_mul_cancel₀ hT2.ne'] at this
      nlinarith [sq_nonneg c]
    have hden : c + 2 * T ^ 2 * u + 2 * T / (1 - lam) ≤ c + 2 * T ^ 2 + 2 * T / (1 - lam) := by
      nlinarith
    calc (c ^ 2 / T ^ 2) / (c + 2 * T ^ 2 + 2 * T / (1 - lam))
        ≤ (c ^ 2 * u) / (c + 2 * T ^ 2 + 2 * T / (1 - lam)) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ c ^ 2 * u / (c + 2 * T ^ 2 * u + 2 * T / (1 - lam)) :=
          div_le_div_of_nonneg_left (by positivity) hD hden

/-- **The powered value, in `min` form.** -/
theorem le_unsatVal_killedPow_min {H : ℕ}
    (hH : 2 * H + 1 < T) (hHT : H + 1 ≤ T)
    (hsq : ∀ i ∈ Finset.range (H + 1), ∀ j ∈ Finset.range (H + 1), i + j + 1 < T)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hspec : R.graph.SpectralBound lam)
    (hn : 0 < R.graph.order) (hq1 : 1 ≤ q)
    (hloss : 2 * (Fintype.card α * pluralityLoss R.graph.deg q T H) ≤ R.graph.deg ^ T * q ^ T) :
    min (powSlope (powConst q α) T lam * ((R.unsatVal : ℚ) : ℝ)) (powFloor (powConst q α) T lam)
      ≤ (((R.killedPow q T hq).unsatVal : ℚ) : ℝ) := by
  refine R.le_unsatVal_killedPow q T hq fun A => ?_
  have hclean := R.unsatFrac_killedPow_clean q T hq A hH hHT hsq hlam0 hlam1 hspec hn hq1 hloss
  have hc0 : 0 ≤ powConst q α := by
    rw [powConst]
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    apply div_nonneg <;> nlinarith
  have hT1 : (1 : ℝ) ≤ T := by
    have : 1 ≤ T := by omega
    exact_mod_cast this
  have hu0 : (0 : ℝ) ≤ ((R.unsatFrac (R.kDecode q T hq A) : ℚ) : ℝ) := by
    exact_mod_cast R.unsatFrac_nonneg _
  have hu1 : ((R.unsatFrac (R.kDecode q T hq A) : ℚ) : ℝ) ≤ 1 := by
    exact_mod_cast R.unsatFrac_le_one _
  have hv : ((R.unsatVal : ℚ) : ℝ) ≤ ((R.unsatFrac (R.kDecode q T hq A) : ℚ) : ℝ) := by
    exact_mod_cast R.unsatVal_le _
  refine le_trans ?_ (le_trans (min_le_powBound hc0 hT1 hlam1 hu0 hu1) hclean)
  refine min_le_min_right _ ?_
  have hs : 0 ≤ powSlope (powConst q α) T lam := by
    rw [powSlope]
    positivity
  exact mul_le_mul_of_nonneg_left hv hs

end RegCSP

/-! ### Choosing the parameters -/

/-- **Bernoulli, for the plurality loss.** With `m = 4 K (q - 1)`,
`4 K (q - 1)^m ≤ q^m`. -/
theorem four_mul_pow_le {K q : ℕ} (hK : 1 ≤ K) (hq : 2 ≤ q) :
    4 * K * (q - 1) ^ (4 * K * (q - 1)) ≤ q ^ (4 * K * (q - 1)) := by
  have hq1 : 1 ≤ q - 1 := by omega
  have hqr : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hpos : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by exact_mod_cast hq1
  set m := 4 * K * (q - 1) with hm
  have hbern : (1 : ℝ) + (m : ℝ) * (1 / ((q - 1 : ℕ) : ℝ))
      ≤ (1 + 1 / ((q - 1 : ℕ) : ℝ)) ^ m :=
    one_add_mul_le_pow (by linarith [one_div_nonneg.2 hpos.le]) m
  have hratio : (1 + 1 / ((q - 1 : ℕ) : ℝ)) = (q : ℝ) / ((q - 1 : ℕ) : ℝ) := by
    have hne : ((q - 1 : ℕ) : ℝ) ≠ 0 := hpos.ne'
    rw [eq_div_iff hne, add_mul, one_mul, one_div, inv_mul_cancel₀ hne, hqr]
    ring
  rw [hratio, div_pow] at hbern
  have hm' : (m : ℝ) * (1 / ((q - 1 : ℕ) : ℝ)) = 4 * K := by
    rw [hm]
    push_cast
    field_simp
  rw [hm'] at hbern
  have hpm : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) ^ m := by positivity
  rw [le_div_iff₀ hpm] at hbern
  have : (4 * K : ℝ) * ((q - 1 : ℕ) : ℝ) ^ m ≤ (q : ℝ) ^ m := by
    nlinarith
  exact_mod_cast this

/-- The truncation length used for powering: `8 K (q - 1)`. -/
def powT (K q : ℕ) : ℕ := 2 * (4 * K * (q - 1))

/-- The plurality threshold used for powering: `4 K (q - 1) - 1`. -/
def powH (K q : ℕ) : ℕ := 4 * K * (q - 1) - 1

/-- **Parameters for powering.** For `q ≥ 2` and alphabet size `K ≥ 1`, the
choices `powT` and `powH` meet every side condition of the powering bound, for
any degree. -/
theorem powering_params_spec {K q : ℕ} (hK : 1 ≤ K) (hq : 2 ≤ q) (d : ℕ) :
    2 * powH K q + 1 < powT K q ∧ powH K q + 1 ≤ powT K q
      ∧ (∀ i ∈ Finset.range (powH K q + 1), ∀ j ∈ Finset.range (powH K q + 1),
          i + j + 1 < powT K q)
      ∧ 2 * (K * RegCSP.pluralityLoss d q (powT K q) (powH K q))
          ≤ d ^ powT K q * q ^ powT K q := by
  set m := 4 * K * (q - 1) with hm
  have hm1 : 1 ≤ m := by
    rw [hm]
    have : 1 ≤ q - 1 := by omega
    nlinarith
  have hT : powT K q = 2 * m := rfl
  have hH : powH K q = m - 1 := rfl
  rw [hT, hH]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro i hi j hj
    rw [Finset.mem_range] at hi hj
    omega
  · have hHm : m - 1 + 1 = m := by omega
    rw [RegCSP.pluralityLoss, hHm]
    have hstar := four_mul_pow_le hK hq
    rw [← hm] at hstar
    have hT' : 2 * m - m = m := by omega
    rw [hT']
    have h1 : 4 * K * (q - 1) ^ (2 * m) ≤ q ^ (2 * m) := by
      have hpow : (q - 1) ^ (2 * m) = (q - 1) ^ m * (q - 1) ^ m := by
        rw [← pow_add]; congr 1; omega
      have hpow' : q ^ (2 * m) = q ^ m * q ^ m := by
        rw [← pow_add]; congr 1; omega
      rw [hpow, hpow']
      have hle : (q - 1) ^ m ≤ q ^ m := Nat.pow_le_pow_left (by omega) m
      calc 4 * K * ((q - 1) ^ m * (q - 1) ^ m) = (4 * K * (q - 1) ^ m) * (q - 1) ^ m := by ring
        _ ≤ q ^ m * q ^ m := Nat.mul_le_mul hstar hle
    have h2 : 4 * K * ((q - 1) ^ m * q ^ m) ≤ q ^ (2 * m) := by
      have hpow' : q ^ (2 * m) = q ^ m * q ^ m := by
        rw [← pow_add]; congr 1; omega
      rw [hpow']
      calc 4 * K * ((q - 1) ^ m * q ^ m) = (4 * K * (q - 1) ^ m) * q ^ m := by ring
        _ ≤ q ^ m * q ^ m := Nat.mul_le_mul_right _ hstar
    have hsum : 2 * (K * ((q - 1) ^ (2 * m) + (q - 1) ^ m * q ^ m)) ≤ q ^ (2 * m) := by
      nlinarith [h1, h2]
    calc 2 * (K * (d ^ (2 * m) * (q - 1) ^ (2 * m) + d ^ (2 * m) * ((q - 1) ^ m * q ^ m)))
        = d ^ (2 * m) * (2 * (K * ((q - 1) ^ (2 * m) + (q - 1) ^ m * q ^ m))) := by ring
      _ ≤ d ^ (2 * m) * q ^ (2 * m) := Nat.mul_le_mul_left _ hsum

/-- The per-unit slope: `powSlope` grows at least linearly in `q - 1`, with this
coefficient. -/
noncomputable def slopeUnit (K lam : ℝ) : ℝ :=
  1 / (16 * K ^ 4 * (1 / (4 * K ^ 2) + 2 + 16 * K / (1 - lam)))

/-- **The slope grows linearly in `q`.** -/
theorem slopeUnit_mul_le_powSlope {K : ℕ} {q : ℕ} (hK : 1 ≤ K) (hq : 2 ≤ q) {lam : ℝ}
    (hlam1 : lam < 1) :
    slopeUnit (K : ℝ) lam * ((q : ℝ) - 1)
      ≤ RegCSP.powSlope (((q : ℝ) - 1) / (4 * (K : ℝ) ^ 2)) (powT K q : ℝ) lam := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hTcast : (powT K q : ℝ) = 8 * K * ((q : ℝ) - 1) := by
    rw [powT, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hTcast, RegCSP.powSlope, slopeUnit]
  set r := (q : ℝ) - 1 with hr
  set D₀ : ℝ := 1 / (4 * (K : ℝ) ^ 2) + 2 + 16 * K / (1 - lam) with hD₀
  have hden : r / (4 * (K : ℝ) ^ 2) + 2 + 2 * (8 * K * r) / (1 - lam) ≤ r * D₀ := by
    rw [hD₀]
    have hx : r / (4 * (K : ℝ) ^ 2) = r * (1 / (4 * (K : ℝ) ^ 2)) := by ring
    have hy : 2 * (8 * K * r) / (1 - lam) = r * (16 * K / (1 - lam)) := by ring
    rw [hx, hy]
    linarith
  have hdenpos : 0 < r / (4 * (K : ℝ) ^ 2) + 2 + 2 * (8 * K * r) / (1 - lam) := by positivity
  calc 1 / (16 * (K : ℝ) ^ 4 * D₀) * r
      = (r / (4 * (K : ℝ) ^ 2)) ^ 2 / (r * D₀) := by
        field_simp
        ring
    _ ≤ (r / (4 * (K : ℝ) ^ 2)) ^ 2 / (r / (4 * (K : ℝ) ^ 2) + 2 + 2 * (8 * K * r) / (1 - lam)) :=
        div_le_div_of_nonneg_left (by positivity) hdenpos hden

end Complexity
