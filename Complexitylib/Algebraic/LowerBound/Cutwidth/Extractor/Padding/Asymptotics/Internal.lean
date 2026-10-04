/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Nondeterministic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding

/-!
# Transporting balanced padding through the asymptotic lower bound

Doubling a source threshold and shifting its index preserve a sublinear
binary logarithm. At each positive length, the padded extractor gives a
rectangle-free function accepting exactly half the inputs. The graph-free
circuit theorems therefore apply to one fixed padded family, as do the
theorems with a general graph-ordering coefficient.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical
open Filter

private def paddedFamily (f : ∀ n, Cslib.BooleanFunction n) : ∀ n, Cslib.BooleanFunction n
  | 0 => fun _ => false
  | n + 1 => balancePad (f n)

private theorem logb_two_mul_shift_isLittleO {K : Nat → Nat}
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ))) :
    (fun n => Real.logb 2 (2 * K (n - 1) : Nat)) =o[atTop] (fun n => (n : ℝ)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro δ hδ
  filter_upwards [(tendsto_sub_atTop_nat 1).eventually (hK.def (by positivity : 0 < δ / 2)),
    eventually_mul_logb_add_lt 0 1 (by positivity : 0 < δ / 2)] with n small constant
  by_cases zero : K (n - 1) = 0
  · simp only [zero, mul_zero, Nat.cast_zero, Real.logb_zero, norm_zero]
    positivity
  have positive : (0 : ℝ) < K (n - 1) := by exact_mod_cast Nat.pos_of_ne_zero zero
  have nonneg : 0 ≤ Real.logb 2 (K (n - 1)) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr zero)
  have smallLog : Real.logb 2 (K (n - 1)) ≤ δ / 2 * (n - 1 : Nat) := by
    simpa only [Real.norm_of_nonneg nonneg,
      Real.norm_of_nonneg (Nat.cast_nonneg (α := ℝ) (n - 1))] using small
  have shift : ((n - 1 : Nat) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  have smallLog' := smallLog.trans (mul_le_mul_of_nonneg_left shift (by positivity : 0 ≤ δ / 2))
  have constant' : (1 : ℝ) ≤ δ / 2 * n := by
    simpa only [zero_mul, zero_add] using constant.le
  have doubled : Real.logb 2 ((2 * K (n - 1) : Nat) : ℝ) =
      1 + Real.logb 2 (K (n - 1)) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.logb_mul (by norm_num) positive.ne',
      Real.logb_self_eq_one one_lt_two]
  rw [doubled, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  linarith

private theorem eventually_hard_paddedFamily
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) {ν : ℝ} (hν : ν < 1 / 2)
    (positive : ∀ᶠ n in atTop, 0 < K n)
    (extract : ∀ᶠ n in atTop, FlatSumsetExtractor (f n) (K n) ν) :
    ∀ᶠ n in atTop, RectangleFree (paddedFamily f n) (2 * K (n - 1)) ∧
      2 ^ (n - 2) ≤ (accepting (paddedFamily f n)).card := by
  filter_upwards [(tendsto_sub_atTop_nat 1).eventually positive,
    (tendsto_sub_atTop_nat 1).eventually extract, eventually_ge_atTop 1]
    with n hn hnExtract hn1
  cases n with
  | zero => lia
  | succ n =>
    refine ⟨?_, ?_⟩
    · exact hnExtract.balancePad_rectangleFree hn hν
    · rw [paddedFamily, card_accepting_balancePad]
      exact Nat.pow_le_pow_right two_pos (by lia)

theorem eventually_lt_size_balancePad_of_flatSumsetExtractor_of_orderingBound {A : ℝ}
    (hA : 0 < A) (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) {ν : ℝ} (hν : ν < 1 / 2)
    (positive : ∀ᶠ n in atTop, 0 < K n)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (extract : ∀ᶠ n in atTop, FlatSumsetExtractor (f n) (K n) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature (n + 1) 1,
      circuit.Computes Binary.interpretation (fun x _ => balancePad (f n) x) →
        (1 + 1 / A - ε) * (n + 1) < circuit.size := by
  have hard := eventually_hard_paddedFamily f K hν positive extract
  have bound := eventually_lt_size_of_orderingBound hA order (paddedFamily f)
    (fun n => 2 * K (n - 1)) (logb_two_mul_shift_isLittleO hK) (hard.mono fun _ h => h.2)
    (hard.mono fun _ h => h.1) hε
  filter_upwards [(tendsto_add_atTop_nat 1).eventually bound] with n hn
  simpa only [paddedFamily, Nat.cast_add, Nat.cast_one] using hn

theorem nondet_eventually_lt_size_balancePad_of_flatSumsetExtractor_of_orderingBound {A : ℝ}
    (hA : 0 < A) (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) {ν : ℝ} (hν : ν < 1 / 2)
    (positive : ∀ᶠ n in atTop, 0 < K n)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (extract : ∀ᶠ n in atTop, FlatSumsetExtractor (f n) (K n) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (m : Nat) (circuit : Circuit Binary.signature (n + 1 + m) 1),
      NondetComputes circuit (balancePad (f n)) → (1 + 1 / A - ε) * (n + 1) < circuit.size := by
  have hard := eventually_hard_paddedFamily f K hν positive extract
  have bound := nondet_eventually_lt_size_of_orderingBound hA order (paddedFamily f)
    (fun n => 2 * K (n - 1)) (logb_two_mul_shift_isLittleO hK)
    (hard.mono fun _ h => h.2) (hard.mono fun _ h => h.1) hε
  filter_upwards [(tendsto_add_atTop_nat 1).eventually bound] with n hn
  simpa only [paddedFamily, Nat.cast_add, Nat.cast_one] using hn

theorem eventually_lt_size_balancePad_of_flatSumsetExtractor
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) {ν : ℝ} (hν : ν < 1 / 2)
    (positive : ∀ᶠ n in atTop, 0 < K n)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (extract : ∀ᶠ n in atTop, FlatSumsetExtractor (f n) (K n) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature (n + 1) 1,
      circuit.Computes Binary.interpretation (fun x _ => balancePad (f n) x) →
        (4 - ε) * (n + 1) < circuit.size := by
  have hard := eventually_hard_paddedFamily f K hν positive extract
  have bound := eventually_lt_size_of_rectangleFree (paddedFamily f) (fun n => 2 * K (n - 1))
    (logb_two_mul_shift_isLittleO hK) (hard.mono fun _ h => h.2)
    (hard.mono fun _ h => h.1) hε
  filter_upwards [(tendsto_add_atTop_nat 1).eventually bound] with n hn
  simpa only [paddedFamily, Nat.cast_add, Nat.cast_one] using hn

theorem nondet_eventually_lt_size_balancePad_of_flatSumsetExtractor
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) {ν : ℝ} (hν : ν < 1 / 2)
    (positive : ∀ᶠ n in atTop, 0 < K n)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (extract : ∀ᶠ n in atTop, FlatSumsetExtractor (f n) (K n) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (m : Nat) (circuit : Circuit Binary.signature (n + 1 + m) 1),
      NondetComputes circuit (balancePad (f n)) → (4 - ε) * (n + 1) < circuit.size := by
  have hard := eventually_hard_paddedFamily f K hν positive extract
  have bound := nondet_eventually_lt_size_of_rectangleFree (paddedFamily f)
    (fun n => 2 * K (n - 1)) (logb_two_mul_shift_isLittleO hK)
    (hard.mono fun _ h => h.2) (hard.mono fun _ h => h.1) hε
  filter_upwards [(tendsto_add_atTop_nat 1).eventually bound] with n hn
  simpa only [paddedFamily, Nat.cast_add, Nat.cast_one] using hn

end Algebraic.Cutwidth.Extractor.Internal
