/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Network

/-!
# Aggregate counting from a graph ordering bound

The graph ordering theorem controls the Boolean frontier, while the cardinality of the
finite commutative monoid contributes one multiplicative factor. Every input is read,
so the terminal-state term costs only one additional layer.
-/

@[expose] public section

namespace Algebraic.Cutwidth.AggregateNetwork

open scoped Classical

variable {n : Nat} {V E M : Type} [CommMonoid M] [Fintype V] [Fintype E] [Fintype M]
  [Nonempty V] (N : AggregateNetwork n V E M)

/-- A graph ordering bound gives the real-valued accepting-input bound with one aggregate
state factor. The vertex bound and edge-excess bound can be supplied by any compiler. -/
theorem card_accepting_le_of_orderingBound {A η C : ℝ} (hAη : 0 ≤ A + η) (hC : 0 ≤ C)
    (order : Multigraph.OrderingBound A η C)
    {f : Cslib.BooleanFunction n} (hf : N.Computes f) (hread : N.read = Finset.univ)
    (hloop : N.Loopless) (hdeg : N.MaxDegreeLE 3) (hconn : N.Connected)
    {s : Nat} {Vb : ℝ} (hV : (Fintype.card V : ℝ) ≤ Vb)
    (hdiff : (Fintype.card E : ℝ) - Fintype.card V ≤ (s : ℝ) - n)
    {K : Nat} (hK : 1 < K) (hrect : RectangleFree f K) :
    ((accepting f).card : ℝ) ≤
      (Vb * (2 : ℝ) ^ ((A + η) * max ((s : ℝ) - n) 0 +
        3 * Real.logb 2 Vb + C + 3) + 1) * Fintype.card M * K ^ 2 := by
  obtain ⟨inst, hcut⟩ := order V E N.toMultigraph hloop hdeg hconn
  let bound : ℝ := (A + η) * max ((Fintype.card E : ℝ) - Fintype.card V) 0 +
    3 * Real.logb 2 (Fintype.card V) + C
  have hVpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hVb0 : 0 ≤ Vb := (hVpos.trans_le hV).le
  have hlogV : 0 ≤ Real.logb 2 (Fintype.card V) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast Fintype.card_pos)
  have hbound0 : 0 ≤ bound := by
    have hmul := mul_nonneg hAη (le_max_right ((Fintype.card E : ℝ) - Fintype.card V) 0)
    dsimp [bound]
    linarith
  have hw : ∀ v, (N.cut (Network.below v)).card ≤ ⌊bound⌋₊ :=
    fun v => Nat.le_floor (hcut _ (Network.isLowerSet_below v))
  have hcount := N.card_accepting_le_of_read_eq_univ hf hread hdeg hw hK hrect
  have hbound : bound ≤ (A + η) * max ((s : ℝ) - n) 0 + 3 * Real.logb 2 Vb + C := by
    have h₁ := mul_le_mul_of_nonneg_left (max_le_max hdiff (le_refl (0 : ℝ))) hAη
    have h₂ := (Real.logb_le_logb one_lt_two hVpos (hVpos.trans_le hV)).mpr hV
    dsimp [bound]
    linarith
  have hexp : ((2 : ℝ) ^ (⌊bound⌋₊ + 3) : ℝ) ≤
      (2 : ℝ) ^ ((A + η) * max ((s : ℝ) - n) 0 + 3 * Real.logb 2 Vb + C + 3) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    push_cast
    linarith [Nat.floor_le hbound0]
  have hK' : (((K - 1 : Nat) : ℝ)) ^ 2 ≤ (K : ℝ) ^ 2 := by
    gcongr
    exact_mod_cast Nat.sub_le K 1
  calc ((accepting f).card : ℝ)
      ≤ ((Fintype.card V : ℝ) * (2 : ℝ) ^ (⌊bound⌋₊ + 3) + 1) * Fintype.card M *
          ((K - 1 : Nat) : ℝ) ^ 2 := by exact_mod_cast hcount
    _ ≤ (Vb * (2 : ℝ) ^ ((A + η) * max ((s : ℝ) - n) 0 +
          3 * Real.logb 2 Vb + C + 3) + 1) * Fintype.card M * K ^ 2 := by
      apply mul_le_mul _ hK' (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith [mul_le_mul hV hexp (by positivity) hVb0]

end Algebraic.Cutwidth.AggregateNetwork
