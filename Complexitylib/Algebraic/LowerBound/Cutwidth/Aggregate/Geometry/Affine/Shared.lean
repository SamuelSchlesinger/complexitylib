/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Shared.Count
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Shared.Preprocess
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Coset

/-!
# Affine savings from shared primary controls

Gate-disjoint pairs of exact-two-primary conjunctions sharing a variable save one
additional unit each in the affine codimension charge. A maximal pairing leaves
at most half the input count unpaired. All statements concern actual circuits,
with no restriction on fan-in, fanout, depth, literal repetitions, or internal inputs.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Shared

open Algebraic.Cutwidth
open scoped Classical

variable {n g : Nat}

/-- Preprocessing shared primary controls improves the actual affine restriction
charge by one unit per gate-disjoint intersecting pair. -/
theorem PrimaryPairing.exists_affine_restriction (p : Program signature n g)
    (P : PrimaryPairing p) :
    ∃ (S : AffineFlat n) (d : Nat),
      (∀ i, AffineOn S (p.gateFunction interpretation i)) ∧
      2 ^ d * S.carrier.card = 2 ^ n ∧
      2 * d + P.pairs.card ≤ g + multiCount p := by
  classical
  obtain ⟨S, d, size, pairs, killed, shared⟩ := P.exists_preprocess p
  let fixed := Finset.univ.filter fun i => ConstantOn S (fun x => x i)
  have fixedOn : ∀ i ∈ fixed, ConstantOn S (fun x => x i) :=
    fun _ hi => (Finset.mem_filter.mp hi).2
  have markBound : remainingCount p fixed + 2 * P.pairs.card ≤ multiCount p := by
    apply P.remainingCount_add_le p fixed
    intro e he
    obtain ⟨j, left, right, constant⟩ := shared e he
    exact ⟨j, left, right, Finset.mem_filter.mpr ⟨Finset.mem_univ _, constant⟩⟩
  obtain ⟨T, e, _, affine, relativeSize, charge⟩ :=
    Shared.exists_affine_restriction p S fixed fixedOn
  refine ⟨T, d + e, affine, ?_, ?_⟩
  · rw [Nat.pow_add, Nat.mul_assoc, relativeSize, size]
  · have count := constantCount_le p T
    lia

/-- Fixing the final affine output costs at most one further equation. -/
theorem PrimaryPairing.exists_monochromatic_affine (p : Program signature n g)
    (P : PrimaryPairing p) (out : Wire n g) :
    ∃ (S : AffineFlat n) (d : Nat), ConstantOn S (p.wireFunction interpretation out) ∧
      2 ^ d * S.carrier.card = 2 ^ n ∧
      2 * d + P.pairs.card ≤ g + multiCount p + 2 := by
  obtain ⟨S, d, affine, size, charge⟩ := P.exists_affine_restriction p
  by_cases constant : ConstantOn S (p.wireFunction interpretation out)
  · exact ⟨S, d, constant, size, by lia⟩
  · obtain ⟨T, _, value, half⟩ := (affineOn_wire p affine out).exists_half constant false
    refine ⟨T, d + 1, ⟨false, value⟩, ?_, by lia⟩
    rw [Nat.pow_succ, Nat.mul_assoc, half, size]

/-- A sumset disperser pays one extra affine-charge unit for each shared-control pair. -/
theorem PrimaryPairing.two_mul_input_add_pairs_le (p : Program signature n g)
    (P : PrimaryPairing p) (out : Wire n g) {K : Nat}
    (disperse : FlatSumsetDisperser (p.wireFunction interpretation out) K) :
    2 * n + P.pairs.card ≤ g + multiCount p + 2 * Nat.clog 2 K := by
  obtain ⟨S, d, mono, size, charge⟩ := P.exists_monochromatic_affine p out
  have small := S.card_lt_of_constant disperse mono
  have strict : 2 ^ n < 2 ^ (d + Nat.clog 2 K) := by
    rw [← size, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_left
      (small.trans_le (Nat.le_pow_clog (by decide) K)) (Nat.two_pow_pos d)
  have exponent : n < d + Nat.clog 2 K :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : Nat))).mp strict
  lia

/-- Eliminating the finite matching parameter gives a stronger geometric inequality
in the actual total and exact-two-primary gate counts. -/
theorem seven_mul_input_add_two_mul_exactTwo_le (p : Program signature n g)
    (out : Wire n g) {K : Nat}
    (disperse : FlatSumsetDisperser (p.wireFunction interpretation out) K) :
    7 * n + 2 * (exactTwo p).card ≤ 4 * g + 4 * multiCount p + 8 * Nat.clog 2 K := by
  obtain ⟨P, matching⟩ := exists_pairing_two_mul_le p
  have geometry := P.two_mul_input_add_pairs_le p out disperse
  lia

end Algebraic.Aggregate.Geometry.Shared
