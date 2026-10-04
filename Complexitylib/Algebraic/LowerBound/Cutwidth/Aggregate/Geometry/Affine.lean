/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Pairing
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Coset

/-!
# The affine pairing bound for signed AND/OR/XOR circuits

The theorem constructs an actual nonempty monochromatic affine flat. Its gate
count consequence for sumset dispersers is unconditional on any geometric-saving
interface: the pairing and all restriction invariants are proved for the actual
acyclic program.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

open Algebraic.Cutwidth

/-- A sumset disperser requires twice its input length in gates plus the number of
multiple-primary conjunctions, up to twice its logarithmic source threshold. -/
theorem two_mul_input_le_size_add_multi {n g K : Nat}
    (p : Program signature n g) (out : Wire n g)
    (disperse : FlatSumsetDisperser (p.wireFunction interpretation out) K) :
    2 * n ≤ g + multiCount p + 2 * Nat.clog 2 K := by
  obtain ⟨S, d, mono, size, charge⟩ := exists_monochromatic_affine p out
  have small := S.card_lt_of_constant disperse mono
  have strict : 2 ^ n < 2 ^ (d + Nat.clog 2 K) := by
    rw [← size, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_left
      (small.trans_le (Nat.le_pow_clog (by decide) K)) (Nat.two_pow_pos d)
  have exponent : n < d + Nat.clog 2 K :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : Nat))).mp strict
  lia

end Algebraic.Aggregate.Geometry
