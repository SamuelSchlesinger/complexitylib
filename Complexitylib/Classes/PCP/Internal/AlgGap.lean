/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.AlgRound
public import Complexitylib.Classes.PCP.Internal.AlgLog

/-!
# Amplifying, logarithmically many times

`AlgRound` computes one round. Dinur's theorem runs logarithmically many, so
this module iterates that function and bounds the size of what it writes: each
round multiplies the edge count by a constant, so after `n` rounds the graph is
`edgeFactor ^ n` times as large, and the ruler keeps `n` logarithmic.

## Main definitions

- `Complexity.gapFn` — the amplified graph, as a string

## Main results

- `Complexity.numEdges_iterStep` — a round's edge count, exactly
- `Complexity.length_encGraph_iterStep_le` — the size of what is written
- `Complexity.gapFn_eq` — it writes the amplifier's iterate
-/

@[expose] public section

set_option maxRecDepth 8000

namespace Complexity

open Dinur Tester

variable (F : FinBase) (hd : 1 < F.deg)

/-! ### The sizes of an iterate -/

theorem numEdges_iterStep (G : ConstraintGraph DinurAlpha) (n : ℕ) :
    ((Dinur.step (F.toFamily hd) (qOf F hd) (qOf_pos F hd))^[n] G).numEdges
      = edgeFactor (F.toFamily hd) (qOf F hd) ^ n * G.numEdges := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Dinur.numEdges_step, ih, pow_succ]
      ring

theorem one_le_edgeFactor : 1 ≤ edgeFactor (F.toFamily hd) (qOf F hd) := by
  rw [edgeFactor]
  have h1 : 0 < powDeg (F.toFamily hd) ^ powT K (qOf F hd) * qOf F hd ^ powT K (qOf F hd) :=
    Nat.mul_pos (Nat.pow_pos (by rw [powDeg]; omega)) (Nat.pow_pos (qOf_pos F hd))
  have h2 : 0 < 2 ^ ROf (bits (F.toFamily hd) (powT K (qOf F hd))) := Nat.two_pow_pos _
  have := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega : 0 < 2) h1) h2) (by omega : 0 < 22)
  omega

theorem numVerts_iterStep_le (G : ConstraintGraph DinurAlpha) (n : ℕ) :
    ((Dinur.step (F.toFamily hd) (qOf F hd) (qOf_pos F hd))^[n] G).numVerts
      ≤ G.numVerts + vertFactor (F.toFamily hd) (qOf F hd)
          * (edgeFactor (F.toFamily hd) (qOf F hd) ^ n * G.numEdges) := by
  cases n with
  | zero => simp
  | succ n =>
      rw [Function.iterate_succ_apply', Dinur.numVerts_step, numEdges_iterStep]
      refine le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ?_)) (Nat.le_add_left _ _)
      exact Nat.pow_le_pow_right (one_le_edgeFactor F hd) (Nat.le_succ n)

theorem size_mono {V V' E E' C : ℕ} (h : V' ≤ V) (hE : E' ≤ E) :
    2 * V' + 4 + E' * (8 * V' + 4 * C + 10) ≤ 2 * V + 4 + E * (8 * V + 4 * C + 10) := by
  have h1 : 8 * V' + 4 * C + 10 ≤ 8 * V + 4 * C + 10 := by omega
  have h2 := Nat.mul_le_mul hE h1
  omega

/-- **The size of what a round writes.** -/
theorem length_encGraph_iterStep_le (G : ConstraintGraph DinurAlpha) (n : ℕ) :
    (encGraph ((Dinur.step (F.toFamily hd) (qOf F hd) (qOf_pos F hd))^[n] G)).length
      ≤ 2 * (G.numVerts + vertFactor (F.toFamily hd) (qOf F hd)
            * (edgeFactor (F.toFamily hd) (qOf F hd) ^ n * G.numEdges)) + 4
        + edgeFactor (F.toFamily hd) (qOf F hd) ^ n * G.numEdges
          * (8 * (G.numVerts + vertFactor (F.toFamily hd) (qOf F hd)
              * (edgeFactor (F.toFamily hd) (qOf F hd) ^ n * G.numEdges))
            + 4 * Fintype.card (DinurAlpha → DinurAlpha → Bool) + 10) := by
  have hV := numVerts_iterStep_le F hd G n
  have hE := numEdges_iterStep F hd G n
  refine le_trans (length_encGraph_le _) ?_
  rw [hE]
  exact size_mono hV (le_refl _)

/-- **The size of what a round writes**, in terms of a bound on the growth
factor, so that one bound serves every round of the iteration. -/
theorem length_encGraph_iterStep_le' (G : ConstraintGraph DinurAlpha) (n r B : ℕ)
    (hn : n ≤ r) (hB : edgeFactor (F.toFamily hd) (qOf F hd) ^ r ≤ B) :
    (encGraph ((Dinur.step (F.toFamily hd) (qOf F hd) (qOf_pos F hd))^[n] G)).length
      ≤ 2 * (G.numVerts + vertFactor (F.toFamily hd) (qOf F hd) * (B * G.numEdges)) + 4
        + B * G.numEdges
          * (8 * (G.numVerts + vertFactor (F.toFamily hd) (qOf F hd) * (B * G.numEdges))
            + 4 * Fintype.card (DinurAlpha → DinurAlpha → Bool) + 10) := by
  have hpow : edgeFactor (F.toFamily hd) (qOf F hd) ^ n ≤ B :=
    le_trans (Nat.pow_le_pow_right (one_le_edgeFactor F hd) hn) hB
  have hV : ((Dinur.step (F.toFamily hd) (qOf F hd) (qOf_pos F hd))^[n] G).numVerts
      ≤ G.numVerts + vertFactor (F.toFamily hd) (qOf F hd) * (B * G.numEdges) :=
    le_trans (numVerts_iterStep_le F hd G n)
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpow)) _)
  have hE : ((Dinur.step (F.toFamily hd) (qOf F hd) (qOf_pos F hd))^[n] G).numEdges
      ≤ B * G.numEdges := by
    rw [numEdges_iterStep]
    exact Nat.mul_le_mul_right _ hpow
  exact le_trans (length_encGraph_le _) (size_mono hV hE)

/-- The amplifier's round is the round the algorithm computes. -/
theorem transform_amplifier :
    (Dinur.amplifier (F.toFamily hd)).transform
      = Dinur.step (F.toFamily hd) (qOf F hd) (qOf_pos F hd) := by
  dsimp only [Dinur.amplifier, qOf]

/-- **So the amplifier's iterate is the algorithm's.** -/
theorem iter_amplifier (G : ConstraintGraph DinurAlpha) (k : ℕ) :
    (Dinur.amplifier (F.toFamily hd)).iter k G
      = (Dinur.step (F.toFamily hd) (qOf F hd) (qOf_pos F hd))^[k] G := by
  rw [Amplifier.iter, transform_amplifier]

/-- **The size of what a round writes**, from numeric bounds alone: a caller
supplies bounds on the graph it starts from and on the growth factor. -/
theorem length_encGraph_iterStep_le'' (G : ConstraintGraph DinurAlpha) (n r B V m : ℕ)
    (hn : n ≤ r) (hB : edgeFactor (F.toFamily hd) (qOf F hd) ^ r ≤ B)
    (hV : G.numVerts ≤ V) (hm : G.numEdges ≤ m) :
    (encGraph ((Dinur.step (F.toFamily hd) (qOf F hd) (qOf_pos F hd))^[n] G)).length
      ≤ 2 * (V + vertFactor (F.toFamily hd) (qOf F hd) * (B * m)) + 4
        + B * m
          * (8 * (V + vertFactor (F.toFamily hd) (qOf F hd) * (B * m))
            + 4 * Fintype.card (DinurAlpha → DinurAlpha → Bool) + 10) := by
  refine le_trans (length_encGraph_iterStep_le' F hd G n r B hn hB) (size_mono ?_ ?_)
  · exact Nat.add_le_add hV (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hm))
  · exact Nat.mul_le_mul_left _ hm

/-! ### The iteration -/

/-- **The amplified graph, as a string**: as many rounds as the ruler is long. -/
noncomputable def gapFn (init ruler : List Bool → List Bool) (z : List Bool) : List Bool :=
  (roundFn F hd)^[(ruler z).length] (init z)

/-- **What it writes**: the amplifier's iterate on whatever graph the start
writes. -/
theorem gapFn_eq {init ruler : List Bool → List Bool} {z : List Bool}
    {G : ConstraintGraph DinurAlpha} (h : init z = encGraph G) :
    gapFn F hd init ruler z
      = encGraph ((Dinur.step (F.toFamily hd) (qOf F hd) (qOf_pos F hd))^[(ruler z).length] G) := by
  rw [gapFn, h]
  exact ((Function.Semiconj.iterate_right (f := encGraph)
    (fun G => (roundFn_eq F hd G).symm) _) G).symm

/-- **And writing it is polynomial-time.** -/
theorem gapFn_mem_FP {init ruler width : List Bool → List Bool}
    (hinit : init ∈ FP) (hruler : ruler ∈ FP) (hwidth : width ∈ FP)
    (hinitG : ∀ z, ∃ G : ConstraintGraph DinurAlpha, init z = encGraph G)
    (hbound : ∀ (z : List Bool) (G : ConstraintGraph DinurAlpha), init z = encGraph G →
      ∀ n ≤ (ruler z).length,
        (encGraph ((Dinur.step (F.toFamily hd) (qOf F hd) (qOf_pos F hd))^[n] G)).length
          ≤ (width z).length) :
    gapFn F hd init ruler ∈ FP :=
  iterate_mem_FP_along encGraph (roundFn_mem_FP F hd) hinit hruler hwidth
    (roundFn_eq F hd) hinitG hbound

end Complexity
