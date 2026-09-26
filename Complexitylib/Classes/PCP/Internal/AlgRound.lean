/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.AlgEdge
public import Complexitylib.Classes.PCP.Internal.GapReduction

/-!
# One round, uniformly

`AlgEdge.stepFn_eq` computes a round of amplification for a graph whose sizes
match the constants it is given. Iterating a round needs more: *one* function
that is right for *every* graph. This module supplies the constants that do not
depend on the graph — the walk length, the degree, the tester's counts — and
specialises the round to them.

The one fact that makes this possible is that the encoding a round composes with
does not depend on the graph either: the walks it is defined on are
`PreWalk E T`, whose type is fixed by the expander family alone.

## Main definitions

- `Complexity.roundOf` — the round's constants
- `Complexity.roundFn` — the round, as one `FP` function

## Main results

- `Complexity.roundFn_eq` — it computes a round of amplification, for every
  graph
-/

@[expose] public section

set_option maxRecDepth 8000

namespace Complexity

open Dinur Tester BooleanAnalysis

variable (F : FinBase) (hd : 1 < F.deg)

/-! ### The constants -/

/-- The killing rate a round uses. -/
noncomputable def qOf : ℕ := q₀ (F.toFamily hd)

theorem qOf_pos : 0 < qOf F hd := by
  have h := two_le_q₀ (F.toFamily hd)
  show 0 < q₀ (F.toFamily hd)
  omega

/-- The walk length a round uses. -/
noncomputable def walkLen : ℕ := powT K (qOf F hd)

/-- How many random strings the tester has. -/
noncomputable def cZOf : ℕ := 2 ^ ROf (bits (F.toFamily hd) (walkLen F hd))

/-- How many constraints the alphabet has. -/
noncomputable def cRel : ℕ := Fintype.card (DinurAlpha → DinurAlpha → Bool)

theorem cRel_eq : cRel = Fintype.card (DinurAlpha → DinurAlpha → Bool) := rfl

theorem cRel_pos : 0 < cRel := Fintype.card_pos

/-- The round's constants. -/
noncomputable def roundOf : Round :=
  dinurRound F hd (qOf F hd) cRel (cZOf F hd)

theorem roundOf_q : (roundOf F hd).q = qOf F hd :=
  dinurRound_q F hd (qOf F hd) cRel (cZOf F hd)

theorem roundOf_T : (roundOf F hd).T = walkLen F hd :=
  dinurRound_T F hd (qOf F hd) cRel (cZOf F hd)

theorem roundOf_C : (roundOf F hd).C = cRel :=
  dinurRound_C F hd (qOf F hd) cRel (cZOf F hd)

theorem roundOf_cZ : (roundOf F hd).cZ = cZOf F hd :=
  dinurRound_cZ F hd (qOf F hd) cRel (cZOf F hd)

theorem roundOf_deg : (roundOf F hd).deg = (F.toFamily hd).degree :=
  dinurRound_deg F hd (qOf F hd) cRel (cZOf F hd)

theorem roundOf_P (G : ConstraintGraph DinurAlpha) :
    (roundOf F hd).P = G.preDeg (F.toFamily hd) :=
  dinurRound_P F hd (qOf F hd) cRel (cZOf F hd) G

theorem roundOf_cQ : (roundOf F hd).cQ = qOf F hd ^ walkLen F hd :=
  dinurRound_cQ F hd (qOf F hd) cRel (cZOf F hd)

/-- A key to fall back on, for arguments that name no edge. -/
noncomputable def dfltKey : StepKey (F.toFamily hd) (roundOf F hd).T (roundOf F hd).q
    (bits (F.toFamily hd) (roundOf F hd).T)
    (Fintype.card (DinurAlpha → DinurAlpha → Bool)) :=
  ⟨⟨fun _ => Sum.inl (), fun _ => ⟨0, qOf_pos F hd⟩⟩,
    ⟨fun _ => 0, fun _ => ⟨0, Fintype.card_pos⟩⟩,
    ⟨fun _ => Sum.inl (), ⟨0, ReadIdx.f1x⟩⟩⟩

/-- The encoding a round composes with. It is written at a graph, but does not
depend on it: the walks are those of the expander family. -/
noncomputable def encOf : (PreWalk (F.toFamily hd) (roundOf F hd).T → DinurAlpha) →
    Cube (bits (F.toFamily hd) (roundOf F hd).T) :=
  Dinur.enc (F.toFamily hd) (baseCSP []) (roundOf F hd).T

theorem encOf_eq (G : ConstraintGraph DinurAlpha) :
    encOf F hd = Dinur.enc (F.toFamily hd) G (roundOf F hd).T := rfl

/-! ### The round -/

/-- **A round of amplification, as one function.** -/
noncomputable def roundFn : List Bool → List Bool :=
  stepFn F (2 * Polynomial.X) (roundOf F hd)
    (vertFactor (F.toFamily hd) (qOf F hd))
    (edgeFactor (F.toFamily hd) (qOf F hd))
    (posFactor (F.toFamily hd) (qOf F hd))
    (NumEnc.card (Cube (bits (F.toFamily hd) (roundOf F hd).T)))
    (NumEnc.card (Cube (nOf (bits (F.toFamily hd) (roundOf F hd).T))))
    (NumEnc.card (Cube (nOf (bits (F.toFamily hd) (roundOf F hd).T)
      * nOf (bits (F.toFamily hd) (roundOf F hd).T))))
    (dfltKey F hd) (encOf F hd)

theorem roundOf_cQ_pos : 0 < (roundOf F hd).cQ := by
  rw [roundOf_cQ]
  exact Nat.pow_pos (qOf_pos F hd)

theorem roundOf_cD_pos : 0 < (roundOf F hd).cD := by
  rw [Round.cD, roundOf_q, roundOf_P F hd (baseCSP []), roundOf_T]
  exact Nat.mul_pos (Nat.pow_pos ((baseCSP []).preDeg_pos (F.toFamily hd)))
    (Nat.pow_pos (qOf_pos F hd))

theorem roundOf_cZ_pos : 0 < (roundOf F hd).cZ := by
  rw [roundOf_cZ, cZOf]
  exact Nat.two_pow_pos _

theorem roundOf_C_pos : 0 < (roundOf F hd).C := by
  rw [roundOf_C]
  exact cRel_pos

theorem roundFn_mem_FP : roundFn F hd ∈ FP :=
  stepFn_mem_FP F (2 * Polynomial.X) (roundOf F hd) _ _ _ _ _ _
    (roundOf_cQ_pos F hd) (roundOf_cD_pos F hd) (roundOf_cZ_pos F hd) (roundOf_C_pos F hd)
    (dfltKey F hd) (encOf F hd)

/-- **The round computes a round of amplification, for every graph.** -/
theorem roundFn_eq (G : ConstraintGraph DinurAlpha) :
    roundFn F hd (encGraph G)
      = encGraph (Dinur.step (F.toFamily hd) (qOf F hd) (qOf_pos F hd) G) := by
  have hq : 0 < (roundOf F hd).q := by
    rw [roundOf_q]
    exact qOf_pos F hd
  have hpol : ∀ n : ℕ, F.fitLevel hd n ≤ (2 * Polynomial.X : Polynomial ℕ).eval n := by
    intro n
    simpa using F.fitLevel_le hd n
  have hrD : (roundOf F hd).cD
      = NumEnc.card ((G.preprocess (F.toFamily hd)).killedPow
          (roundOf F hd).q (roundOf F hd).T hq).graph.D := by
    rw [NumEnc.card_eq_fintype_card, RegCSP.graph_killedPow]
    show _ = ((G.preprocess (F.toFamily hd)).graph.killedPower
      (roundOf F hd).q (roundOf F hd).T hq).deg
    rw [RegGraph.deg_killedPower, G.deg_preprocess, Round.cD, roundOf_P F hd G,
      G.preDeg_eq (F.toFamily hd)]
  have hrZ : (roundOf F hd).cZ
      = 2 ^ ROf (bits (F.toFamily hd) (roundOf F hd).T) := by
    rw [roundOf_cZ, roundOf_T, cZOf]
  refine stepFn_eq F (2 * Polynomial.X) hd G (roundOf F hd) hq _ _ _ _ _ _
    hrD hrZ (roundOf_deg F hd) (roundOf_P F hd G) ((roundOf_C F hd).trans cRel_eq)
    ?_ ?_ ?_ ?_ rfl rfl rfl ?_ (dfltKey F hd)
  · exact fun u => hpol _
  · exact hpol _
  · exact Dinur.numVerts_step (F.toFamily hd) _ hq G
  · exact Dinur.numEdges_step (F.toFamily hd) _ hq G
  · exact (Dinur.card_pos_step (F.toFamily hd) _ hq G).trans (Nat.mul_comm _ _)

end Complexity
