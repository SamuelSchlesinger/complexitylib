/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.AlgGap
public import Complexitylib.Classes.PCP.Internal.AlgInit
public import Complexitylib.Classes.PCP.Internal.AlgFormula
public import Complexitylib.Classes.PCP.Internal.AlgUniform

/-!
# The gap graph of an input

Everything the reduction does, in one function: read the formula, write its
constraint graph padded to a size the input's length decides, and amplify it as
many times as a logarithmic ruler is long.

## Main definitions

- `Complexity.gapAllG` — the graph itself
- `Complexity.gapAll` — that graph, as a string

## Main results

- `Complexity.gapAll_eq` — the string is the graph's encoding
- `Complexity.satisfiable_gapAllG` — completeness
- `Complexity.gap_le_unsatVal_gapAllG` — soundness
-/

@[expose] public section

set_option maxRecDepth 8000

namespace Complexity

open Dinur SAT

variable (F : FinBase) (hd : 1 < F.deg) (E padU : List Bool → List Bool)
  {Φ : List Bool → CNF}

/-- How many rounds an input gets: enough that the padded edge count is below
`2 ^ rounds`. -/
noncomputable def gapRuler (x : List Bool) : List Bool := logRuler (padU x)

theorem gapRuler_mem_FP (hpad : padU ∈ FP) : gapRuler padU ∈ FP :=
  mem_FP_of_eq (mem_FP_comp hpad logRuler_mem_FP) fun _ => rfl

@[simp] theorem length_gapRuler (x : List Bool) :
    (gapRuler padU x).length = rulerLen (padU x).length := by
  rw [gapRuler, length_logRuler]

/-- **The gap graph of an input.** -/
noncomputable def gapAllG (x : List Bool) : ConstraintGraph DinurAlpha :=
  (Dinur.step (F.toFamily hd) (qOf F hd) (qOf_pos F hd))^[rulerLen (padU x).length]
    ((baseCSP (Φ x)).padGraph (numVerts_baseCSP_pos (Φ x)) (padU x).length)

/-- **The gap graph of an input, as a string.** -/
noncomputable def gapAll : List Bool → List Bool :=
  gapFn F hd (basePadFn E padU baseCodeFn) (gapRuler padU)

theorem gapAll_eq (hE : ∀ x, E x = (Φ x).encode) (h3 : ∀ x, CNF.Is3CNF (Φ x))
    (hmark : ∀ x, padU x = List.replicate (padU x).length true)
    (hle : ∀ x, 3 * (Φ x).length ≤ (padU x).length) (x : List Bool) :
    gapAll F hd E padU x = encGraph (gapAllG F hd padU (Φ := Φ) x) := by
  rw [gapAll, gapFn_eq F hd (basePadFn_eq E hE h3 x (hmark x) (hle x)), gapAllG,
    length_gapRuler]

/-! ### The gap -/

theorem numEdges_padded_le (x : List Bool) (hle : 3 * (Φ x).length ≤ (padU x).length) :
    ((baseCSP (Φ x)).padGraph (numVerts_baseCSP_pos (Φ x)) (padU x).length).numEdges
      ≤ 2 ^ rulerLen (padU x).length := by
  rw [ConstraintGraph.numEdges_padGraph, numEdges_baseCSP, max_eq_left (by omega)]
  exact le_of_lt (lt_two_pow_rulerLen _)

/-- **Completeness.** -/
theorem satisfiable_gapAllG (h3 : ∀ x, CNF.Is3CNF (Φ x))
    (hle : ∀ x, 3 * (Φ x).length ≤ (padU x).length) (x : List Bool)
    (h : (Φ x).Satisfiable) : (gapAllG F hd padU (Φ := Φ) x).Satisfiable := by
  have hd' := (Amplifier.dichotomy (Dinur.amplifier (F.toFamily hd)) _
    (numEdges_padded_le padU x (hle x))).1
  rw [iter_amplifier] at hd'
  exact hd' (ConstraintGraph.satisfiable_padGraph_iff.mpr ((satisfiable_baseCSP_iff (h3 x)).mpr h))

/-- **Soundness.** -/
theorem gap_le_unsatVal_gapAllG (h3 : ∀ x, CNF.Is3CNF (Φ x))
    (hle : ∀ x, 3 * (Φ x).length ≤ (padU x).length) (x : List Bool)
    (h : ¬ (Φ x).Satisfiable) :
    (Dinur.amplifier (F.toFamily hd)).gap ≤ (gapAllG F hd padU (Φ := Φ) x).unsatVal := by
  have hd' := (Amplifier.dichotomy (Dinur.amplifier (F.toFamily hd)) _
    (numEdges_padded_le padU x (hle x))).2
  rw [iter_amplifier] at hd'
  exact hd' fun hs => h ((satisfiable_baseCSP_iff (h3 x)).mp
    (ConstraintGraph.satisfiable_padGraph_iff.mp hs))

/-! ### Writing it is polynomial-time -/

/-- The exponent by which the whole iteration can grow the graph. -/
noncomputable def growthExp : ℕ := rulerLen (edgeFactor (F.toFamily hd) (qOf F hd))

theorem pow_edgeFactor_le (m : ℕ) :
    edgeFactor (F.toFamily hd) (qOf F hd) ^ rulerLen m ≤ (2 * m + 1) ^ growthExp F hd := by
  calc edgeFactor (F.toFamily hd) (qOf F hd) ^ rulerLen m
      ≤ (2 ^ growthExp F hd) ^ rulerLen m :=
        Nat.pow_le_pow_left (le_of_lt (lt_two_pow_rulerLen _)) _
    _ = (2 ^ rulerLen m) ^ growthExp F hd := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (2 * m + 1) ^ growthExp F hd :=
        Nat.pow_le_pow_left (two_pow_rulerLen_le m) _

/-- How wide the iteration ever gets, as a function of the input's length. The
round's constants are parameters, so that no tactic here ever meets them. -/
def widthFn (p₀ q : Polynomial ℕ) (v cw d : ℕ) (n : ℕ) : ℕ :=
  2 * (2 * p₀.eval n + 1 + v * ((2 * q.eval n + 1) ^ d * q.eval n)) + 4
    + (2 * q.eval n + 1) ^ d * q.eval n
      * (8 * (2 * p₀.eval n + 1 + v * ((2 * q.eval n + 1) ^ d * q.eval n)) + cw)

theorem widthFn_hasRuler (p₀ q : Polynomial ℕ) (v cw d : ℕ) :
    HasRuler (widthFn p₀ q v cw d) := by
  have hm : HasRuler fun n => q.eval n := HasRuler.of_poly q
  have hV : HasRuler fun n => 2 * p₀.eval n + 1 :=
    HasRuler.add (HasRuler.mul (HasRuler.const 2) (HasRuler.of_poly p₀)) (HasRuler.const 1)
  have hB : HasRuler fun n => (2 * q.eval n + 1) ^ d :=
    HasRuler.pow (HasRuler.add (HasRuler.mul (HasRuler.const 2) hm) (HasRuler.const 1)) _
  have hBm := HasRuler.mul hB hm
  have hA := HasRuler.add hV (HasRuler.mul (HasRuler.const v) hBm)
  exact HasRuler.add (HasRuler.add (HasRuler.mul (HasRuler.const 2) hA) (HasRuler.const 4))
    (HasRuler.mul hBm (HasRuler.add (HasRuler.mul (HasRuler.const 8) hA) (HasRuler.const cw)))

set_option maxRecDepth 100000 in
/-- **Writing the gap graph is polynomial-time.** -/
theorem gapAll_mem_FP (hEfp : E ∈ FP) (hpad : padU ∈ FP)
    (hE : ∀ x, E x = (Φ x).encode) (h3 : ∀ x, CNF.Is3CNF (Φ x))
    (hmark : ∀ x, padU x = List.replicate (padU x).length true)
    (hle : ∀ x, 3 * (Φ x).length ≤ (padU x).length) (p₀ q : Polynomial ℕ)
    (hp₀ : ∀ x, (E x).length ≤ p₀.eval x.length)
    (hq : ∀ x, (padU x).length = q.eval x.length) :
    gapAll F hd E padU ∈ FP := by
  obtain ⟨R, hR, hRlen⟩ := widthFn_hasRuler p₀ q (vertFactor (F.toFamily hd) (qOf F hd))
    (4 * Fintype.card (DinurAlpha → DinurAlpha → Bool) + 10) (growthExp F hd)
  refine gapFn_mem_FP F hd (basePadFn_mem_FP E hEfp hpad _) (gapRuler_mem_FP padU hpad) hR
    (fun z => ⟨_, basePadFn_eq E hE h3 z (hmark z) (hle z)⟩) ?_
  intro z G hG n hn
  have hsame : encGraph G
      = encGraph ((baseCSP (Φ z)).padGraph (numVerts_baseCSP_pos (Φ z)) (padU z).length) := by
    rw [← hG, basePadFn_eq E hE h3 z (hmark z) (hle z)]
  have hV : G.numVerts
      = ((baseCSP (Φ z)).padGraph (numVerts_baseCSP_pos (Φ z)) (padU z).length).numVerts := by
    rw [← gVerts_encGraph (G := G), hsame, gVerts_encGraph]
  have hEd : G.numEdges
      = ((baseCSP (Φ z)).padGraph (numVerts_baseCSP_pos (Φ z)) (padU z).length).numEdges := by
    rw [← gEdges_encGraph (G := G), hsame, gEdges_encGraph]
  have hmq : G.numEdges = q.eval z.length := by
    rw [hEd, ConstraintGraph.numEdges_padGraph, numEdges_baseCSP,
      max_eq_left (by have := hle z; omega), hq]
  have hVle : G.numVerts ≤ 2 * p₀.eval z.length + 1 := by
    have h1 := CNF.maxVar_le_encode_length (Φ z)
    have h2 := length_le_length_encode (Φ z)
    have h3' := hp₀ z
    rw [hE z] at h3'
    have hvv : G.numVerts = (Φ z).maxVar + 1 + (Φ z).length := by
      rw [hV]
      rfl
    omega
  have hn' : n ≤ rulerLen (padU z).length := by
    rwa [length_gapRuler] at hn
  have hB : edgeFactor (F.toFamily hd) (qOf F hd) ^ rulerLen (padU z).length
      ≤ (2 * q.eval z.length + 1) ^ growthExp F hd := by
    rw [← hq]
    exact pow_edgeFactor_le F hd _
  refine le_trans (length_encGraph_iterStep_le'' F hd G n _ _ _ _ hn' hB hVle
    (le_of_eq hmq)) (le_trans (le_of_eq ?_) (hRlen z))
  rw [widthFn]
  ring

end Complexity
