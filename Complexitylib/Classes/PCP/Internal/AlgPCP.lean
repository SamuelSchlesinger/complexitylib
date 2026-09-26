/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.AlgGapCSP
public import Complexitylib.Classes.PCP.Internal.SquareVerifier

/-!
# Every NP language has a PCP verifier

The pieces are all in place: an `NP` language is the satisfiability of an `FP`
family of 3-CNFs, the gap reduction turns each into a constraint graph with a
constant gap, that graph is written by an `FP` function, and a verifier reading
one edge of it accepts members always and non-members with probability bounded
away from one.

## Main definitions

- `Complexity.gapNumEdges` — how many edges the gap graph of a length has

## Main results

- `Complexity.exists_pcp_of_mem_NP` — the hard half of the PCP theorem
-/

@[expose] public section

set_option maxRecDepth 8000

namespace Complexity

open SAT Dinur

/-- The finite base the reduction's expander family comes from. -/
noncomputable def algF : FinBase := algBase

theorem algHd : 1 < algF.deg := one_lt_algBase_deg

/-- How many edges the gap graph of an input of length `n` has: the padded
count, multiplied by the round's factor once per round. -/
noncomputable def gapNumEdges (q : Polynomial ℕ) (n : ℕ) : ℕ :=
  edgeFactor (algF.toFamily algHd) (qOf algF algHd) ^ rulerLen (q.eval n) * q.eval n

theorem gapNumEdges_pos {q : Polynomial ℕ} {n : ℕ} (hq : 0 < q.eval n) :
    0 < gapNumEdges q n :=
  Nat.mul_pos (Nat.pow_pos (one_le_edgeFactor algF algHd)) hq

/-- The gap graph's size is polynomial in the input's length. -/
theorem gapNumEdges_polyBounded (q : Polynomial ℕ) : PolyBounded (gapNumEdges q) := by
  have hq : PolyBounded fun n => q.eval n := polyBounded_eval q
  refine PolyBounded.mono (PolyBounded.mul
    (PolyBounded.pow (PolyBounded.add (PolyBounded.mul (PolyBounded.const 2) hq)
      (PolyBounded.const 1)) (growthExp algF algHd)) hq) fun n => ?_
  exact Nat.mul_le_mul_right _ (pow_edgeFactor_le algF algHd (q.eval n))

/-- **The coin count**: enough for the gap graph's edges, and no more than one
too many. -/
noncomputable def gapCoins (q : Polynomial ℕ) (n : ℕ) : ℕ := rulerLen (gapNumEdges q n)

theorem le_two_pow_gapCoins (q : Polynomial ℕ) (n : ℕ) :
    gapNumEdges q n ≤ 2 ^ gapCoins q n :=
  le_of_lt (lt_two_pow_rulerLen _)

theorem two_pow_gapCoins_le {q : Polynomial ℕ} {n : ℕ} (hq : 0 < q.eval n) :
    2 ^ gapCoins q n ≤ 2 * gapNumEdges q n := by
  have hpos := gapNumEdges_pos (q := q) (n := n) hq
  have hle := two_pow_rulerLen_le (gapNumEdges q n)
  have hone : 0 < rulerLen (gapNumEdges q n) := rulerLen_pos hpos
  have heven : 2 ∣ 2 ^ gapCoins q n := dvd_pow_self 2 (by rw [gapCoins]; omega)
  obtain ⟨c, hc⟩ := heven
  have hgc : gapCoins q n = rulerLen (gapNumEdges q n) := rfl
  rw [hgc] at hc
  rw [hgc]
  omega

theorem gapCoins_bigO_log (q : Polynomial ℕ) :
    gapCoins q =O fun n => Nat.log 2 n := by
  obtain ⟨A, B, hAB⟩ := gapNumEdges_polyBounded q
  exact rulerLen_bigO_log hAB

/-- Doubling a constructible bound `j` times keeps it constructible. -/
theorem constructible_pow_mul {t : ℕ → ℕ}
    (ht : (fun x : List Bool => List.replicate (t x.length) true) ∈ FP) (j : ℕ) :
    (fun x : List Bool => List.replicate (2 ^ j * t x.length) true) ∈ FP := by
  induction j with
  | zero => simpa using ht
  | succ j ih =>
      refine mem_FP_of_eq (constructible_double (r := fun n => 2 ^ j * t n) ih) fun x => ?_
      congr 1
      ring

/-! ### The edge count of the algorithmic graph -/

theorem numEdges_gapAlg_eq {E padU : List Bool → List Bool} {Φ : List Bool → CNF}
    (hgap : gapAll algF algHd E padU ∈ FP)
    (hE : ∀ x, E x = (Φ x).encode) (h3 : ∀ x, CNF.Is3CNF (Φ x))
    (hmark : ∀ x, padU x = List.replicate (padU x).length true)
    (hle : ∀ x, 3 * (Φ x).length ≤ (padU x).length) {q : Polynomial ℕ}
    (hq : ∀ x, (padU x).length = q.eval x.length) (x : List Bool) :
    (gapAlg algF algHd E padU hgap).numEdges x = gapNumEdges q x.length := by
  rw [numEdges_gapAlg, gapAll_eq algF algHd E padU hE h3 hmark hle x, gEdges_encGraph,
    gapAllG, numEdges_iterStep, ConstraintGraph.numEdges_padGraph, numEdges_baseCSP,
    max_eq_left (by have := hle x; omega), hq, gapNumEdges]

/-! ### The verifier -/

open scoped Complexity in
/-- **Every `NP` language has a PCP verifier** with logarithmically many coins
and constantly many queries. -/
theorem exists_pcp_of_mem_NP {L : Language} (hL : L ∈ NP) :
    ∃ r : ℕ → ℕ, r =O (fun n => Nat.log 2 n) ∧ Constructible r
      ∧ ∃ qc : ℕ → ℕ, qc =O (fun _ => 1) ∧ L ∈ PCP r qc := by
  classical
  obtain ⟨E, Φ, hEfp, hEeq, h3, hLiff⟩ := exists_reduction_cnf hL
  obtain ⟨pad0, q0, hpad0fp, hmark0, hq0, hle0⟩ := exists_padRuler hEfp 3
  set padU : List Bool → List Bool := fun x => pad0 x ++ [true] with hpadU
  set q : Polynomial ℕ := q0 + 1 with hqdef
  have hpadfp : padU ∈ FP := Cobham.appendFn_mem_FP hpad0fp (constFn_mem_FP [true])
  have hlen : ∀ x, (padU x).length = (pad0 x).length + 1 := by
    intro x
    rw [hpadU]
    simp
  have hmark : ∀ x, padU x = List.replicate (padU x).length true := by
    intro x
    rw [hlen x, List.replicate_succ', ← hmark0 x, hpadU]
  have hq : ∀ x : List Bool, (padU x).length = q.eval x.length := by
    intro x
    rw [hlen x, hq0 x, hqdef, Polynomial.eval_add, Polynomial.eval_one]
  have hqpos : ∀ n, 0 < q.eval n := by
    intro n
    rw [hqdef, Polynomial.eval_add, Polynomial.eval_one]
    omega
  have hle : ∀ x, 3 * (Φ x).length ≤ (padU x).length := by
    intro x
    have h1 := hle0 x
    have h2 := length_le_length_encode (Φ x)
    rw [← hEeq x] at h2
    rw [hlen x]
    omega
  obtain ⟨p0, hp0⟩ := Cobham.output_length_poly_of_mem_FP hEfp
  have hgap : gapAll algF algHd E padU ∈ FP :=
    gapAll_mem_FP algF algHd E padU hEfp hpadfp hEeq h3 hmark hle p0 q hp0 hq
  have hmodels := gapAlg_models algF algHd E padU hgap hEeq h3 hmark hle
  have hNE : ∀ x, (gapAlg algF algHd E padU hgap).numEdges x = gapNumEdges q x.length :=
    fun x => numEdges_gapAlg_eq hgap hEeq h3 hmark hle hq x
  have ht : (fun x : List Bool => List.replicate (gapCoins q x.length) true) ∈ FP := by
    have hfp : (fun x : List Bool =>
        logRuler (posCount (pairSnd (gapAll algF algHd E padU x)))) ∈ FP :=
      mem_FP_of_eq (mem_FP_comp (gEdgesFn_mem_FP hgap) logRuler_mem_FP) fun _ => rfl
    refine mem_FP_of_eq hfp fun x => ?_
    have h : gEdges (gapAll algF algHd E padU x) = gapNumEdges q x.length := by
      rw [← numEdges_gapAlg algF algHd E padU hgap x]
      exact hNE x
    rw [logRuler_eq, length_posCount_sndBlock, h, gapCoins]
  obtain ⟨Ac, Bc, hABc⟩ := gapNumEdges_polyBounded q
  have hclamp : ∀ n : ℕ, 2 ^ gapCoins q n
      ≤ (Polynomial.C (2 * Ac + 1) * (Polynomial.X + 1) ^ Bc).eval
          (2 * n + 2 + gapCoins q n) := by
    intro n
    have h1 : 2 ^ gapCoins q n ≤ 2 * gapNumEdges q n := two_pow_gapCoins_le (hqpos n)
    have h2 : gapNumEdges q n ≤ Ac * (n + 1) ^ Bc := hABc n
    have h4 : (n + 1) ^ Bc ≤ (2 * n + 2 + gapCoins q n + 1) ^ Bc :=
      Nat.pow_le_pow_left (by omega) _
    have h5 : (Polynomial.C (2 * Ac + 1) * (Polynomial.X + 1) ^ Bc).eval
        (2 * n + 2 + gapCoins q n)
        = (2 * Ac + 1) * (2 * n + 2 + gapCoins q n + 1) ^ Bc := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    have h6 : 2 * (Ac * (n + 1) ^ Bc)
        ≤ (2 * Ac + 1) * (2 * n + 2 + gapCoins q n + 1) ^ Bc := by
      calc 2 * (Ac * (n + 1) ^ Bc) = (2 * Ac) * (n + 1) ^ Bc := by ring
        _ ≤ (2 * Ac + 1) * (2 * n + 2 + gapCoins q n + 1) ^ Bc :=
            Nat.mul_le_mul (by omega) h4
    rw [h5]
    omega
  have hcomp : ∀ x ∈ L, ∃ π : List Bool,
      ∀ e < (gapAlg algF algHd E padU hgap).numEdges x,
        (gapAlg algF algHd E padU hgap).Sat x π e := by
    intro x hx
    exact hmodels.sat_of_satisfiable x
      (satisfiable_gapAllG algF algHd padU h3 hle x ((hLiff x).mp hx))
  have hsound : ∀ x ∉ L, ∀ π : List Bool,
      (((Finset.range ((gapAlg algF algHd E padU hgap).numEdges x)).filter
        ((gapAlg algF algHd E padU hgap).Sat x π)).card : ℚ)
        ≤ (1 - (Dinur.amplifier (algF.toFamily algHd)).gap)
          * (gapAlg algF algHd E padU hgap).numEdges x := by
    intro x hx π
    exact hmodels.card_sat_le x
      (gap_le_unsatVal_gapAllG algF algHd padU h3 hle x
        (fun hs => hx ((hLiff x).mpr hs))) π
  obtain ⟨j, hj⟩ := mem_PCP_of_algCSP (gapAlg algF algHd E padU hgap)
    (Polynomial.C (2 * Ac + 1) * (Polynomial.X + 1) ^ Bc) (gapCoins q) ht hclamp
    (fun x => by rw [hNE x]; exact le_two_pow_gapCoins q x.length)
    (fun x => by rw [hNE x]; exact two_pow_gapCoins_le (hqpos x.length))
    (Dinur.amplifier (algF.toFamily algHd)).gap_pos
    (Dinur.amplifier (algF.toFamily algHd)).gap_le_one hcomp hsound
  refine ⟨fun n => 2 ^ j * gapCoins q n, ?_, ?_,
    fun _ => 2 ^ j * (2 * (gapAlg algF algHd E padU hgap).width), ?_, hj⟩
  · exact BigO.const_mul_left _ (gapCoins_bigO_log q)
  · exact constructible_pow_mul ht j
  · have h := BigO.const_mul_left (2 ^ j * (2 * (gapAlg algF algHd E padU hgap).width))
      (BigO.refl fun _ : ℕ => 1)
    simpa using h

end Complexity
