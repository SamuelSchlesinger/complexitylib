/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.MCSP.SubcubeRepetition

/-!
# Non-vacuity of the MCSP lower bounds

The lower bounds in `Complexitylib.Algebraic.LowerBound.MCSP.Symmetry` assume that the MCSP
predicate is non-constant, and those in `Complexitylib.Algebraic.LowerBound.MCSP.SubcubeRepetition`
assume that some truth table has exact `DeMorgan.binaryCost` complexity `s ≥ 1`. This module
discharges both hypotheses.

* `card_sub_le_costComplexity_deMorgan`: a target with `k` essential inputs and `m` outputs has
  `DeMorgan.binaryCost` complexity at least `k - m` (weighted frontier counting).
* `costComplexity_andTarget`: the conjunction `x 0 && x 1` of two of `n + 2` variables has
  `DeMorgan.binaryCost` complexity exactly `1`, so
  `exactCostSet DeMorgan.interpretation DeMorgan.binaryCost (n + 2) 1` is nonempty
  (`exactCostSet_deMorgan_one_nonempty`).
* `mcspCostScalar_deMorgan_succ_ne_of_mem_exactCostSet`: if `tt` has exact complexity `s ≥ 1`,
  then `mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s` is non-constant
  (`pairTruthTable tt tt` is a yes-instance; pairing the complement of `tt` with `tt` is not).
* Consequently the `Symmetry` bounds hold for `n + 1` without the non-constancy hypothesis
  (`..._of_mem_exactCostSet`), and for `s = 1` on `2 ^ (n + 3)` truth-table inputs they hold with
  no hypothesis at all (`mcspCostTarget_deMorgan_one_binaryCost_lower_bound`,
  `mcspCostTarget_deMorgan_one_size_lower_bound`, `mcsp_one_formula_leaves_lower_bound`).

The `Binary` predicate `mcspScalar Binary.interpretation n s` is not treated here; its
non-constancy remains a hypothesis of the `Binary` bounds in `Symmetry`.
-/

@[expose] public section

namespace Algebraic.MCSP

/-! ## Essential inputs lower-bound `DeMorgan.binaryCost` complexity -/

/-- If every coordinate in `selected` is essential for `target`, then any De Morgan circuit
computing `target` has `binaryCost` at least `selected.card - m`. -/
theorem card_sub_le_costComplexity_deMorgan {N m : Nat} {target : Target Bool N m}
    {selected : Finset (Fin N)} (hess : ∀ i ∈ selected, EssentialAt target i) :
    ((selected.card - m : Nat) : ℕ∞) ≤
      Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost target := by
  apply Circuit.le_costComplexity
  intro c hc
  have hsub : selected.card ≤ c.inputSupport.card :=
    Finset.card_le_card fun i hi => (hess i hi).mem_support hc.dependsOnlyOn
  have hbound := card_inputSupport_le_binaryCost c
  exact_mod_cast (show selected.card - m ≤ c.cost DeMorgan.binaryCost by omega)

/-! ## A truth table of exact `DeMorgan.binaryCost` complexity one -/

/-- The conjunction `x 0 && x 1` of the first two of `n + 2` input variables. -/
def andTarget (n : Nat) : Target Bool (n + 2) 1 :=
  fun x _ => x 0 && x 1

/-- The one-gate De Morgan circuit computing `andTarget n`. -/
def andCircuit (n : Nat) : Circuit DeMorgan.signature (n + 2) 1 where
  program := Program.empty.gate (DeMorgan.binaryLine .and (Wire.input 0) (Wire.input 1))
  outputs := fun _ => Wire.gate 0

/-- `andCircuit n` computes `andTarget n`. -/
theorem andCircuit_computes (n : Nat) :
    (andCircuit n).ComputesWith DeMorgan.interpretation (andTarget n) := by
  intro x
  funext o
  rfl

/-- `andCircuit n` has `DeMorgan.binaryCost` exactly `1`. -/
@[simp]
theorem cost_andCircuit (n : Nat) : (andCircuit n).cost DeMorgan.binaryCost = 1 :=
  rfl

/-- Changing only coordinate `i ∈ {0, 1}` of the all-`true` input changes `andTarget n`. -/
private theorem essentialAt_andTarget {n : Nat} (i : Fin (n + 2)) (hi : i = 0 ∨ i = 1) :
    EssentialAt (andTarget n) i := by
  refine ⟨fun _ => true, Function.update (fun _ => true) i false, ?_, ?_⟩
  · intro k hk
    exact (Function.update_of_ne hk false (fun _ : Fin (n + 2) => true)).symm
  · intro heq
    have h0 := congrFun heq 0
    rcases hi with rfl | rfl <;> simp [andTarget] at h0

/-- The conjunction of two variables has `DeMorgan.binaryCost` complexity exactly `1`: the
one-gate `andCircuit` gives `≤ 1`, and since both variables are essential, frontier counting
(`card_sub_le_costComplexity_deMorgan`) gives `≥ 2 - 1`. -/
theorem costComplexity_andTarget (n : Nat) :
    Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost (andTarget n) = 1 := by
  apply le_antisymm
  · simpa using (andCircuit n).costComplexity_le DeMorgan.binaryCost (andCircuit_computes n)
  · have hne : (0 : Fin (n + 2)) ≠ 1 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    have hcard : ({0, 1} : Finset (Fin (n + 2))).card = 2 := Finset.card_pair hne
    have hbound := card_sub_le_costComplexity_deMorgan (m := 1) (target := andTarget n)
      (selected := {0, 1}) (by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        exact essentialAt_andTarget i hi)
    rw [hcard] at hbound
    simpa using hbound

/-- The truth table of `andTarget n` has exact `DeMorgan.binaryCost` complexity `1`. -/
theorem andTruthTable_mem_exactCostSet (n : Nat) :
    (truthTableTargetEquiv (n + 2)).symm (andTarget n) ∈
      exactCostSet DeMorgan.interpretation DeMorgan.binaryCost (n + 2) 1 := by
  rw [mem_exactCostSet_iff, Equiv.apply_symm_apply]
  exact_mod_cast costComplexity_andTarget n

/-- For every `n`, some `2 ^ (n + 2)`-bit truth table has exact `DeMorgan.binaryCost`
complexity `1`. -/
theorem exactCostSet_deMorgan_one_nonempty (n : Nat) :
    (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost (n + 2) 1).Nonempty :=
  ⟨_, andTruthTable_mem_exactCostSet n⟩

/-! ## Non-constancy of MCSP from an exact-complexity truth table -/

/-- If `tt` has exact `DeMorgan.binaryCost` complexity `s ≥ 1`, then
`mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s` is non-constant: it accepts
`pairTruthTable tt tt` and rejects `pairTruthTable (fun i => !tt i) tt`. -/
theorem mcspCostScalar_deMorgan_succ_ne_of_mem_exactCostSet {n s : Nat} (hs : 1 ≤ s)
    {tt : Fin (2 ^ n) → Bool}
    (htt : tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s) :
    mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s
        (pairTruthTable tt tt) ≠
      mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s
        (pairTruthTable (fun i => !tt i) tt) := by
  rw [(mcspCostScalar_pairTruthTable_left_eq_true_iff hs htt tt).mpr rfl]
  intro h
  have heq := (mcspCostScalar_pairTruthTable_left_eq_true_iff hs htt _).mp h.symm
  have h0 := congrFun heq ⟨0, Nat.two_pow_pos n⟩
  simp at h0

/-- Hypothesis-free form of `mcspCostScalar_deMorgan_essentialAt` for `n + 1`: if some truth
table has exact `DeMorgan.binaryCost` complexity `s ≥ 1`, every coordinate of
`mcspCostScalar ... (n + 1) s` is essential. -/
theorem mcspCostScalar_deMorgan_essentialAt_of_mem_exactCostSet {n s : Nat} (hs : 1 ≤ s)
    {tt : Fin (2 ^ n) → Bool}
    (htt : tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s)
    (i : Fin (2 ^ (n + 1))) :
    EssentialAt (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s) i :=
  mcspCostScalar_deMorgan_essentialAt (mcspCostScalar_deMorgan_succ_ne_of_mem_exactCostSet hs htt) i

/-- Hypothesis-free form of `mcspCostTarget_deMorgan_inputSupport_eq_univ` for `n + 1`: if some
truth table has exact `DeMorgan.binaryCost` complexity `s ≥ 1`, every circuit (in any basis)
computing `mcspCostTarget ... (n + 1) s` reads all `2 ^ (n + 1)` inputs. -/
theorem mcspCostTarget_deMorgan_inputSupport_eq_univ_of_mem_exactCostSet {σ : Signature}
    {interpretation : Interpretation σ Bool} {n s : Nat} (hs : 1 ≤ s)
    {tt : Fin (2 ^ n) → Bool}
    (htt : tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s)
    {c : Circuit σ (2 ^ (n + 1)) 1}
    (hcomp : c.ComputesWith interpretation
      (mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s)) :
    c.inputSupport = Finset.univ :=
  mcspCostTarget_deMorgan_inputSupport_eq_univ
    (mcspCostScalar_deMorgan_succ_ne_of_mem_exactCostSet hs htt) hcomp

/-- Hypothesis-free form of `mcspCostTarget_deMorgan_binaryCost_lower_bound` for `n + 1`:
`2 ^ (n + 1) ≤ c.cost DeMorgan.binaryCost + 1` whenever some truth table has exact
`DeMorgan.binaryCost` complexity `s ≥ 1`. -/
theorem mcspCostTarget_deMorgan_binaryCost_lower_bound_of_mem_exactCostSet {n s : Nat}
    (hs : 1 ≤ s) {tt : Fin (2 ^ n) → Bool}
    (htt : tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s)
    (c : Circuit DeMorgan.signature (2 ^ (n + 1)) 1)
    (hcomp : c.ComputesWith DeMorgan.interpretation
      (mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s)) :
    2 ^ (n + 1) ≤ c.cost DeMorgan.binaryCost + 1 :=
  mcspCostTarget_deMorgan_binaryCost_lower_bound
    (mcspCostScalar_deMorgan_succ_ne_of_mem_exactCostSet hs htt) c hcomp

/-- Hypothesis-free form of `mcspCostTarget_deMorgan_size_lower_bound` for `n + 1`:
`2 ^ (n + 1) ≤ c.size + 1` for every fan-in-2 circuit (in any basis) computing
`mcspCostTarget ... (n + 1) s`, whenever some truth table has exact `DeMorgan.binaryCost`
complexity `s ≥ 1`. -/
theorem mcspCostTarget_deMorgan_size_lower_bound_of_mem_exactCostSet {σ : Signature}
    {interpretation : Interpretation σ Bool} {n s : Nat} (hs : 1 ≤ s)
    {tt : Fin (2 ^ n) → Bool}
    (htt : tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s)
    (c : Circuit σ (2 ^ (n + 1)) 1) (hfan : c.FanInAtMost 2)
    (hcomp : c.ComputesWith interpretation
      (mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s)) :
    2 ^ (n + 1) ≤ c.size + 1 :=
  mcspCostTarget_deMorgan_size_lower_bound
    (mcspCostScalar_deMorgan_succ_ne_of_mem_exactCostSet hs htt) c hfan hcomp

/-! ## Fully hypothesis-free bounds for `s = 1` -/

/-- Every De Morgan circuit computing
`mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost (n + 3) 1` satisfies
`2 ^ (n + 3) ≤ c.cost DeMorgan.binaryCost + 1`. -/
theorem mcspCostTarget_deMorgan_one_binaryCost_lower_bound (n : Nat)
    (c : Circuit DeMorgan.signature (2 ^ (n + 3)) 1)
    (hcomp : c.ComputesWith DeMorgan.interpretation
      (mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost (n + 3) 1)) :
    2 ^ (n + 3) ≤ c.cost DeMorgan.binaryCost + 1 :=
  mcspCostTarget_deMorgan_binaryCost_lower_bound_of_mem_exactCostSet le_rfl
    (andTruthTable_mem_exactCostSet n) c hcomp

/-- Every fan-in-2 circuit (in any basis) computing
`mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost (n + 3) 1` satisfies
`2 ^ (n + 3) ≤ c.size + 1`. -/
theorem mcspCostTarget_deMorgan_one_size_lower_bound {σ : Signature}
    {interpretation : Interpretation σ Bool} (n : Nat)
    (c : Circuit σ (2 ^ (n + 3)) 1) (hfan : c.FanInAtMost 2)
    (hcomp : c.ComputesWith interpretation
      (mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost (n + 3) 1)) :
    2 ^ (n + 3) ≤ c.size + 1 :=
  mcspCostTarget_deMorgan_size_lower_bound_of_mem_exactCostSet le_rfl
    (andTruthTable_mem_exactCostSet n) c hfan hcomp

/-- Every De Morgan formula computing
`mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 3) 1` has at least `2 ^ (n + 3)`
leaves. -/
theorem mcsp_one_formula_leaves_lower_bound (n : Nat) {F : KW.Formula (2 ^ (n + 3))}
    (hF : F.Computes (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 3) 1)) :
    2 ^ (n + 3) ≤ F.leaves :=
  mcsp_formula_leaves_lower_bound le_rfl (andTruthTable_mem_exactCostSet n) hF

end Algebraic.MCSP
