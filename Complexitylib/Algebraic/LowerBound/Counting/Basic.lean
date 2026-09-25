/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Counting.Syntax
public import Complexitylib.Algebraic.Semantics

/-!
# Shannon counting bounds

Exact ordered-syntax counts are converted here into semantic bounds for an
arbitrary finite interpretation and an arbitrary finite family of targets.
-/

@[expose] public section

namespace Algebraic

/-- A circuit with a gate count chosen from `0, ..., G`. -/
abbrev BoundedCircuit (σ : Signature) (n m G : Nat) :=
  Σ g : Fin (G + 1), {circuit : Circuit σ n m // circuit.size = g}

/-- Evaluate a circuit whose internal gate count is bounded by `G`. -/
def BoundedCircuit.eval
    (circuit : BoundedCircuit σ n m G)
    (interpretation : Interpretation σ U) : Target U n m :=
  circuit.2.1.eval interpretation

/-- Functions computed by circuits with at most `G` internal gates. -/
noncomputable def _root_.Cslib.Circuits.Circuit.functionsAtMost
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n m G : Nat) : Finset (Target U n m) := by
  classical
  exact Finset.univ.image fun circuit : BoundedCircuit σ n m G =>
    circuit.eval interpretation

export Cslib.Circuits (Circuit.functionsAtMost)

/-- Number of topologically ordered circuit descriptions with at most `G`
internal gates. -/
def _root_.Cslib.Circuits.Signature.orderedBudget
    (σ : Signature) [Fintype σ.Op]
    (n m G : Nat) : Nat :=
  ∑ g ∈ Finset.range (G + 1),
    (∏ j ∈ Finset.range g, σ.lineCount (n + j)) *
      (n + g) ^ m

export Cslib.Circuits (Signature.orderedBudget)

theorem _root_.Cslib.Circuits.Circuit.mem_functionsAtMost_iff
    [Fintype σ.Op] [Fintype U]
    {interpretation : Interpretation σ U}
    {target : Target U n m} :
    target ∈ Circuit.functionsAtMost interpretation n m G ↔
      ∃ circuit : Circuit σ n m, circuit.size ≤ G ∧
        circuit.ComputesWith interpretation target := by
  classical
  constructor
  · intro present
    rw [Circuit.functionsAtMost, Finset.mem_image] at present
    obtain ⟨circuit, _, equal⟩ := present
    exact ⟨circuit.2.1, circuit.2.2.le.trans (Nat.le_of_lt_succ circuit.1.isLt),
      fun input => by
        simpa [BoundedCircuit.eval] using congrFun equal input⟩
  · rintro ⟨circuit, bounded, computes⟩
    rw [Circuit.functionsAtMost, Finset.mem_image]
    let index : Fin (G + 1) := ⟨circuit.size, Nat.lt_succ_iff.mpr bounded⟩
    refine ⟨⟨index, circuit, rfl⟩, Finset.mem_univ _, ?_⟩
    simpa [BoundedCircuit.eval] using computes.eval_eq

export Cslib.Circuits (Circuit.mem_functionsAtMost_iff)

/-- Being absent from the easy-function set is exactly gate hardness at the
corresponding budget. -/
theorem _root_.Cslib.Circuits.Circuit.not_mem_functionsAtMost_iff
    [Fintype σ.Op] [Fintype U]
    {interpretation : Interpretation σ U}
    {target : Target U n m} :
    target ∉ Circuit.functionsAtMost interpretation n m G ↔
      Circuit.GateHard interpretation G target := by
  simpa [Circuit.GateHard] using not_congr
    (Circuit.mem_functionsAtMost_iff
      (interpretation := interpretation) (target := target) (G := G))

export Cslib.Circuits (Circuit.not_mem_functionsAtMost_iff)

/-- Exact number of ordered circuits with at most `G` internal gates. -/
theorem BoundedCircuit.card [Fintype σ.Op] :
    Fintype.card (BoundedCircuit σ n m G) =
      σ.orderedBudget n m G := by
  unfold Signature.orderedBudget Signature.lineCount
  rw [Fintype.card_sigma]
  simp_rw [card_circuit]
  exact Fin.sum_univ_eq_sum_range
    (fun g : Nat =>
      (∏ j ∈ Finset.range g,
        ∑ op : σ.Op, (n + j) ^ σ.Arity op) *
      (n + g) ^ m)
    (G + 1)

/-- Semantic functions are no more numerous than their ordered descriptions. -/
theorem _root_.Cslib.Circuits.Circuit.card_functionsAtMost_le
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U) :
    (Circuit.functionsAtMost interpretation n m G).card ≤
      σ.orderedBudget n m G := by
  classical
  exact Finset.card_image_le.trans_eq BoundedCircuit.card

export Cslib.Circuits (Circuit.card_functionsAtMost_le)

/-- Any family larger than the set of functions available within budget contains
a target outside that budget. -/
theorem _root_.Cslib.Circuits.Circuit.exists_hard_in_family_of_card_lt
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (family : Finset (Target U n m))
    (large :
      (Circuit.functionsAtMost interpretation n m G).card < family.card) :
    ∃ target ∈ family,
      Circuit.GateHard interpretation G target := by
  classical
  obtain ⟨target, inFamily, notComputable⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card large
  exact ⟨target, inFamily,
    Circuit.not_mem_functionsAtMost_iff.mp notComputable⟩

export Cslib.Circuits (Circuit.exists_hard_in_family_of_card_lt)

/-- If the easy functions do not fill the whole target space, some target lies
outside the gate budget. -/
theorem _root_.Cslib.Circuits.Circuit.exists_hard_of_card_lt
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (small :
      (Circuit.functionsAtMost interpretation n m G).card <
        Target.count U n m) :
    ∃ target : Target U n m,
      Circuit.GateHard interpretation G target := by
  classical
  have targetCard : Fintype.card (Target U n m) =
      Target.count U n m := by
    rw [Target.count, Nat.card_eq_fintype_card]
  obtain ⟨target, _, hard⟩ := Circuit.exists_hard_in_family_of_card_lt
    (G := G) interpretation (Finset.univ : Finset (Target U n m))
    (by simpa only [Finset.card_univ, targetCard] using small)
  exact ⟨target, hard⟩

export Cslib.Circuits (Circuit.exists_hard_of_card_lt)

/-- A family larger than the ordered-syntax budget contains a hard target. -/
theorem _root_.Cslib.Circuits.Circuit.exists_hard_in_family
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (family : Finset (Target U n m))
    (large : σ.orderedBudget n m G < family.card) :
    ∃ target ∈ family,
      Circuit.GateHard interpretation G target := by
  apply Circuit.exists_hard_in_family_of_card_lt interpretation family
  exact (Circuit.card_functionsAtMost_le interpretation).trans_lt large

export Cslib.Circuits (Circuit.exists_hard_in_family)

end Algebraic
