/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Support
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Size lower bounds from bounded fan-in

Unfolding a frontier through a bounded-fan-in program controls how many
original inputs can reach the outputs. Essential inputs therefore give a
lower bound on circuit size.
-/

@[expose] public section

namespace Algebraic

private def _root_.Cslib.Circuits.Program.reachableInputs :
    (program : Program σ n g) → Finset (Wire n g) → Finset (Fin n)
  | .empty, frontier => frontier
  | @Program.gate _ _ g program line, frontier =>
      let prior := Finset.univ.filter fun wire : Wire n g => wire.castSucc ∈ frontier
      let opened :=
        if Fin.last (n + g) ∈ frontier then
          prior ∪ Finset.univ.image line.wires
        else
          prior
      program.reachableInputs opened

private def _root_.Cslib.Circuits.Circuit.frontier (c : Circuit σ n g m) : Finset (Wire n g) :=
  Finset.univ.image c.outputs

@[simp] private theorem _root_.Cslib.Circuits.Circuit.mem_frontier
    {c : Circuit σ n g m}
    {wire : Wire n g} :
    wire ∈ c.frontier ↔
      ∃ output, c.outputs output = wire := by
  simp [Cslib.Circuits.Circuit.frontier]

private def _root_.Cslib.Circuits.Circuit.reachableInputs (c : Circuit σ n g m) : Finset (Fin n) :=
  c.program.reachableInputs c.frontier

private theorem _root_.Cslib.Circuits.Program.support_subset_reachableInputs
    (program : Program σ n g) :
    ∀ frontier : Finset (Wire n g),
      frontier.biUnion program.wireSupport ⊆
        program.reachableInputs frontier := by
  induction program with
  | empty =>
      intro frontier i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨wire, wireSelected, hi⟩ := hi
      revert wireSelected hi
      refine Fin.addCases (fun input wireSelected hi => ?_)
        (fun impossible => Fin.elim0 impossible) wire
      simp only [Program.wireSupport, Program.gateSupport,
        Fin.addCases_left, Finset.mem_singleton] at hi
      subst i
      change input ∈ frontier
      simpa using wireSelected
  | @gate g program line ih =>
      intro frontier i hi
      let prior := Finset.univ.filter fun wire : Wire n g => wire.castSucc ∈ frontier
      let opened :=
        if Fin.last (n + g) ∈ frontier then
          prior ∪ Finset.univ.image line.wires
        else
          prior
      change i ∈ program.reachableInputs opened
      apply ih opened
      rw [Finset.mem_biUnion] at hi
      obtain ⟨wire, wireSelected, hi⟩ := hi
      revert wireSelected hi
      refine Fin.lastCases ?_ (fun wire => ?_) wire
      · intro lastSelected hi
        simp only [Nat.add_eq] at lastSelected hi
        rw [Program.wireSupport_gate_last] at hi
        obtain ⟨argument, hi⟩ := Line.mem_inputSupport.mp hi
        exact Finset.mem_biUnion.mpr
          ⟨line.wires argument, by simp [opened, lastSelected], hi⟩
      · intro wireSelected hi
        rw [Program.wireSupport_gate_castSucc] at hi
        refine Finset.mem_biUnion.mpr ⟨wire, ?_, hi⟩
        by_cases lastSelected : Fin.last (n + g) ∈ frontier <;>
          simp [opened, lastSelected, prior, wireSelected]

private theorem _root_.Cslib.Circuits.Circuit.inputSupport_subset_reachableInputs
    (c : Circuit σ n g m) :
    c.inputSupport ⊆ c.reachableInputs := by
  intro input present
  apply c.program.support_subset_reachableInputs c.frontier
  simp only [Circuit.mem_inputSupport, Finset.mem_biUnion,
    Cslib.Circuits.Circuit.mem_frontier] at present ⊢
  obtain ⟨output, supported⟩ := present
  exact ⟨c.outputs output, ⟨output, rfl⟩, supported⟩

private theorem _root_.Cslib.Circuits.Program.card_reachableInputs_le
    (program : Program σ n g)
    (r : Nat) :
    ∀ (_bounded : program.FanInAtMost r) (frontier : Finset (Wire n g)),
      (program.reachableInputs frontier).card ≤
        frontier.card + (r - 1) * g := by
  induction program with
  | empty =>
      intro _ frontier
      simp [Cslib.Circuits.Program.reachableInputs]
  | @gate g program line ih =>
      intro bounded frontier
      obtain ⟨programBounded, lineBounded⟩ := bounded
      let prior := Finset.univ.filter fun wire : Wire n g => wire.castSucc ∈ frontier
      let lineInputs := Finset.univ.image line.wires
      let opened :=
        if Fin.last (n + g) ∈ frontier then prior ∪ lineInputs else prior
      have priorBound : prior.card ≤ frontier.card := by
        apply Finset.card_le_card_of_injOn Fin.castSucc
        · intro wire present
          simpa [prior] using present
        · exact (Fin.castSucc_injective _).injOn
      have lineBound : lineInputs.card ≤ r := by
        calc
          lineInputs.card ≤ (Finset.univ : Finset (Fin (σ.Arity line.op))).card :=
            Finset.card_image_le
          _ = σ.Arity line.op := by simp
          _ ≤ r := lineBounded
      have openedBound : opened.card ≤ frontier.card + (r - 1) := by
        by_cases lastSelected : Fin.last (n + g) ∈ frontier
        · have priorEraseBound : prior.card ≤
              (frontier.erase (Fin.last (n + g))).card := by
            apply Finset.card_le_card_of_injOn Fin.castSucc
            · intro wire present
              change Fin.castSucc wire ∈ frontier.erase (Fin.last (n + g))
              rw [Finset.mem_erase]
              exact ⟨by simp, by simpa [prior] using present⟩
            · exact (Fin.castSucc_injective _).injOn
          have erased := Finset.card_erase_of_mem lastSelected
          have openedEq : opened = prior ∪ lineInputs := by
            simp [opened, lastSelected]
          rw [openedEq]
          calc
            (prior ∪ lineInputs).card ≤ prior.card + lineInputs.card :=
              Finset.card_union_le _ _
            _ ≤ (frontier.erase (Fin.last (n + g))).card + r :=
              Nat.add_le_add priorEraseBound lineBound
            _ = frontier.card - 1 + r := by rw [erased]
            _ ≤ frontier.card + (r - 1) := by
              have frontierPositive : 1 ≤ frontier.card :=
                Finset.one_le_card.mpr ⟨_, lastSelected⟩
              omega
        · have openedEq : opened = prior := by
            simp [opened, lastSelected]
          rw [openedEq]
          omega
      change (program.reachableInputs opened).card ≤ _
      calc
        (program.reachableInputs opened).card ≤ opened.card + (r - 1) * g :=
          ih programBounded opened
        _ ≤ frontier.card + (r - 1) * (g + 1) := by
          rw [Nat.mul_succ]
          omega

private theorem _root_.Cslib.Circuits.Circuit.card_reachableInputs_le_size
    (c : Circuit σ n g m)
    (r : Nat)
    (bounded : c.FanInAtMost r) :
    c.reachableInputs.card ≤ m + (r - 1) * c.size := by
  have frontierBound : c.frontier.card ≤ m := by
    simpa [Cslib.Circuits.Circuit.frontier] using
      (Finset.card_image_le :
        (Finset.univ.image c.outputs).card ≤
          (Finset.univ : Finset (Fin m)).card)
  have programBound := c.program.card_reachableInputs_le r bounded c.frontier
  calc
    c.reachableInputs.card ≤ c.frontier.card + (r - 1) * g := programBound
    _ ≤ m + (r - 1) * g := Nat.add_le_add_right frontierBound _
    _ = m + (r - 1) * c.size := rfl

/-- A fan-in-`r` circuit has at most `m + (r - 1) * c.size`
supporting inputs. -/
theorem _root_.Cslib.Circuits.Circuit.card_inputSupport_le_size
    (c : Circuit σ n g m)
    {r : Nat}
    (bounded : c.FanInAtMost r) :
    c.inputSupport.card ≤ m + (r - 1) * c.size := by
  exact (Finset.card_le_card c.inputSupport_subset_reachableInputs).trans
    (c.card_reachableInputs_le_size r bounded)

export Cslib.Circuits (Circuit.card_inputSupport_le_size)

/-- If a circuit has fan-in at most `r`, computes `target`, and every input in
`selected` is essential to `target`, then `selected` has at most
`m + (r - 1) * c.size` elements. -/
theorem _root_.Cslib.Circuits.Circuit.essential_le_size
    (c : Circuit σ n g m)
    {interpretation : Interpretation σ U}
    {target : (Fin n → U) → Fin m → U}
    {selected : Finset (Fin n)}
    {r : Nat}
    (computes : c.ComputesWith interpretation target)
    (essential : ∀ k ∈ selected, EssentialAt target k)
    (bounded : c.FanInAtMost r) :
    selected.card ≤ m + (r - 1) * c.size := by
  have targetDepends := computes.dependsOnlyOn
  exact (Finset.card_le_card fun k hk =>
    (essential k hk).mem_support targetDepends).trans
      (c.card_inputSupport_le_size bounded)

export Cslib.Circuits (Circuit.essential_le_size)

end Algebraic
