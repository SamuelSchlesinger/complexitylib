/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Support
public import Complexitylib.Algebraic.Cost

/-!
# Weighted support bounds across a circuit frontier

Opening a gate of arity at most `weight + 1` increases the number of live
wires by at most its weight. This bounds the union of the supports of any
selected wires, including shared intermediate gates and free output wires.
-/

@[expose] public section

namespace Algebraic

/-- The union of original inputs supporting a selected set of circuit wires. -/
def _root_.Cslib.Circuits.Program.frontierSupport (program : Program σ n g) (frontier : Finset (Wire n g)) :
    Finset (Fin n) := frontier.biUnion program.wireSupport

export Cslib.Circuits (Program.frontierSupport)

/-- Weighted fan-in controls the number of inputs reaching an arbitrary wire frontier. -/
theorem _root_.Cslib.Circuits.Program.card_frontierSupport_le (program : Program σ n g)
    (weight : OperationCost σ) (bounded : ∀ op, σ.Arity op ≤ weight op + 1)
    (frontier : Finset (Wire n g)) :
    (program.frontierSupport frontier).card ≤ frontier.card + program.cost weight := by
  induction program with
  | empty =>
    have included : (Program.empty : Program σ n 0).frontierSupport frontier ⊆ frontier := by
      intro i member
      obtain ⟨wire, present, supported⟩ := Finset.mem_biUnion.mp member
      revert present supported
      refine Fin.addCases (fun input present supported => ?_) (fun j => Fin.elim0 j) wire
      have same : i = input := by
        change i ∈ (Program.empty : Program σ n 0).wireSupport (Wire.input input) at supported
        simpa only [Program.wireSupport_input, Finset.mem_singleton] using supported
      simpa [same] using present
    simpa using Finset.card_le_card included
  | @gate g program line ih =>
    let prior := Finset.univ.filter (fun wire : Wire n g => wire.castSucc ∈ frontier)
    let arguments := Finset.univ.image line.wires
    let opened := if Fin.last (n + g) ∈ frontier then prior ∪ arguments else prior
    have supports : (program.gate line).frontierSupport frontier ⊆
        program.frontierSupport opened := by
      intro i member
      obtain ⟨wire, present, supported⟩ := Finset.mem_biUnion.mp member
      revert present supported
      refine Fin.lastCases ?_ (fun wire => ?_) wire
      · intro present supported
        simp only [Nat.add_eq] at present supported
        rw [Program.wireSupport_gate_last] at supported
        obtain ⟨argument, supported⟩ := Line.mem_inputSupport.mp supported
        exact Finset.mem_biUnion.mpr ⟨line.wires argument,
          by simp [opened, arguments, present], supported⟩
      · intro present supported
        rw [Program.wireSupport_gate_castSucc] at supported
        refine Finset.mem_biUnion.mpr ⟨wire, ?_, supported⟩
        by_cases last : Fin.last (n + g) ∈ frontier <;> simp [opened, prior, last, present]
    have priorBound : prior.card ≤ frontier.card := by
      apply Finset.card_le_card_of_injOn Fin.castSucc
      · intro wire present
        simpa [prior] using present
      · exact (Fin.castSucc_injective _).injOn
    have argumentBound : arguments.card ≤ weight line.op + 1 := by
      calc
        arguments.card ≤ (Finset.univ : Finset (Fin (σ.Arity line.op))).card := Finset.card_image_le
        _ = σ.Arity line.op := by simp
        _ ≤ weight line.op + 1 := bounded line.op
    have openedBound : opened.card ≤ frontier.card + weight line.op := by
      by_cases last : Fin.last (n + g) ∈ frontier
      · have eraseBound : prior.card ≤ (frontier.erase (Fin.last (n + g))).card := by
          apply Finset.card_le_card_of_injOn Fin.castSucc
          · intro wire present
            exact Finset.mem_erase.mpr ⟨by simp, by simpa [prior] using present⟩
          · exact (Fin.castSucc_injective _).injOn
        have erased := Finset.card_erase_of_mem last
        have positive := Finset.one_le_card.mpr ⟨_, last⟩
        have unionBound := Finset.card_union_le prior arguments
        simp only [opened, last, ↓reduceIte]
        omega
      · simp only [opened, last, ↓reduceIte]
        omega
    exact (Finset.card_le_card supports).trans ((ih opened).trans (by
      simp only [Program.cost_gate]
      omega))

export Cslib.Circuits (Program.card_frontierSupport_le)

end Algebraic
