/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BasisHom.Defs

/-!
# Semantics-preserving maps between circuit bases -- proof internals
-/

@[expose] public section

namespace Complexity

namespace Gate

theorem eval_mapBasis_internal
    (hom : Basis.Hom source target)
    (gate : Gate source W) (wireValues : BitString W) :
    (gate.mapBasis hom).eval wireValues =
      gate.eval wireValues := by
  simp only [Gate.eval, mapBasis]
  exact hom.eval_map gate.op gate.fanIn gate.arityOk _

end Gate

namespace Circuit

variable {N M G : ℕ} [NeZero N] [NeZero M]

theorem wireValue_mapBasis_internal
    (hom : Basis.Hom source target)
    (circuit : Circuit source N M G)
    (input : BitString N) (wire : Fin (N + G)) :
    (circuit.mapBasis hom).wireValue input wire =
      circuit.wireValue input wire := by
  have hmain : ∀ value, (hvalue : value < N + G) →
      (circuit.mapBasis hom).wireValue input ⟨value, hvalue⟩ =
        circuit.wireValue input ⟨value, hvalue⟩ := by
    intro value
    induction value using Nat.strongRecOn with
    | ind value ih =>
        intro hvalue
        by_cases hinput : value < N
        · rw [Circuit.wireValue_of_lt _ _ _ hinput,
            Circuit.wireValue_of_lt _ _ _ hinput]
        · have hgate : value - N < G := by omega
          rw [Circuit.wireValue_of_not_lt _ _ _
              (by simpa using hinput),
            Circuit.wireValue_of_not_lt _ _ _
              (by simpa using hinput)]
          change
            ((circuit.gates ⟨value - N, hgate⟩).mapBasis hom).eval
                ((circuit.mapBasis hom).wireValue input) =
              (circuit.gates ⟨value - N, hgate⟩).eval
                (circuit.wireValue input)
          rw [Gate.eval_mapBasis_internal]
          unfold Gate.eval
          congr 1
          funext gateInput
          congr 1
          apply ih
          change
            ((circuit.gates
              ⟨value - N, hgate⟩).inputs gateInput).val < value
          have hacyclic :=
            circuit.acyclic ⟨value - N, hgate⟩ gateInput
          have hNle : N ≤ value := Nat.le_of_not_gt hinput
          simpa [Nat.add_sub_of_le hNle] using hacyclic
  exact hmain wire.val wire.isLt

theorem eval_mapBasis_internal
    (hom : Basis.Hom source target)
    (circuit : Circuit source N M G)
    (input : BitString N) :
    (circuit.mapBasis hom).eval input =
      circuit.eval input := by
  funext output
  unfold Circuit.eval
  change
    ((circuit.outputs output).mapBasis hom).eval
        ((circuit.mapBasis hom).wireValue input) =
      (circuit.outputs output).eval
        (circuit.wireValue input)
  rw [Gate.eval_mapBasis_internal]
  unfold Gate.eval
  congr 1
  funext gateInput
  congr 1
  exact wireValue_mapBasis_internal hom circuit input _

theorem wireDepth_mapBasis_internal
    (hom : Basis.Hom source target)
    (circuit : Circuit source N M G)
    (wire : Fin (N + G)) :
    (circuit.mapBasis hom).wireDepth wire =
      circuit.wireDepth wire := by
  have hmain : ∀ value, (hvalue : value < N + G) →
      (circuit.mapBasis hom).wireDepth ⟨value, hvalue⟩ =
        circuit.wireDepth ⟨value, hvalue⟩ := by
    intro value
    induction value using Nat.strongRecOn with
    | ind value ih =>
        intro hvalue
        by_cases hinput : value < N
        · rw [Circuit.wireDepth_of_lt _ _ hinput,
            Circuit.wireDepth_of_lt _ _ hinput]
        · have hgate : value - N < G := by omega
          rw [Circuit.wireDepth_of_not_lt _ _
              (by simpa using hinput),
            Circuit.wireDepth_of_not_lt _ _
              (by simpa using hinput)]
          change
            1 + Fin.foldl
                (circuit.gates ⟨value - N, hgate⟩).fanIn
                (fun acc gateInput =>
                  max acc
                    ((circuit.mapBasis hom).wireDepth
                      ((circuit.gates
                        ⟨value - N, hgate⟩).inputs gateInput))) 0 =
              1 + Fin.foldl
                (circuit.gates ⟨value - N, hgate⟩).fanIn
                (fun acc gateInput =>
                  max acc
                    (circuit.wireDepth
                      ((circuit.gates
                        ⟨value - N, hgate⟩).inputs gateInput))) 0
          congr 1
          apply congrArg
            (fun depths :
                Fin (circuit.gates
                  ⟨value - N, hgate⟩).fanIn → ℕ =>
              Fin.foldl
                (circuit.gates ⟨value - N, hgate⟩).fanIn
                (fun acc gateInput =>
                  max acc (depths gateInput)) 0)
          funext gateInput
          apply ih
          change
            ((circuit.gates
              ⟨value - N, hgate⟩).inputs gateInput).val < value
          have hacyclic :=
            circuit.acyclic ⟨value - N, hgate⟩ gateInput
          have hNle : N ≤ value := Nat.le_of_not_gt hinput
          simpa [Nat.add_sub_of_le hNle] using hacyclic
  exact hmain wire.val wire.isLt

theorem outputDepth_mapBasis_internal
    (hom : Basis.Hom source target)
    (circuit : Circuit source N M G) (output : Fin M) :
    (circuit.mapBasis hom).outputDepth output =
      circuit.outputDepth output := by
  unfold Circuit.outputDepth
  change
    1 + Fin.foldl (circuit.outputs output).fanIn
        (fun acc gateInput =>
          max acc
            ((circuit.mapBasis hom).wireDepth
              ((circuit.outputs output).inputs gateInput))) 0 =
      1 + Fin.foldl (circuit.outputs output).fanIn
        (fun acc gateInput =>
          max acc
            (circuit.wireDepth
              ((circuit.outputs output).inputs gateInput))) 0
  congr 1
  apply congrArg
    (fun depths : Fin (circuit.outputs output).fanIn → ℕ =>
      Fin.foldl (circuit.outputs output).fanIn
        (fun acc gateInput => max acc (depths gateInput)) 0)
  funext gateInput
  exact wireDepth_mapBasis_internal hom circuit _

theorem depth_mapBasis_internal
    (hom : Basis.Hom source target)
    (circuit : Circuit source N M G) :
    (circuit.mapBasis hom).depth = circuit.depth := by
  unfold Circuit.depth
  apply congrArg
    (fun depths : Fin M → ℕ =>
      Fin.foldl M (fun acc output =>
        max acc (depths output)) 0)
  funext output
  exact outputDepth_mapBasis_internal hom circuit output

theorem size_mapBasis_internal
    (hom : Basis.Hom source target)
    (circuit : Circuit source N M G) :
    (circuit.mapBasis hom).size = circuit.size :=
  rfl

end Circuit

namespace CircuitFamily

theorem function_mapBasis_internal
    (hom : Basis.Hom source target)
    (family : CircuitFamily source) :
    (family.mapBasis hom).function = family.function := by
  funext n input
  cases n with
  | zero => rfl
  | succ n =>
      exact congrFun
        (Circuit.eval_mapBasis_internal hom
          (family.circuit (n + 1)) input) 0

theorem size_mapBasis_internal
    (hom : Basis.Hom source target)
    (family : CircuitFamily source) :
    (family.mapBasis hom).size = family.size := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      exact Circuit.size_mapBasis_internal hom
        (family.circuit (n + 1))

theorem depth_mapBasis_internal
    (hom : Basis.Hom source target)
    (family : CircuitFamily source) :
    (family.mapBasis hom).depth = family.depth := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      exact Circuit.depth_mapBasis_internal hom
        (family.circuit (n + 1))

end CircuitFamily
end Complexity
