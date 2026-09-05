/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Fragment
public import Complexitylib.Circuits.BitString
public import Complexitylib.Circuits.Unrolling.Defs
public import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# Internal correctness of bounded-trace initialization circuits

This file proves the exact size, topological ordering, and iterative-evaluator
semantics of the one-gate-per-atom initialization fragment.
-/


public section

namespace Complexity

namespace CircuitUnrolling

open CircuitCode

/-- Internal exact length of the canonical atom ordering. -/
theorem length_configAtoms_internal (tm : NTM k) (T : ℕ) :
    (configAtoms tm T).length = configWidth tm T := by
  simp [configAtoms]

/-- Internal lookup law connecting arithmetic atom indices to list order. -/
theorem getElem_configAtoms_configIndex_internal (tm : NTM k) (T : ℕ)
    (atom : ConfigAtom tm T) :
    (configAtoms tm T)[configIndex tm T atom]'(by
      simpa [length_configAtoms_internal] using configIndex_lt tm T atom) = atom := by
  simp only [configAtoms, List.getElem_ofFn]
  apply (configAtomEquiv tm T).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  exact (configAtomEquiv_apply_val tm T atom).symm

/-- Internal exact gate count of the initialization fragment. -/
theorem length_initFragment_internal (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) :
    (initFragment tm T n available layout).length = configWidth tm T := by
  simp [initFragment, length_configAtoms_internal]

private theorem InitSource.gate_wellFormedAt (source : InitSource available)
    [NeZero available] : source.gate.WellFormedAt available := by
  have havailable : 0 < available := Nat.pos_of_ne_zero (NeZero.ne available)
  cases source with
  | constant value =>
      cases value <;> simp [InitSource.gate, RawGate.constant, RawGate.WellFormedAt,
        havailable]
  | wire input negated => simp [InitSource.gate, RawGate.copy, RawGate.WellFormedAt,
      input.isLt]

/-- Internal topological well-formedness of initialization gates. -/
theorem initFragment_topologicallyWellFormed_internal (tm : NTM k)
    (T n available : ℕ) [NeZero available] (layout : InputWires T n available) :
    (initFragment tm T n available layout).TopologicallyWellFormed available := by
  intro i
  have hgate :
      ((initFragment tm T n available layout).get i).WellFormedAt available := by
    have hi : (i : ℕ) < (configAtoms tm T).length := by
      simpa [initFragment] using i.isLt
    have hmap : (initFragment tm T n available layout).get i
        = (initSource tm T n available layout ((configAtoms tm T)[(i : ℕ)]'hi)).gate := by
      simp only [List.get_eq_getElem]; exact List.getElem_map _
    rw [hmap]
    exact InitSource.gate_wellFormedAt (available := available) _
  unfold RawGate.WellFormedAt at hgate ⊢
  omega

private theorem InitSource.value_initSource (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) (assignment : Fin available → Bool)
    (x : BitString n) (hx : ∀ i, assignment (layout.data i) = x i)
    (atom : ConfigAtom tm T) :
    (initSource tm T n available layout atom).value assignment =
      atom.value (tm.initCfg x.toList) := by
  cases atom with
  | state q => rfl
  | head tape position =>
      cases tape <;>
        change decide (position.val = 0) = decide (0 = position.val) <;>
        simp only [eq_comm]
  | cell tape position symbol =>
      by_cases hzero : position.val = 0
      · cases tape <;> cases symbol <;>
          simp [initSource, hzero, InitSource.value, ConfigAtom.value,
            TapeSlot.get]
      · have hpositive : position.val - 1 + 1 = position.val := by omega
        cases tape with
        | input =>
            by_cases hdata : position.val - 1 < n
            · let i : Fin n := ⟨position.val - 1, hdata⟩
              have hcell :
                  (Tape.init (x.toList.map Γ.ofBool)).cells position.val =
                    Γ.ofBool (x i) := by
                rw [← hpositive]
                have hi : i.val < x.toList.length := by
                  rw [BitString.length_toList]
                  exact i.isLt
                rw [Tape.init_ofBool_cells_lt x.toList i.val hi]
                congr 1
                exact BitString.getElem_toList x i
              cases symbol <;> simp [initSource, hzero, hdata, InitSource.value,
                ConfigAtom.value, TapeSlot.get, i, hx, hcell] <;>
                cases hxi : x i <;> simp_all [Γ.ofBool]
            · have hge : n ≤ position.val - 1 := Nat.le_of_not_gt hdata
              have hcell :
                  (Tape.init (x.toList.map Γ.ofBool)).cells position.val =
                    Γ.blank := by
                rw [← hpositive]
                exact Tape.init_ofBool_cells_ge x.toList (position.val - 1) (by
                  simpa using hge)
              cases symbol <;> simp [initSource, hzero, hdata, InitSource.value,
                ConfigAtom.value, TapeSlot.get, hcell]
        | work i =>
            have hcell : (Tape.init []).cells position.val = Γ.blank := by
              rw [← hpositive]
              exact Tape.init_nil_cells_succ (position.val - 1)
            cases symbol <;> simp [initSource, hzero, InitSource.value,
              ConfigAtom.value, TapeSlot.get, hcell]
        | output =>
            have hcell : (Tape.init []).cells position.val = Γ.blank := by
              rw [← hpositive]
              exact Tape.init_nil_cells_succ (position.val - 1)
            cases symbol <;> simp [initSource, hzero, InitSource.value,
              ConfigAtom.value, TapeSlot.get, hcell]

private theorem InitSource.evalAux?_gate [NeZero available]
    (source : InitSource available) (assignment : Fin available → Bool)
    (wires : Array Bool)
    (hinput : ∀ i, wires[i.val]? = some (assignment i)) :
    RawCircuit.evalAux? [source.gate] wires =
      some (wires.push (source.value assignment)) := by
  cases source with
  | constant value =>
      have hwitness := hinput (0 : Fin available)
      have hwitness' : wires[0]? = some (assignment (0 : Fin available)) := by
        simpa using hwitness
      cases value <;>
        simp [InitSource.gate, RawGate.constant, RawCircuit.evalAux?,
          RawGate.eval, InitSource.value, hwitness']
  | wire input negated =>
      have hwire := hinput input
      cases negated <;>
        simp [InitSource.gate, RawGate.copy, RawCircuit.evalAux?,
          RawGate.eval, InitSource.value, hwire]

/-- Internal evaluator theorem for a list of one-gate initialization sources. -/
theorem evalAux?_sourceGates_internal (available : ℕ) [NeZero available]
    (sources : List (InitSource available)) (assignment : Fin available → Bool)
    (wires : Array Bool) (hsize : wires.size = available)
    (hinput : ∀ i, wires[i.val]? = some (assignment i)) :
    ∃ result,
      RawCircuit.evalAux? (sources.map InitSource.gate) wires = some result ∧
        result.size = wires.size + sources.length ∧
        (∀ i < wires.size, result[i]? = wires[i]?) ∧
        (∀ (j : ℕ) (hj : j < sources.length),
          result[available + j]? = some ((sources[j]'hj).value assignment)) := by
  induction sources using List.reverseRecOn with
  | nil =>
      refine ⟨wires, by simp [RawCircuit.evalAux?], by simp, ?_, ?_⟩
      · simp
      · intro j hj
        simp at hj
  | append_singleton sources source ih =>
      obtain ⟨result, heval, hresultSize, hprefix, houtputs⟩ := ih
      have hresultInput : ∀ i, result[i.val]? = some (assignment i) := by
        intro i
        rw [hprefix i.val (by omega)]
        exact hinput i
      let final := result.push (source.value assignment)
      refine ⟨final, ?_, ?_, ?_, ?_⟩
      · simp only [List.map_append, List.map_singleton]
        rw [RawCircuit.evalAux?_append, heval]
        exact InitSource.evalAux?_gate source assignment result hresultInput
      · simp [final, hresultSize, Nat.add_assoc]
      · intro i hi
        have hwiresResult : wires.size ≤ result.size := by
          rw [hresultSize]
          omega
        have hine : i ≠ result.size := by omega
        simp only [final, Array.getElem?_push, ite_eq_right hine]
        exact hprefix i hi
      · intro j hj
        have hjbound : j < sources.length + 1 := by simpa using hj
        by_cases hbefore : j < sources.length
        · have hjresult : available + j < result.size := by omega
          rw [show (sources ++ [source])[j]'hj = sources[j]'hbefore by
            exact List.getElem_append_left hbefore]
          simp only [final, Array.getElem?_push, ite_eq_right (Nat.ne_of_lt hjresult)]
          exact houtputs j hbefore
        · have hjlast : j = sources.length := by omega
          subst j
          rw [show (sources ++ [source])[sources.length]'(by simp) = source by simp]
          have hwire : available + sources.length = result.size := by omega
          rw [hwire]
          exact Array.getElem?_push_size

/-- Internal semantic correctness theorem for the initial-configuration fragment. -/
theorem evalAux?_initFragment_internal (tm : NTM k) (T n available : ℕ)
    [NeZero available] (layout : InputWires T n available) {wires : Array Bool}
    (hsize : wires.size = available) (x : BitString n)
    (hx : ∀ i, wires[(layout.data i).val]? = some (x i)) :
    ∃ result,
      RawCircuit.evalAux? (initFragment tm T n available layout) wires = some result ∧
        result.size = wires.size + configWidth tm T ∧
        (∀ i < wires.size, result[i]? = wires[i]?) ∧
        EncodesConfig tm T available result (tm.initCfg x.toList) := by
  let assignment : Fin available → Bool := fun i => wires[i.val]'(by
    rw [hsize]
    exact i.isLt)
  have hinput : ∀ i, wires[i.val]? = some (assignment i) := by
    intro i
    simp [assignment, hsize, i.isLt]
  have hdata : ∀ i, assignment (layout.data i) = x i := by
    intro i
    have hi := hx i
    simpa [assignment, hsize] using hi
  let sources := (configAtoms tm T).map (initSource tm T n available layout)
  obtain ⟨result, heval, hresultSize, hprefix, houtputs⟩ :=
    evalAux?_sourceGates_internal available sources assignment wires hsize hinput
  refine ⟨result, ?_, ?_, hprefix, ?_⟩
  · simpa [sources, initFragment, List.map_map, Function.comp_def] using heval
  · simpa [sources, length_configAtoms_internal] using hresultSize
  · intro atom
    have hindex : configIndex tm T atom < (configAtoms tm T).length := by
      simpa [length_configAtoms_internal] using configIndex_lt tm T atom
    have hsourceIndex :
        sources[configIndex tm T atom]'(by simpa [sources] using hindex) =
          initSource tm T n available layout atom := by
      simp only [sources, List.getElem_map]
      rw [getElem_configAtoms_configIndex_internal]
    have houtput := houtputs (configIndex tm T atom) (by
      simpa [sources] using hindex)
    rw [hsourceIndex] at houtput
    rw [InitSource.value_initSource tm T n available layout assignment x hdata atom]
      at houtput
    exact houtput

end CircuitUnrolling

end Complexity
