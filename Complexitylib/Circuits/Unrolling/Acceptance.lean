/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.ToCircuit
public import Complexitylib.Circuits.Unrolling.Acceptance.Defs
public import Complexitylib.Circuits.Unrolling.Acceptance.Internal.Evaluation
public import Complexitylib.Circuits.Unrolling.Acceptance.Internal.Structure
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Acceptance circuits for bounded Turing-machine traces

This module appends the actual acceptance bit to a bounded trace: one final AND
gate tests that the machine is halted and that output cell one contains `1`.
The raw circuit is topologically well formed, has cubic size, and reconstructs
to a typed fan-in-two circuit whose output is exactly the predicate counted by
`NTM.acceptCount`.

The canonical constructor places choice bits before input-data bits. Its input
arity must be positive; circuit families continue to handle the unique
zero-length case separately.

## Main results

- `acceptanceRawCircuit_wellFormed`: the raw circuit is valid.
- `eval?_acceptanceRawCircuit`: raw evaluation returns the acceptance bit.
- `acceptanceCircuit_eval`: typed evaluation has the same semantics.
- `canonicalAcceptanceCircuit_eval`: canonical choices-first semantics.
- `canonicalAcceptanceCircuit_size_le`: canonical cubic size bound.
- `card_acceptingChoices_eq_acceptCount`: circuit acceptance counts machine
  accepting paths exactly.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- Appending the final acceptance test adds exactly one gate. -/
@[simp] theorem length_acceptanceRawCircuit (tm : NTM k)
    (T n available : ℕ) (layout : InputWires T n available) :
    (acceptanceRawCircuit tm T n available layout).length =
      traceFragmentSize tm T n available layout + 1 :=
  length_acceptanceRawCircuit_internal tm T n available layout

/-- The raw acceptance circuit is topologically ordered after any nonempty
primary-input prefix. -/
theorem acceptanceRawCircuit_topologicallyWellFormed
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) :
    (acceptanceRawCircuit tm T n available layout).TopologicallyWellFormed
      available :=
  acceptanceRawCircuit_topologicallyWellFormed_internal tm T n available layout

/-- The raw acceptance circuit is nonempty and topologically well formed. -/
theorem acceptanceRawCircuit_wellFormed
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) :
    (acceptanceRawCircuit tm T n available layout).WellFormed available :=
  acceptanceRawCircuit_wellFormed_internal tm T n available layout

/-- The raw acceptance circuit retains the trace compiler's cubic size bound. -/
theorem length_acceptanceRawCircuit_le (tm : NTM k)
    (T n available : ℕ) (layout : InputWires T n available) :
    (acceptanceRawCircuit tm T n available layout).length ≤
      acceptanceSizeCoeff tm * (T + 2) ^ 3 :=
  length_acceptanceRawCircuit_le_internal tm T n available layout

/-- Evaluating the raw acceptance circuit appends the final acceptance bit to
the successfully evaluated trace array. -/
theorem evalAux?_acceptanceRawCircuit
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) (x : BitString n)
    (choices : Fin T → Bool) (wires : Array Bool)
    (hsize : wires.size = available)
    (hdata : ∀ j, wires[(layout.data j).val]? = some (x j))
    (hchoices : ∀ j, wires[(layout.choice j).val]? = some (choices j)) :
    ∃ traceResult,
      CircuitCode.RawCircuit.evalAux?
          (acceptanceRawCircuit tm T n available layout) wires =
        some (traceResult.push (decide (
          (tm.trace T choices (tm.initCfg x.toList)).state = tm.qhalt ∧
            (tm.trace T choices (tm.initCfg x.toList)).output.cells 1 = Γ.one))) ∧
      traceResult.size =
        wires.size + traceFragmentSize tm T n available layout ∧
      (∀ i < wires.size, traceResult[i]? = wires[i]?) ∧
      EncodesConfig tm T (traceOutputBase tm T n available layout) traceResult
        (tm.trace T choices (tm.initCfg x.toList)) :=
  evalAux?_acceptanceRawCircuit_internal tm T n available layout x choices
    wires hsize hdata hchoices

/-- Raw single-output evaluation returns exactly the bounded-trace acceptance
predicate. -/
theorem eval?_acceptanceRawCircuit
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) (x : BitString n)
    (choices : Fin T → Bool) (input : BitString available)
    (hdata : ∀ j, input (layout.data j) = x j)
    (hchoices : ∀ j, input (layout.choice j) = choices j) :
    CircuitCode.RawCircuit.eval?
        (acceptanceRawCircuit tm T n available layout) input.toList =
      some (decide (
        (tm.trace T choices (tm.initCfg x.toList)).state = tm.qhalt ∧
          (tm.trace T choices (tm.initCfg x.toList)).output.cells 1 = Γ.one)) :=
  eval?_acceptanceRawCircuit_internal tm T n available layout x choices input
    hdata hchoices

/-- Reconstruct the valid raw acceptance code as a typed fan-in-two circuit.
The final raw gate becomes the sole typed output gate. -/
noncomputable def acceptanceCircuit
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) :
    Circuit Basis.andOr2 available 1
      ((acceptanceRawCircuit tm T n available layout).length - 1) :=
  (acceptanceRawCircuit tm T n available layout).toCircuit available
    (acceptanceRawCircuit_wellFormed tm T n available layout)

/-- Typed reconstruction preserves the exact raw gate count. -/
@[simp] theorem acceptanceCircuit_size
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) :
    (acceptanceCircuit tm T n available layout).size =
      traceFragmentSize tm T n available layout + 1 := by
  rw [acceptanceCircuit,
    CircuitCode.RawCircuit.size_toCircuit,
    length_acceptanceRawCircuit]

/-- The typed acceptance circuit has the same machine-dependent cubic size
bound as its raw representation. -/
theorem acceptanceCircuit_size_le
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) :
    (acceptanceCircuit tm T n available layout).size ≤
      acceptanceSizeCoeff tm * (T + 2) ^ 3 := by
  rw [acceptanceCircuit_size]
  simpa only [length_acceptanceRawCircuit] using
    length_acceptanceRawCircuit_le tm T n available layout

/-- The typed acceptance circuit computes the exact halt-and-output predicate
of the bounded machine trace represented by its primary inputs. -/
theorem acceptanceCircuit_eval
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) (x : BitString n)
    (choices : Fin T → Bool) (input : BitString available)
    (hdata : ∀ j, input (layout.data j) = x j)
    (hchoices : ∀ j, input (layout.choice j) = choices j) :
    ((acceptanceCircuit tm T n available layout).eval input) 0 =
      decide ((tm.trace T choices (tm.initCfg x.toList)).state = tm.qhalt ∧
        (tm.trace T choices (tm.initCfg x.toList)).output.cells 1 = Γ.one) := by
  have hbridge := CircuitCode.RawCircuit.eval?_toCircuit available
    (acceptanceRawCircuit tm T n available layout)
    (acceptanceRawCircuit_wellFormed tm T n available layout) input
  rw [eval?_acceptanceRawCircuit tm T n available layout x choices input
    hdata hchoices] at hbridge
  exact (Option.some.inj hbridge).symm

/-- Canonical choices-first, data-second acceptance circuit. -/
noncomputable def canonicalAcceptanceCircuit
    (tm : NTM k) (T n : ℕ) [NeZero (T + n)] :
    Circuit Basis.andOr2 (T + n) 1
      ((acceptanceRawCircuit tm T n (T + n) (prefixInputWires T n)).length - 1) :=
  acceptanceCircuit tm T n (T + n) (prefixInputWires T n)

/-- Under the canonical layout, evaluating on `choices ++ x` returns the
machine's bounded-trace acceptance bit. -/
theorem canonicalAcceptanceCircuit_eval
    (tm : NTM k) (T n : ℕ) [NeZero (T + n)]
    (choices : BitString T) (x : BitString n) :
    ((canonicalAcceptanceCircuit tm T n).eval (Fin.append choices x)) 0 =
      decide ((tm.trace T choices (tm.initCfg x.toList)).state = tm.qhalt ∧
        (tm.trace T choices (tm.initCfg x.toList)).output.cells 1 = Γ.one) := by
  apply acceptanceCircuit_eval tm T n (T + n) (prefixInputWires T n)
  · intro j
    have hdata : (prefixInputWires T n).data j = Fin.natAdd T j := by
      apply Fin.ext
      simp
    rw [hdata, Fin.append_right]
  · intro j
    have hchoice : (prefixInputWires T n).choice j = Fin.castAdd n j := by
      apply Fin.ext
      rfl
    rw [hchoice, Fin.append_left]

/-- The canonical choices-first acceptance circuit inherits the generic cubic
size bound. -/
theorem canonicalAcceptanceCircuit_size_le
    (tm : NTM k) (T n : ℕ) [NeZero (T + n)] :
    (canonicalAcceptanceCircuit tm T n).size ≤
      acceptanceSizeCoeff tm * (T + 2) ^ 3 :=
  acceptanceCircuit_size_le tm T n (T + n) (prefixInputWires T n)

/-- The number of canonical choice strings accepted by the circuit is exactly
the machine's bounded accepting-path count. -/
theorem card_acceptingChoices_eq_acceptCount
    (tm : NTM k) (T n : ℕ) [NeZero (T + n)] (x : BitString n) :
    (Finset.univ.filter fun choices : BitString T =>
      ((canonicalAcceptanceCircuit tm T n).eval (Fin.append choices x)) 0 = true).card =
        tm.acceptCount x.toList T := by
  unfold NTM.acceptCount
  apply congrArg Finset.card
  ext choices
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [canonicalAcceptanceCircuit_eval]
  simp

end CircuitUnrolling

end Complexity
