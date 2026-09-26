/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.StraightLine.Defs
public import Complexitylib.Circuits.Dependency.Defs

/-!
# Typed circuits as CSLib straight-line programs

This file proves that `Circuit.toStraightLine`, which turns a typed circuit
over a basis `B` into a CSLib circuit over `B.signature`, preserves the computed
function, the size, and the total fan-in, and that its outputs are gates
(`Cslib.Circuits.Circuit.GatedOutputs`). It is the correspondence on which the
move of Complexitylib's circuit developments to CSLib's model rests (see
`ROADMAP.md`, item 7). The correspondence proved here runs one way, from typed
circuits to CSLib circuits; the translation back is not yet formalized.

## Main results

- `Complexity.Basis.interpretation_kind` — the interpretation of a gate's kind
  is the gate's evaluation
- `Complexity.StraightLine.eval_ofLines` — each gate of a program built from
  lines evaluates its line on the values of the earlier gates
- `Complexity.StraightLine.index_wireOfIndex` — the wire with index `w` in the
  typed layout has CSLib index `w`
- `Complexity.Circuit.eval_toStraightLine` — the translation computes what the
  typed circuit computes
- `Complexity.Circuit.size_toStraightLine` — the translation has the typed
  circuit's size
- `Complexity.Circuit.gatedOutputs_toStraightLine` — every output of the
  translation is an internal gate
- `Complexity.Circuit.totalFanIn_toStraightLine` — the translation has the typed
  circuit's total fan-in
-/


public section

namespace Complexity

open Cslib.Circuits

/-- The interpretation of a gate's kind, applied to the values of the gate's
input wires, is the gate's evaluation: `Basis.interpretation` negates the
flagged inputs and applies the operation exactly as `Gate.eval` does. -/
theorem Basis.interpretation_kind {B : Basis} {W : ℕ} (g : Gate B W) (v : BitString W) :
    B.interpretation g.kind (v ∘ g.inputs) = g.eval v :=
  rfl

namespace StraightLine

variable {σ : Signature} {N : ℕ} {U : Type*}

/-- The wire with index `w` in the layout of typed circuits has CSLib index
`w`. -/
@[simp] theorem index_wireOfIndex {j : ℕ} (w : ℕ) (hw : w < N + j) :
    (wireOfIndex w hw).index = ⟨w, hw⟩ := by
  unfold wireOfIndex
  split
  · rfl
  · next h => exact Fin.ext (by simp; omega)

/-- Each gate of `Program.ofLines g lines` evaluates its line on the values of
the earlier gates. -/
theorem eval_ofLines (I : Interpretation σ U) (x : Fin N → U) :
    ∀ (g : ℕ) (lines : (j : Fin g) → Line σ N j) (j : Fin g),
      (Program.ofLines g lines).eval I x j =
        (lines j).eval I x fun k => (Program.ofLines g lines).eval I x (Fin.castLE (by omega) k)
  | 0, _, j => j.elim0
  | g + 1, lines, j => by
    induction j using Fin.lastCases with
    | last =>
      rw [Program.ofLines, Program.eval_gate_last]
      congr 1
      funext k
      rw [show (Fin.castLE (by omega) k : Fin (g + 1)) = Fin.castSucc k from Fin.ext rfl,
        Program.eval_gate_castSucc]
    | cast j =>
      rw [Program.ofLines, Program.eval_gate_castSucc, eval_ofLines I x g]
      congr 1
      funext k
      rw [show (Fin.castLE (by omega) k : Fin (g + 1)) = Fin.castSucc (Fin.castLE (by omega) k)
        from Fin.ext rfl, Program.eval_gate_castSucc]

end StraightLine

namespace Circuit

variable {B : Basis} {N M G : ℕ} [NeZero N] [NeZero M]

/-- The value of position `j` of the straight-line form: internal gate `j` for
`j < G`, and output gate `j - G` otherwise. -/
private def straightLineValue (c : Circuit B N M G) (x : BitString N) (j : Fin (G + M)) :
    Bool :=
  if h : j.val < G then c.wireValue x ⟨N + j, by omega⟩
  else (c.outputs ⟨j - G, by omega⟩).eval (c.wireValue x)

/-- Wire `N + i` carries the value of internal gate `i`. -/
private theorem wireValue_natAdd (c : Circuit B N M G) (x : BitString N) (i : ℕ) (hi : i < G)
    (h : N + i < N + G) :
    c.wireValue x ⟨N + i, h⟩ = (c.gates ⟨i, hi⟩).eval (c.wireValue x) := by
  rw [wireValue_of_not_lt _ _ _ (by simp)]
  congr 2
  exact Fin.ext (by simp)

/-- A wire below position `j` reads the typed circuit's wire value, provided the
positions before `j` hold their typed values. -/
private theorem elim_wireOfIndex (c : Circuit B N M G) (x : BitString N) (j : Fin (G + M))
    (w : ℕ) (hw : w < N + j) (hG : w < N + G) :
    Wire.elim x (fun k : Fin j => c.straightLineValue x (Fin.castLE (by omega) k))
        (StraightLine.wireOfIndex w hw) = c.wireValue x ⟨w, hG⟩ := by
  unfold StraightLine.wireOfIndex
  split
  · next h => rw [Wire.elim_input, wireValue_of_lt _ _ _ h]
  · next h =>
    have hlt : w - N < G := by omega
    rw [Wire.elim_gate, straightLineValue]
    simp only [Fin.val_castLE, hlt, ↓reduceDIte]
    congr 1
    exact Fin.ext (by simp; omega)

/-- Every position of the straight-line form holds its typed value. -/
private theorem eval_straightLine (c : Circuit B N M G) (x : BitString N) :
    ∀ (bound : ℕ) (j : Fin (G + M)), j.val < bound →
      (Program.ofLines (G + M) c.straightLineAt).eval B.interpretation x j =
        c.straightLineValue x j
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | bound + 1, j, hj => by
    have hvalues : ∀ k : Fin j,
        (Program.ofLines (G + M) c.straightLineAt).eval B.interpretation x
            (Fin.castLE (by omega) k) = c.straightLineValue x (Fin.castLE (by omega) k) :=
      fun k => eval_straightLine c x bound _ (by simp; omega)
    rw [StraightLine.eval_ofLines]
    simp only [hvalues]
    rw [straightLineAt, straightLineValue]
    by_cases h : j.val < G
    · simp only [h, ↓reduceDIte]
      rw [wireValue_natAdd c x j h]
      simp only [Line.eval, Function.comp_def, Basis.interpretation, Gate.kind, Gate.eval]
      congr 1
      funext k
      rw [elim_wireOfIndex c x j _ _ (by omega)]
    · simp only [h, ↓reduceDIte]
      simp only [Line.eval, Function.comp_def, Basis.interpretation, Gate.kind, Gate.eval]
      congr 1
      funext k
      rw [elim_wireOfIndex c x j _ _ ((c.outputs _).inputs k).isLt]

/-- **The straight-line form computes what the typed circuit computes.** -/
theorem eval_toStraightLine (c : Circuit B N M G) (x : BitString N) :
    c.toStraightLine.eval B.interpretation x = c.eval x := by
  funext o
  have h := eval_straightLine c x (G + M + 1) (Fin.natAdd G o) (by omega)
  have hout : ¬ ((Fin.natAdd G o : Fin (G + M)) : ℕ) < G := by simp
  simp only [straightLineValue, hout, ↓reduceDIte] at h
  simp only [Cslib.Circuits.Circuit.eval, toStraightLine, Function.comp_apply,
    Program.trace_gateWire, Program.gateFunction_apply, h]
  congr 2
  exact Fin.ext (by simp)

/-- **The straight-line form has the typed circuit's size.** -/
theorem size_toStraightLine (c : Circuit B N M G) : c.toStraightLine.size = c.size :=
  rfl

/-- **The straight-line form has gated outputs.** Its outputs are the last `M`
gates, the typed circuit's output gates, never an original input. -/
theorem gatedOutputs_toStraightLine (c : Circuit B N M G) : c.toStraightLine.GatedOutputs :=
  fun _ => trivial

/-- **The straight-line form has the typed circuit's total fan-in.** CSLib's
`Circuit.totalFanIn` of the translation, the sum of the arities of its lines,
equals the typed circuit's `Circuit.totalFanIn`, the sum of the fan-ins of its
internal and output gates. -/
theorem totalFanIn_toStraightLine (c : Circuit B N M G) :
    c.toStraightLine.totalFanIn = c.totalFanIn := by
  change (Program.ofLines (G + M) c.straightLineAt).totalFanIn = _
  rw [Program.totalFanIn_eq_sum_lines, Circuit.totalFanIn, Fin.sum_univ_add]
  simp only [Program.lines_ofLines, Line.mapWires]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [straightLineAt, Basis.signature, Gate.kind]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have h : ¬ ((Fin.natAdd G j : Fin (G + M)) : ℕ) < G := by simp
    simp only [straightLineAt, h, ↓reduceDIte]
    show (c.outputs _).fanIn = _
    congr 2
    exact Fin.ext (by simp)

end Circuit

end Complexity
