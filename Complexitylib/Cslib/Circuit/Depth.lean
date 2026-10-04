/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Cslib.Circuit.Program
public import Cslib.Computability.Circuit.Composition

/-!
# Depth of parallel CSLib circuits

Continuing a program preserves the depths of its existing wires. If the
continuation reads only primary inputs, its wires also retain their original
depths. Consequently, parallel composition takes the maximum output depth.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n k g h m r : ℕ}

@[simp] theorem Program.wireDepths_gate_last (p : Program σ n g) (l : Line σ n g) :
    (p.gate l).wireDepths (.gate (Fin.last g)) = l.depth p.wireDepths := by
  simp [Program.wireDepths, Program.depths]

/-- Existing wires keep their depths under continuation. -/
theorem Program.wireDepths_append_castAdd (p : Program σ n g)
    (feed : Fin k → Wire n g) (q : Program σ k h) (w : Wire n g) :
    (p.append feed q).wireDepths (w.castAdd h) = p.wireDepths w := by
  induction q with
  | empty => cases w <;> rfl
  | gate q l ih => cases w <;> exact (Program.wireDepths_gate_castSucc _ _ _).trans ih

/-- A continuation fed by primary inputs retains its own wire depths. -/
theorem Program.wireDepths_append_input (p : Program σ n g) (select : Fin k → Fin n)
    (q : Program σ k h) (w : Wire k h) :
    (p.append (Wire.input ∘ select) q).wireDepths
      (Program.appendedWire (Wire.input ∘ select) w) = q.wireDepths w := by
  induction q with
  | empty => cases w with
    | input i => rfl
    | gate j => exact j.elim0
  | @gate h q l ih =>
    cases w with
    | input i => exact Program.wireDepths_append_castAdd p _ (q.gate l) (Wire.input (select i))
    | gate j =>
      refine Fin.lastCases ?_ (fun j => ?_) j
      · change (p.append (Wire.input ∘ select) (q.gate l)).wireDepths
          (Wire.gate (Fin.last (g + h))) = _
        dsimp only [Program.append]
        simp only [Program.wireDepths, Program.depths, Wire.elim, Fin.lastCases_last]
        rw [@Fin.lastCases_last (g + h) (fun _ => ℕ)]
        unfold Line.depth Line.mapWires
        change (Fin.foldl (σ.Arity l.op) (fun depth i => max depth
          ((p.append (Wire.input ∘ select) q).wireDepths
            (Program.appendedWire (Wire.input ∘ select) (l.wires i)))) 0).succ = _
        simp only [ih]
        rfl
      · exact (Program.wireDepths_gate_castSucc _ _ (.gate (Fin.natAdd _ j))).trans
          ((ih (.gate j)).trans (Program.wireDepths_gate_castSucc q l (.gate j)).symm)

/-- The circuit depth is bounded exactly when every output depth is bounded. -/
theorem Circuit.depth_le_iff (c : Circuit σ n m) (d : ℕ) :
    c.depth ≤ d ↔ ∀ i, c.outputDepths i ≤ d := by
  constructor
  · intro h i
    exact (Algebraic.Fin.le_foldl_max c.outputDepths 0 i).trans h
  · intro h
    exact Algebraic.Fin.foldl_max_le _ _ _ (Nat.zero_le _) h

/-- Parallel composition preserves the depths of the left outputs. -/
@[simp] theorem Circuit.outputDepths_append_left (c : Circuit σ n m)
    (d : Circuit σ n r) (i : Fin m) :
    (c.append d).outputDepths (Fin.castAdd r i) = c.outputDepths i := by
  simp only [Circuit.outputDepths, Circuit.append, Function.comp_apply, Fin.append_left]
  exact Program.wireDepths_append_castAdd ..

/-- Parallel composition preserves the depths of the right outputs. -/
@[simp] theorem Circuit.outputDepths_append_right (c : Circuit σ n m)
    (d : Circuit σ n r) (i : Fin r) :
    (c.append d).outputDepths (Fin.natAdd m i) = d.outputDepths i := by
  simp only [Circuit.outputDepths, Circuit.append, Function.comp_apply, Fin.append_right]
  exact Program.wireDepths_append_input c.program (fun i => i) d.program _

/-- A common depth bound survives parallel composition. -/
theorem Circuit.depth_append_le (c : Circuit σ n m) (d : Circuit σ n r) (b : ℕ)
    (hc : c.depth ≤ b) (hd : d.depth ≤ b) : (c.append d).depth ≤ b := by
  apply (Circuit.depth_le_iff _ _).2
  intro i
  induction i using Fin.addCases with
  | left i => simpa using (c.depth_le_iff b).1 hc i
  | right i => simpa using (d.depth_le_iff b).1 hd i

end Cslib.Circuits
