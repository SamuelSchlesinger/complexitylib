/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Cslib.Computability.Circuit.Basic
public import Complexitylib.Algebraic.Cost
public import Complexitylib.Algebraic.Fin

/-!
# Building, measuring, and bounding CSLib programs

This file extends CSLib's straight-line programs (`Cslib.Circuits.Program`):

- `Program.ofLines` builds the program whose gate `j` computes a given line
  reading the inputs and the `j` gates before it; `Program.lines_ofLines`
  reads those lines back, widened by `Program.wireCastLE`.
- `Program.depths_eq_lines_depth` states CSLib's depth equation line by line,
  and `Program.wireDepths_le` bounds every wire's depth by any certificate
  that bounds each line's depth at its own wire.
- `Program.totalFanIn` and `Circuit.totalFanIn` count the wires read by all
  gates. They are the weighted cost `Program.cost` from
  `Complexitylib.Algebraic.Cost` in which each operation costs its arity, so
  that API (for instance `Program.cost_eq_sum_lines`) applies to them.

This file lives in `Complexitylib/Cslib/` because it extends CSLib types in
their home namespace `Cslib.Circuits`; its contents are candidates for
upstreaming to CSLib.

## Main definitions

- `Cslib.Circuits.Program.ofLines` — a program from its lines
- `Cslib.Circuits.Program.wireCastLE` — a wire of a shorter program, widened
- `Cslib.Circuits.Program.totalFanIn`, `Cslib.Circuits.Circuit.totalFanIn` —
  the total fan-in

## Main results

- `Cslib.Circuits.Program.lines_ofLines` — the lines of `Program.ofLines`
- `Cslib.Circuits.Program.depths_eq_lines_depth` — CSLib's depth equation,
  line by line
- `Cslib.Circuits.Program.wireDepths_le` — bounding CSLib depth by a
  line-wise certificate
-/

@[expose] public section

namespace Cslib.Circuits

open scoped BigOperators

variable {σ : Signature} {N g : ℕ}

/-- A valuation of wires is the valuation of their indices that lists the
inputs and then the gates. -/
theorem Wire.elim_eq_addCases_index {α : Sort*} (x : Fin N → α) (v : Fin g → α)
    (w : Wire N g) : Wire.elim x v w = Fin.addCases x v w.index := by
  cases w <;> simp

/-- Widening a wire into a longer program keeps its CSLib depth. -/
theorem Program.wireDepths_gate_castSucc (p : Program σ N g) (line : Line σ N g)
    (w : Wire N g) : (p.gate line).wireDepths w.castSucc = p.wireDepths w := by
  cases w <;> simp [Program.wireDepths, Program.depths]

/-- Line `j` of a program has the CSLib depth of gate `j`. -/
theorem Program.depths_eq_lines_depth (p : Program σ N g) (j : Fin g) :
    p.depths j = (p.lines j).depth p.wireDepths := by
  induction p with
  | empty => exact j.elim0
  | @gate g p line ih =>
    have hmap (l : Line σ N g) :
        (l.mapWires Wire.Renaming.castSucc).depth (p.gate line).wireDepths =
          l.depth p.wireDepths := by
      simp only [Line.depth, Line.mapWires, Function.comp_apply, Wire.Renaming.castSucc_apply,
        Program.wireDepths_gate_castSucc]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [Program.lines_gate_last, hmap]
      simp only [Program.depths, Fin.lastCases_last]
      rfl
    · rw [Program.lines_gate_castSucc, hmap, ← ih]
      simp [Program.depths]

/-- The program whose line `j` is `F j`, a line reading only the inputs and the
`j` gates before it. -/
def Program.ofLines : (g : ℕ) → ((j : Fin g) → Line σ N j) → Program σ N g
  | 0, _ => .empty
  | g + 1, F => .gate (Program.ofLines g fun j => F j.castSucc) (F (Fin.last g))

/-- Regard a wire of a program with `j` gates as a wire of a program with
`g ≥ j` gates, extending the first. -/
def Program.wireCastLE {j g : ℕ} (h : j ≤ g) : Wire N j → Wire N g :=
  Wire.elim Wire.input fun k => Wire.gate (Fin.castLE h k)

/-- Widening a wire keeps its index. -/
@[simp] theorem Program.index_wireCastLE {j g : ℕ} (h : j ≤ g) (w : Wire N j) :
    (Program.wireCastLE h w).index = Fin.castLE (Nat.add_le_add_left h N) w.index := by
  cases w <;> exact Fin.ext rfl

/-- The lines of `Program.ofLines` are the given lines, widened. -/
theorem Program.lines_ofLines (g : ℕ) (F : (j : Fin g) → Line σ N j) (j : Fin g) :
    (Program.ofLines g F).lines j = (F j).mapWires (Program.wireCastLE j.isLt.le) := by
  induction g with
  | zero => exact j.elim0
  | succ g ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [Program.ofLines, Program.lines_gate_last]
      rfl
    · rw [Program.ofLines, Program.lines_gate_castSucc, ih]
      simp only [Line.mapWires]
      congr 1
      funext a
      simp only [Function.comp_apply, Wire.Renaming.castSucc_apply]
      generalize (F j.castSucc).wires a = w
      cases w with
      | input i => rfl
      | gate k => exact congrArg Wire.gate (Fin.ext rfl)

/-- A line's depth is monotone in the depths of the wires it reads. -/
theorem Line.depth_mono {g : ℕ} (l : Line σ N g) {d e : Wire N g → ℕ}
    (h : ∀ a, d (l.wires a) ≤ e (l.wires a)) : l.depth d ≤ l.depth e :=
  Nat.succ_le_succ <| Algebraic.Fin.foldl_max_le _ _ _ (Nat.zero_le _) fun k =>
    (h k).trans (Algebraic.Fin.le_foldl_max (fun k => e (l.wires k)) 0 k)

/-- **Bounding CSLib depth by a line-wise certificate.** If `b` bounds every
line's depth at the line's own wire, it bounds every wire's depth. -/
theorem Program.wireDepths_le (p : Program σ N g) (b : Wire N g → ℕ)
    (hb : ∀ j, (p.lines j).depth b ≤ b (Wire.gate j)) (w : Wire N g) :
    p.wireDepths w ≤ b w := by
  have hg : ∀ n (j : Fin g), j.val = n → p.depths j ≤ b (Wire.gate j) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro j hj
    rw [Program.depths_eq_lines_depth]
    refine le_trans (Line.depth_mono _ fun a => ?_) (hb j)
    have hlt := Program.lines_wires_lt p j a
    generalize (p.lines j).wires a = w at hlt ⊢
    cases w with
    | input i => simp [Program.wireDepths]
    | gate k =>
      simp only [Program.wireDepths, Wire.elim_gate]
      exact ih k (by simp at hlt; omega) k rfl
  cases w with
  | input i => simp [Program.wireDepths]
  | gate j => exact hg _ j rfl

/-- The total fan-in of a program: the number of wires read by all its gates,
counted with multiplicity. It is the program's cost when every operation costs
its arity. -/
def Program.totalFanIn (p : Program σ N g) : ℕ :=
  p.cost σ.Arity

/-- The total fan-in is the cost charging each operation its arity. -/
theorem Program.totalFanIn_eq_cost (p : Program σ N g) : p.totalFanIn = p.cost σ.Arity :=
  rfl

/-- The empty program reads no wires. -/
@[simp] theorem Program.totalFanIn_empty : (Program.empty : Program σ N 0).totalFanIn = 0 :=
  rfl

/-- A new gate adds its arity to the total fan-in. -/
@[simp] theorem Program.totalFanIn_gate (p : Program σ N g) (line : Line σ N g) :
    (p.gate line).totalFanIn = p.totalFanIn + σ.Arity line.op :=
  rfl

/-- The total fan-in is the sum of the arities of the program's lines. -/
theorem Program.totalFanIn_eq_sum_lines (p : Program σ N g) :
    p.totalFanIn = ∑ j : Fin g, σ.Arity (p.lines j).op :=
  p.cost_eq_sum_lines σ.Arity

/-- The total fan-in of a circuit: the number of wires read by all its gates,
counted with multiplicity. Designated outputs read nothing. -/
def Circuit.totalFanIn {m : ℕ} (c : Circuit σ N m) : ℕ :=
  c.program.totalFanIn

/-- The total fan-in of a circuit is the cost charging each operation its
arity. -/
theorem Circuit.totalFanIn_eq_cost {m : ℕ} (c : Circuit σ N m) :
    c.totalFanIn = c.cost σ.Arity :=
  rfl

/-- A circuit's total fan-in is its program's. -/
@[simp] theorem Circuit.totalFanIn_mk {m g : ℕ} (p : Program σ N g)
    (outputs : Fin m → Wire N g) : (⟨p, outputs⟩ : Circuit σ N m).totalFanIn = p.totalFanIn :=
  rfl

/-- A wiring has no gates, so it reads no wires. -/
@[simp] theorem Circuit.totalFanIn_wiring {m : ℕ} (select : Fin m → Fin N) :
    (Circuit.wiring σ select).totalFanIn = 0 :=
  rfl

end Cslib.Circuits
