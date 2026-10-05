/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Basic

/-!
# Facts about straight-line programs

Upstreaming candidates for `Cslib.Computability.Circuit.Program`:

* `Program.lines_wires_eq_gate_lt`: a gate reads only earlier gates.
* `Program.FanInAtMost.arity_le`: under a fan-in bound, every line has bounded arity.
* `Program.trace_gate`: the value of a gate is its operation applied to the values of its
  arguments.
* `Program.Upstream` and `Program.trace_congr_of_upstream`: the value of a wire depends only
  on the inputs upstream of it.
* `Circuit.innerSize`: the number of gates of positive arity. Gates of arity zero are
  constants, leaves of the circuit like its inputs.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n s : ℕ}

/-- The argument wires of a gate are original inputs or earlier gates. -/
theorem Program.lt_of_gate_mem_range_wires (p : Program σ n s) (g : Fin s) {g' : Fin s}
    (h : Wire.gate g' ∈ Set.range (p.lines g).wires) : g' < g := by
  induction p with
  | empty => exact g.elim0
  | @gate s p line ih =>
    refine Fin.lastCases (motive := fun g =>
      Wire.gate g' ∈ Set.range ((p.gate line).lines g).wires → g' < g) ?_ (fun g₀ h => ?_) g h
    · rw [Program.lines_gate_last]
      rintro ⟨a, ha⟩
      change Wire.Renaming.castSucc (line.wires a) = _ at ha
      rw [Wire.Renaming.castSucc_apply] at ha
      generalize line.wires a = w at ha
      cases w with
      | input i => cases ha
      | gate g'' => cases ha; exact Fin.castSucc_lt_last g''
    · rw [Program.lines_gate_castSucc] at h
      obtain ⟨a, ha⟩ := h
      change Wire.Renaming.castSucc ((p.lines g₀).wires a) = _ at ha
      rw [Wire.Renaming.castSucc_apply] at ha
      generalize hw : (p.lines g₀).wires a = w at ha
      cases w with
      | input i => cases ha
      | gate g'' =>
        cases ha
        exact Fin.castSucc_lt_castSucc_iff.mpr (ih g₀ ⟨a, hw⟩)

/-- A gate reads only original inputs and earlier gates. -/
theorem Program.lines_wires_eq_gate_lt (p : Program σ n s) (g : Fin s)
    (a : Fin (σ.Arity (p.lines g).op)) {g' : Fin s} (h : (p.lines g).wires a = .gate g') :
    g' < g :=
  p.lt_of_gate_mem_range_wires g ⟨a, h⟩

/-- Under a fan-in bound, every line of a program has bounded arity. -/
theorem Program.FanInAtMost.arity_le {p : Program σ n s} {r : ℕ} (h : p.FanInAtMost r)
    (g : Fin s) : σ.Arity (p.lines g).op ≤ r := by
  induction p with
  | empty => exact g.elim0
  | @gate s p line ih =>
    obtain ⟨hp, hline⟩ := h
    refine Fin.lastCases ?_ (fun g₀ => ?_) g
    · rw [Program.lines_gate_last, Line.mapWires_op]; exact hline
    · rw [Program.lines_gate_castSucc, Line.mapWires_op]; exact ih hp g₀

/-- The value of a gate is its operation applied to the values of its argument wires. -/
theorem Program.trace_gate {U : Type*} (p : Program σ n s) (I : Interpretation σ U)
    (x : Fin n → U) (g : Fin s) :
    p.trace I x (.gate g) = I (p.lines g).op fun a => p.trace I x ((p.lines g).wires a) := by
  rw [Program.trace_gateWire, Program.gateFunction_apply, ← Program.lines_eval]
  rfl

/-- `p.Upstream w v`: the wire `v` is `w` itself or an argument of a gate upstream of `w`. The
value of `w` can depend only on the wires upstream of it. -/
inductive Program.Upstream (p : Program σ n s) (w : Wire n s) : Wire n s → Prop
  /-- Every wire is upstream of itself. -/
  | refl : p.Upstream w w
  /-- The arguments of a gate upstream of `w` are upstream of `w`. -/
  | arg {g : Fin s} (a : Fin (σ.Arity (p.lines g).op)) :
      p.Upstream w (.gate g) → p.Upstream w ((p.lines g).wires a)

theorem Program.Upstream.trans {p : Program σ n s} {u v w : Wire n s} (huv : p.Upstream u v)
    (hvw : p.Upstream v w) : p.Upstream u w := by
  induction hvw with
  | refl => exact huv
  | arg a _ ih => exact .arg a ih

/-- The value of a wire depends only on the inputs upstream of it. -/
theorem Program.trace_congr_of_upstream {U : Type*} (p : Program σ n s) (I : Interpretation σ U)
    {x y : Fin n → U} {w : Wire n s} (h : ∀ i, p.Upstream w (.input i) → x i = y i) :
    ∀ v, p.Upstream w v → p.trace I x v = p.trace I y v
  | .input i, hv => h i hv
  | .gate g, hg => by
    rw [p.trace_gate, p.trace_gate]
    congr 1
    funext a
    exact p.trace_congr_of_upstream I h _ (.arg a hg)
termination_by v => match v with | .input _ => 0 | .gate g => g.val + 1
decreasing_by
  generalize hw' : (p.lines g).wires a = w' at *
  cases w' with
  | input => simp
  | gate g' => simpa using p.lines_wires_eq_gate_lt g a hw'

/-- The *inner* gates of a program: those of positive arity. A gate of arity zero is a
constant, a leaf of the circuit like an input. -/
def Program.innerGates (p : Program σ n s) : Finset (Fin s) :=
  Finset.univ.filter fun g : Fin s => σ.Arity (p.lines g).op ≠ 0

/-- The number of inner gates of a circuit: its size, with constant gates free. For arithmetic
circuits this counts additions and multiplications. -/
def Circuit.innerSize {m : ℕ} (c : Circuit σ n m) : ℕ :=
  c.program.innerGates.card

theorem Circuit.innerSize_le_size {m : ℕ} (c : Circuit σ n m) : c.innerSize ≤ c.size :=
  (Finset.card_filter_le _ _).trans (by simp)

end Cslib.Circuits
