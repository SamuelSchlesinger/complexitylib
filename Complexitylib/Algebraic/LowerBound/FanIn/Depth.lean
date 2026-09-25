/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Fin
public import Complexitylib.Algebraic.Support
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Depth lower bounds from bounded fan-in

At depth `d`, a fan-in-`r` output can depend on at most `r ^ d` inputs.
Essential inputs therefore give a lower bound on circuit depth.
-/

@[expose] public section

namespace Algebraic

private theorem _root_.Cslib.Circuits.Line.card_inputSupport_le_depth
    (line : Line σ n g)
    (wireSupport : Wire n g → Finset (Fin n))
    (wireDepths : Wire n g → Nat)
    (r : Nat)
    (arity : σ.Arity line.op ≤ r)
    (wireBound : ∀ wire,
      (wireSupport wire).card ≤ (max 1 r) ^ wireDepths wire) :
    (line.inputSupport wireSupport).card ≤
      (max 1 r) ^ line.depth wireDepths := by
  have positive : 1 ≤ max 1 r := Nat.le_max_left 1 r
  let maxDepth := Fin.foldl (σ.Arity line.op)
    (fun result argument => max result (wireDepths (line.wires argument))) 0
  have argumentBound (argument : Fin (σ.Arity line.op)) :
      (wireSupport (line.wires argument)).card ≤
        (max 1 r) ^ maxDepth :=
    (wireBound (line.wires argument)).trans <|
      Nat.pow_le_pow_right positive <|
        Fin.le_foldl_max
          (fun argument => wireDepths (line.wires argument)) 0 argument
  calc
    (line.inputSupport wireSupport).card ≤
        σ.Arity line.op * (max 1 r) ^ maxDepth := by
      simpa [Line.inputSupport] using
        Finset.card_biUnion_le_card_mul
          (Finset.univ : Finset (Fin (σ.Arity line.op)))
          (fun argument => wireSupport (line.wires argument))
          ((max 1 r) ^ maxDepth) (fun argument _ => argumentBound argument)
    _ ≤ (max 1 r) * (max 1 r) ^ maxDepth :=
      Nat.mul_le_mul_right ((max 1 r) ^ maxDepth)
        (arity.trans (Nat.le_max_right 1 r))
    _ = (max 1 r) ^ line.depth wireDepths := by
      simp [Line.depth, maxDepth, Nat.pow_succ, Nat.mul_comm]

private theorem _root_.Cslib.Circuits.Program.card_gateSupport_le_depth
    (program : Program σ n g)
    (r : Nat)
    (bounded : program.FanInAtMost r)
    (k : Fin g) :
    (program.gateSupport k).card ≤
      (max 1 r) ^ program.depths k := by
  induction program with
  | empty => exact Fin.elim0 k
  | @gate g program line ih =>
      obtain ⟨programBounded, lineBounded⟩ := bounded
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simp only [Program.gateSupport, Program.depths, Fin.lastCases_last]
        let wireSupport : Wire n g → Finset (Fin n) :=
          Wire.elim (fun k => {k}) program.gateSupport
        let wireDepths : Wire n g → Nat :=
          Wire.elim (fun _ => 0) program.depths
        apply line.card_inputSupport_le_depth wireSupport wireDepths r lineBounded
        intro wire
        cases wire with
        | input i => simp [wireSupport, wireDepths]
        | gate j => simpa [wireSupport, wireDepths] using ih programBounded j
      · simp only [Program.gateSupport, Program.depths, Fin.lastCases_castSucc]
        exact ih programBounded j

private theorem _root_.Cslib.Circuits.Circuit.card_inputSupport_le_depth_aux
    (c : Circuit σ n m)
    (r : Nat)
    (bounded : c.FanInAtMost r) :
    c.inputSupport.card ≤ m * (max 1 r) ^ c.depth := by
  have positive : 1 ≤ max 1 r := Nat.le_max_left 1 r
  have outputBound (output : Fin m) :
      (c.outputSupport output).card ≤
        (max 1 r) ^ c.outputDepths output := by
    let wire := c.outputs output
    change (c.program.wireSupport wire).card ≤
      (max 1 r) ^ c.program.wireDepths wire
    cases wire with
    | input i => simp [Program.wireSupport, Program.wireDepths]
    | gate j =>
      simpa [Program.wireSupport, Program.wireDepths] using
        c.program.card_gateSupport_le_depth r bounded j
  have supportBound := Finset.card_biUnion_le_card_mul
    (Finset.univ : Finset (Fin m)) c.outputSupport ((max 1 r) ^ c.depth)
    (fun output _ => (outputBound output).trans <|
      Nat.pow_le_pow_right positive
        (Fin.le_foldl_max c.outputDepths 0 output))
  simpa [Circuit.inputSupport] using supportBound

/-- A fan-in-`r` circuit has at most `m * (max 1 r) ^ c.depth` supporting
inputs. The maximum accounts for direct output wires when `r = 0`. -/
theorem _root_.Cslib.Circuits.Circuit.card_inputSupport_le_depth
    (c : Circuit σ n m)
    {r : Nat}
    (bounded : c.FanInAtMost r) :
    c.inputSupport.card ≤ m * (max 1 r) ^ c.depth := by
  exact c.card_inputSupport_le_depth_aux r bounded

export Cslib.Circuits (Circuit.card_inputSupport_le_depth)

/-- If a circuit has fan-in at most `r`, computes `target`, and every input in
`selected` is essential to `target`, then `selected` has at most
`m * (max 1 r) ^ c.depth` elements. -/
theorem _root_.Cslib.Circuits.Circuit.essential_le_depth
    (c : Circuit σ n m)
    {interpretation : Interpretation σ U}
    {target : (Fin n → U) → Fin m → U}
    {selected : Finset (Fin n)}
    {r : Nat}
    (computes : c.ComputesWith interpretation target)
    (essential : ∀ k ∈ selected, EssentialAt target k)
    (bounded : c.FanInAtMost r) :
    selected.card ≤ m * (max 1 r) ^ c.depth := by
  have targetDepends := computes.dependsOnlyOn
  exact (Finset.card_le_card fun k hk =>
    (essential k hk).mem_support targetDepends).trans
      (c.card_inputSupport_le_depth bounded)

export Cslib.Circuits (Circuit.essential_le_depth)

end Algebraic
