/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AndOrNot.Defs
public import Complexitylib.Circuits.Internal.CircuitDescriptor

/-! # Internal: Typed Circuits as Circuit Descriptors

This internal module connects the typed `Circuit` model over `Basis.andOr2`
to the fixed-size `CircDesc` counting model. It contains only the encoding,
its orderedness proof, and its semantic-correctness proof, so clients that need
this bridge do not also acquire the lower-bound and padding machinery from
`Internal.Bridge`.
-/


@[expose] public section

namespace Complexity

open CircDesc

/-! ## Encoding -/

/-- Encode a `Basis.andOr2` gate as a `GateSlot`. -/
def encodeGate {W W' : Nat} (g : Gate Basis.andOr2 W) (hW : W ≤ W') : GateSlot W' :=
  have h2 := fanIn_andOr2 g
  (match g.op with | .and => true | .or => false,
   (⟨(g.inputs ⟨0, by omega⟩).val, by omega⟩,
    ⟨(g.inputs ⟨1, by omega⟩).val, by omega⟩),
   (g.negated ⟨0, by omega⟩, g.negated ⟨1, by omega⟩))

/-- Encode a circuit over `Basis.andOr2` as a circuit descriptor.
    Internal gates map to positions `0..G-1`; the output gate to position `G`. -/
def circuitToDesc {N G : Nat} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) : CircDesc N (G + 1) := fun i =>
  if h : i.val < G then
    encodeGate (c.gates ⟨i.val, h⟩) (by omega : N + G ≤ N + (G + 1))
  else
    encodeGate (c.outputs 0) (by omega : N + G ≤ N + (G + 1))

/-- Descriptors obtained from typed circuits only refer to primary inputs or
    strictly earlier gates. -/
theorem circuitToDesc_ordered {N G : Nat} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) : CircDesc.Ordered (circuitToDesc c) := by
  intro i
  simp only [circuitToDesc]
  split_ifs with hi
  · have h2 := fanIn_andOr2 (c.gates ⟨i.val, hi⟩)
    simp only [encodeGate, Fin.val_mk]
    constructor
    · exact c.acyclic ⟨i.val, hi⟩ ⟨0, by omega⟩
    · exact c.acyclic ⟨i.val, hi⟩ ⟨1, by omega⟩
  · have h2 := fanIn_andOr2 (c.outputs 0)
    simp only [encodeGate, Fin.val_mk]
    constructor <;> omega

/-! ## Semantic Equivalence -/

/-- Gate evaluation over `Basis.andOr2` matches the `GateSlot` encoding semantics. -/
private theorem gate_eval_eq_slot {W W' : Nat} (g : Gate Basis.andOr2 W) (hW : W ≤ W')
    (wireVal : Fin W → Bool) (wireVal' : Fin W' → Bool)
    (hwv : ∀ w : Fin W, wireVal w = wireVal' ⟨w.val, by omega⟩) :
    g.eval wireVal =
      let (isAnd, (w1, w2), (n1, n2)) := encodeGate g hW
      if isAnd then
        (n1.xor (wireVal' w1)) && (n2.xor (wireVal' w2))
      else
        (n1.xor (wireVal' w1)) || (n2.xor (wireVal' w2)) := by
  obtain ⟨op, fanIn, arityOk, inputs, negated⟩ := g
  change fanIn = 2 at arityOk
  subst arityOk
  cases op <;> simp [Gate.eval, Basis.andOr2, encodeGate, AndOrOp.eval,
    Fin.foldl_succ_last, Fin.foldl_zero, hwv]

/-- Wire values agree between `Circuit.wireValue` and `wireVal` for wires
    in the range `0..N+G-1`. -/
theorem wireValue_eq_wireVal {N G : Nat} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G)
    (input : BitString N) (w : Fin (N + G)) :
    c.wireValue input w =
      wireVal (circuitToDesc c) input ⟨w.val, by omega⟩ := by
  by_cases hwN : w.val < N
  · -- Primary input wire
    rw [Circuit.wireValue_of_lt _ _ _ hwN]
    conv_rhs => unfold wireVal
    simp [hwN]
  · -- Gate wire
    push Not at hwN
    have hG : w.val - N < G := by omega
    rw [Circuit.wireValue_of_not_lt c input w (by omega)]
    -- h2 first, so omega can resolve Fin bounds
    have h2 : (c.gates ⟨w.val - N, hG⟩).fanIn = 2 := fanIn_andOr2 _
    -- Acyclicity (before set, so set rewrites them consistently)
    have hacyc0 : ((c.gates ⟨w.val - N, hG⟩).inputs ⟨0, by omega⟩).val < w.val := by
      have h := c.acyclic ⟨w.val - N, hG⟩ ⟨0, by omega⟩
      simp only [] at h; omega
    have hacyc1 : ((c.gates ⟨w.val - N, hG⟩).inputs ⟨1, by omega⟩).val < w.val := by
      have h := c.acyclic ⟨w.val - N, hG⟩ ⟨1, by omega⟩
      simp only [] at h; omega
    -- set gate — rewrites h2, hacyc0, hacyc1 and the goal
    set gate := c.gates ⟨w.val - N, hG⟩ with gate_def
    -- IH for the two input wires
    have ih0 := wireValue_eq_wireVal c input
      ⟨(gate.inputs ⟨0, by omega⟩).val, by omega⟩
    have ih1 := wireValue_eq_wireVal c input
      ⟨(gate.inputs ⟨1, by omega⟩).val, by omega⟩
    -- Unfold wireVal one step
    conv_rhs => unfold wireVal
    simp only [show ¬((⟨w.val, (by omega : w.val < N + (G + 1))⟩ : Fin (N + (G + 1))).val < N)
      from by simp; omega, dite_false]
    -- circuitToDesc lookup
    simp only [circuitToDesc, show (⟨w.val - N, (by omega : w.val - N < G + 1)⟩ :
      Fin (G + 1)).val < G from hG, dite_true, encodeGate, Fin.val_mk]
    -- Normalize all c.gates ⟨↑w-N, _⟩ to gate (for any proof, via Fin.ext)
    have hgate : ∀ h : w.val - N < G, c.gates ⟨w.val - N, h⟩ = gate :=
      fun h => (congrArg c.gates (Fin.ext rfl)).trans gate_def.symm
    simp_rw [hgate]
    -- Guards pass by acyclicity
    simp only [hacyc0, hacyc1, ↓reduceIte]
    -- Rewrite wireVal back to wireValue using IH
    rw [← ih0, ← ih1]
    -- The RHS has (c.gates ⟨↑w-N,⋯⟩).negated with an opaque Fin proof.
    -- Prove .negated equality using a helper that transports across the gate equality.
    suffices h : ∀ (h' : ↑w - N < G) (j : Fin (c.gates ⟨↑w - N, h'⟩).fanIn),
        (c.gates ⟨↑w - N, h'⟩).negated j =
          gate.negated (j.cast (show (c.gates ⟨↑w - N, h'⟩).fanIn = gate.fanIn by
            rw [hgate h'])) by
      -- First apply h to rewrite all .negated terms to gate.negated (Fin.cast ...)
      simp only [h, Fin.cast_mk]
      -- The LHS is gate.eval and the RHS is the 2-input expansion.
      -- Use gate_eval_eq_slot which produces encodeGate terms,
      -- then show encodeGate gate matches the RHS
      have := gate_eval_eq_slot gate (show N + G ≤ N + G by omega)
        (c.wireValue input) (c.wireValue input) (fun _ => rfl)
      rw [this]; clear this
      -- Now both sides use encodeGate gate; unfold and simplify
      simp [encodeGate]
      rfl
    intro h' j
    exact (show ∀ (g : Gate Basis.andOr2 (N + G)) (heq : g = c.gates ⟨↑w - N, h'⟩)
        (hfanIn : (c.gates ⟨↑w - N, h'⟩).fanIn = g.fanIn)
        (j : Fin (c.gates ⟨↑w - N, h'⟩).fanIn),
        (c.gates ⟨↑w - N, h'⟩).negated j = g.negated (j.cast hfanIn)
      from fun g heq _ j => by subst heq; rfl)
      _ (hgate h').symm (by simp [hgate h']) j
  termination_by w.val

/-- Circuit evaluation agrees with descriptor evaluation. -/
theorem circuit_eval_eq_eval {N G : Nat} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) :
    (fun x => (c.eval x) 0) = eval (Nat.succ_pos G) (circuitToDesc c) := by
  funext x
  simp only [Circuit.eval, eval]
  rw [gate_eval_eq_slot (c.outputs 0) (by omega : N + G ≤ N + (G + 1))
    (c.wireValue x) _ (fun w => wireValue_eq_wireVal c x w)]
  conv_rhs => unfold wireVal
  simp only []
  simp only [circuitToDesc, show ¬((⟨N + G.succ - 1 - N, (by omega : N + G.succ - 1 - N < G + 1)⟩ :
    Fin (G + 1)).val < G) from by simp, dite_false]
  have h2 := fanIn_andOr2 (c.outputs 0)
  simp only [encodeGate, Fin.val_mk,
    show ((c.outputs 0).inputs ⟨0, by omega⟩).val < N + G.succ - 1 from by
      exact Nat.lt_of_lt_of_le ((c.outputs 0).inputs ⟨0, by omega⟩).isLt (by omega),
    show ((c.outputs 0).inputs ⟨1, by omega⟩).val < N + G.succ - 1 from by
      exact Nat.lt_of_lt_of_le ((c.outputs 0).inputs ⟨1, by omega⟩).isLt (by omega),
    ite_true]
  simp only [show ¬(N + G.succ - 1 < N) from by omega, dite_false]
  rfl

end Complexity
