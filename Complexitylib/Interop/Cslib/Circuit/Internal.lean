/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Cslib.Circuit.Defs
public import Cslib.Computability.Circuit.Boolean.Synthesis
public import Complexitylib.Circuits.AndOrNot

/-!
# Proofs for the CSLib circuit bridge

- `Circuit.eval_ofCslib_internal`: the translation `Circuit.ofCslib` computes what the
  CSLib circuit computes. The proof shows that our wire values satisfy every
  gate equation of the CSLib program, which determines the program's
  evaluation (`Program.eq_eval_of_forall_lines_eval`).
- `Circuit.exists_cslib_internal`: every fan-in-two AND/OR circuit has a CSLib De Morgan
  circuit of size at most `N + 2G + M` computing the same outputs. The proof
  uses CSLib's synthesis calculus: it keeps every wire and its negation
  available, spending `N` gates on negated inputs, two gates per internal gate,
  and one gate per output.
-/


public section

namespace Complexity

open Cslib.Circuits

namespace Circuit

variable {N M G g : ℕ}

/-- The gate simulating a line computes the line's operation. -/
theorem ofCslibGate_eval [NeZero N] (l : Line Boolean.signature N g) (v : BitString (N + g)) :
    (ofCslibGate l).eval v =
      Boolean.interpretation l.op (fun a => v (l.wires a).index) := by
  obtain ⟨op, w⟩ := l
  cases op with
  | const b =>
    cases b <;>
      simp [ofCslibGate, Gate.eval, Basis.andOr2, AndOrOp.eval_two_and, AndOrOp.eval_two_or,
        Boolean.interpretation]
  | not =>
    simp [ofCslibGate, Gate.eval, Basis.andOr2, AndOrOp.eval_two_and, Boolean.interpretation]
  | and =>
    simp [ofCslibGate, Gate.eval, Basis.andOr2, AndOrOp.eval_two_and, Boolean.interpretation]
  | or =>
    simp [ofCslibGate, Gate.eval, Basis.andOr2, AndOrOp.eval_two_or, Boolean.interpretation]

/-- Our wire values in the translation are the CSLib program's wire values. -/
theorem wireValue_ofCslib [NeZero N] [NeZero M]
    (c : Cslib.Circuits.Circuit Boolean.signature N M) (x : BitString N) (w : Wire N c.size) :
    (ofCslib c).wireValue x w.index = c.program.trace Boolean.interpretation x w := by
  set values : Fin c.size → Bool := fun j => (ofCslib c).wireValue x (Fin.natAdd N j)
  have helim : ∀ w, Wire.elim x values w = (ofCslib c).wireValue x w.index := by
    intro w
    cases w with
    | input i =>
      rw [Wire.elim_input, Wire.index_input, wireValue_of_lt _ _ _ (by simp)]
      rfl
    | gate j => rfl
  have heval : values = c.program.eval Boolean.interpretation x := by
    apply Program.eq_eval_of_forall_lines_eval
    intro j
    show _ = (ofCslib c).wireValue x (Fin.natAdd N j)
    rw [wireValue_of_not_lt _ _ _ (by simp)]
    have hj : (⟨(Fin.natAdd N j).val - N, by simp⟩ : Fin c.size) = j := Fin.ext (by simp)
    rw [hj]
    refine Eq.trans ?_ (ofCslibGate_eval _ _).symm
    rw [Line.eval]
    congr 1
    funext a
    exact helim _
  rw [← helim, heval]
  rfl

/-- **The translation computes what the CSLib circuit computes.** -/
theorem eval_ofCslib_internal [NeZero N] [NeZero M]
    (c : Cslib.Circuits.Circuit Boolean.signature N M) (x : BitString N) :
    (ofCslib c).eval x = c.eval Boolean.interpretation x := by
  funext j
  show ((ofCslib c).outputs j).eval ((ofCslib c).wireValue x) =
    c.program.trace Boolean.interpretation x (c.outputs j)
  rw [← wireValue_ofCslib]
  simp [ofCslib, Gate.eval, Basis.andOr2, AndOrOp.eval_two_and]

/-- A fan-in-two AND/OR gate whose two literals are available costs one CSLib
gate. -/
theorem synthesis_gate {W : ℕ} (gt : Gate Basis.andOr2 W) (val : BitString N → BitString W)
    (s : Set (BitString N → Bool))
    (hs : ∀ k, (fun x => (gt.negated k).xor (val x (gt.inputs k))) ∈ s) :
    Synthesis Boolean.interpretation s {fun x => gt.eval (val x)} 1 := by
  obtain ⟨op, fanIn, hfan, inputs, negated⟩ := gt
  change fanIn = 2 at hfan
  subst hfan
  have h0 := Synthesis.of_mem (I := Boolean.interpretation) (hs 0)
  have h1 := Synthesis.of_mem (I := Boolean.interpretation) (hs 1)
  cases op
  · convert Synthesis.and h0 h1 using 2
    funext x
    simp [Gate.eval, Basis.andOr2, AndOrOp.eval_two_and]
  · convert Synthesis.or h0 h1 using 2
    funext x
    simp [Gate.eval, Basis.andOr2, AndOrOp.eval_two_or]

variable [NeZero N] [NeZero M]

/-- Literals `b ⊕ w` of the wires `w` below `bound`. -/
def litSet (c : Circuit Basis.andOr2 N M G) (bound : ℕ) : Set (BitString N → Bool) :=
  {f | ∃ (b : Bool) (w : Fin (N + G)), w.val < bound ∧ f = fun x => b.xor (c.wireValue x w)}

/-- Spending one negation per input makes every input literal available. -/
theorem synthesis_litSet_zero (c : Circuit Basis.andOr2 N M G) :
    Synthesis Boolean.interpretation (inputs N) (c.litSet N) N := by
  have h : ∀ k : Fin N, Synthesis Boolean.interpretation (inputs N)
      ({fun x => x k} ∪ {fun x => !x k}) (0 + 1) := fun k =>
    (Synthesis.of_mem (s := inputs N) (f := fun x => x k) ⟨k, rfl⟩).union
      (Synthesis.not (Synthesis.of_mem (s := inputs N) (f := fun x => x k) ⟨k, rfl⟩))
  refine (Synthesis.iUnion _ _ h).mono Set.Subset.rfl ?_ (by simp)
  rintro f ⟨b, w, hw, rfl⟩
  refine Set.mem_iUnion.mpr ⟨⟨w, hw⟩, ?_⟩
  cases b
  · left
    funext x
    simp [wireValue_of_lt _ _ _ hw]
  · right
    funext x
    simp [wireValue_of_lt _ _ _ hw]

/-- Two more gates make both literals of the next gate wire available. -/
theorem synthesis_litSet_succ (c : Circuit Basis.andOr2 N M G) {i : ℕ} (hi : i < G)
    (h : Synthesis Boolean.interpretation (inputs N) (c.litSet (N + i)) (N + 2 * i)) :
    Synthesis Boolean.interpretation (inputs N) (c.litSet (N + (i + 1))) (N + 2 * (i + 1)) := by
  let w : Fin (N + G) := ⟨N + i, by omega⟩
  have hpos : Synthesis Boolean.interpretation (inputs N ∪ c.litSet (N + i))
      {fun x => c.wireValue x w} 1 := by
    have hval : (fun x => c.wireValue x w) = fun x => (c.gates ⟨i, hi⟩).eval (c.wireValue x) := by
      funext x
      rw [wireValue_of_not_lt _ _ _ (by simp [w])]
      congr 2
      exact Fin.ext (by simp [w])
    rw [hval]
    exact synthesis_gate _ _ _ fun k =>
      Or.inr ⟨_, _, by simpa using c.acyclic ⟨i, hi⟩ k, rfl⟩
  have hboth := hpos.comp (Synthesis.not (Synthesis.of_mem (Set.mem_union_right _ rfl)))
  refine (h.comp hboth).mono Set.Subset.rfl ?_ (by omega)
  rintro f ⟨b, v, hv, rfl⟩
  by_cases hlt : v.val < N + i
  · exact Or.inl ⟨b, v, hlt, rfl⟩
  · have hvw : v = w := Fin.ext (by simp [w]; omega)
    subst hvw
    right
    cases b
    · left
      funext x
      simp
    · right
      funext x
      simp

/-- **Every fan-in-two AND/OR circuit is a CSLib De Morgan circuit** of size at
most `N + 2G + M` computing the same outputs. -/
theorem exists_cslib_internal (c : Circuit Basis.andOr2 N M G) :
    ∃ c' : Cslib.Circuits.Circuit Boolean.signature N M, c'.size ≤ N + 2 * G + M ∧
      ∀ x j, c'.eval Boolean.interpretation x j = c.eval x j := by
  have hG : ∀ i ≤ G,
      Synthesis Boolean.interpretation (inputs N) (c.litSet (N + i)) (N + 2 * i) := by
    intro i
    induction i with
    | zero => exact fun _ => by simpa using c.synthesis_litSet_zero
    | succ i ih => exact fun hi => c.synthesis_litSet_succ (by omega) (ih (by omega))
  have hout := (hG G le_rfl).trans (Synthesis.family (fun j x => c.eval x j) (fun _ => 1)
    fun j => synthesis_gate (c.outputs j) c.wireValue _ fun k =>
      Or.inr ⟨_, _, ((c.outputs j).inputs k).isLt, rfl⟩)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hout
  obtain ⟨c', hc', hsize⟩ := hout.exists_circuit_outputs
  exact ⟨c', hsize, fun x j => congrFun (hc' x) j⟩

end Circuit

end Complexity
