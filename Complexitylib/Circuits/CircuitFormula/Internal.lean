/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.CircuitFormula.Defs

/-!
# Unfolding fan-in-two circuit outputs into Boolean formulas -- proof internals
-/

@[expose] public section

namespace Complexity

namespace BoolFormula

theorem eval_negateIf_internal (assignment : ℕ → Bool)
    (negated : Bool) (formula : BoolFormula) :
    eval assignment (negateIf negated formula) =
      negated.xor (eval assignment formula) := by
  cases negated <;> simp [negateIf, eval]

theorem depth_negateIf_le_internal (negated : Bool)
    (formula : BoolFormula) :
    (negateIf negated formula).depth ≤ formula.depth + 1 := by
  cases negated <;> simp [negateIf, depth]

theorem depth_andOr_negateIf_le_internal (op : AndOrOp)
    (negated₀ negated₁ : Bool) (formula₀ formula₁ : BoolFormula) :
    (match op with
      | .and => BoolFormula.conj (negateIf negated₀ formula₀)
          (negateIf negated₁ formula₁)
      | .or => BoolFormula.disj (negateIf negated₀ formula₀)
          (negateIf negated₁ formula₁)).depth ≤
      2 + max formula₀.depth formula₁.depth := by
  have h₀ := depth_negateIf_le_internal negated₀ formula₀
  have h₁ := depth_negateIf_le_internal negated₁ formula₁
  have hmax := max_le
    (le_trans h₀ (Nat.add_le_add_right (le_max_left _ _) 1))
    (le_trans h₁ (Nat.add_le_add_right (le_max_right _ _) 1))
  cases op <;> change max _ _ + 1 ≤ _
  all_goals
    omega

theorem vars_negateIf_internal
    (negated : Bool) (formula : BoolFormula) :
    (negateIf negated formula).vars = formula.vars := by
  cases negated <;> simp [negateIf, vars]

end BoolFormula

namespace Gate

theorem eval_toBoolFormula_internal {W : ℕ}
    (gate : Gate Basis.andOr2 W) (wireFormula : Fin W → BoolFormula)
    (assignment : ℕ → Bool) :
    BoolFormula.eval assignment (gate.toBoolFormula wireFormula) =
      gate.eval fun wire => BoolFormula.eval assignment (wireFormula wire) := by
  obtain ⟨op, fanIn, arityOk, inputs, negated⟩ := gate
  change fanIn = 2 at arityOk
  subst arityOk
  cases op <;>
    simp [Gate.toBoolFormula, Gate.eval, Basis.andOr2, AndOrOp.eval,
      BoolFormula.eval, BoolFormula.eval_negateIf_internal,
      Fin.foldl_succ_last, Fin.foldl_zero]

theorem depth_toBoolFormula_le_internal {W : ℕ}
    (gate : Gate Basis.andOr2 W) (wireFormula : Fin W → BoolFormula) :
    let input₀ : Fin gate.fanIn :=
      ⟨0, by rw [fanIn_andOr2 gate]; omega⟩
    let input₁ : Fin gate.fanIn :=
      ⟨1, by rw [fanIn_andOr2 gate]; omega⟩
    (gate.toBoolFormula wireFormula).depth ≤
      2 + max (wireFormula (gate.inputs input₀)).depth
        (wireFormula (gate.inputs input₁)).depth := by
  dsimp only
  unfold Gate.toBoolFormula
  dsimp only
  exact BoolFormula.depth_andOr_negateIf_le_internal gate.op
    (gate.negated ⟨0, by rw [fanIn_andOr2 gate]; omega⟩)
    (gate.negated ⟨1, by rw [fanIn_andOr2 gate]; omega⟩)
    (wireFormula (gate.inputs ⟨0, by rw [fanIn_andOr2 gate]; omega⟩))
    (wireFormula (gate.inputs ⟨1, by rw [fanIn_andOr2 gate]; omega⟩))

theorem vars_toBoolFormula_lt_internal {W N : ℕ}
    (gate : Gate Basis.andOr2 W) (wireFormula : Fin W → BoolFormula)
    (hvars : ∀ input : Fin gate.fanIn, ∀ index,
      index ∈ (wireFormula (gate.inputs input)).vars → index < N) :
    ∀ index ∈ (gate.toBoolFormula wireFormula).vars, index < N := by
  unfold Gate.toBoolFormula
  dsimp only
  cases gate.op <;>
    simp only [BoolFormula.vars, Finset.mem_union,
      BoolFormula.vars_negateIf_internal]
  all_goals
    intro index hindex
    rcases hindex with hleft | hright
    · exact hvars _ index hleft
    · exact hvars _ index hright

end Gate

namespace Circuit

variable {N M G : ℕ} [NeZero N] [NeZero M]

theorem wireFormula_of_lt_internal
    (circuit : Circuit Basis.andOr2 N M G) (wire : Fin (N + G))
    (hinput : wire.val < N) :
    circuit.wireFormula wire = .var wire.val := by
  conv_lhs => unfold wireFormula
  simp only [hinput, dite_true]

theorem wireFormula_of_not_lt_internal
    (circuit : Circuit Basis.andOr2 N M G) (wire : Fin (N + G))
    (hinput : ¬ wire.val < N) :
    circuit.wireFormula wire =
      (circuit.gates ⟨wire.val - N, by omega⟩).toBoolFormula
        fun source => circuit.wireFormula source := by
  conv_lhs => unfold wireFormula
  simp only [hinput, dite_false]
  rfl

/-- Auxiliary: for a fan-in-two gate `g`, the `Fin.foldl` over its inputs
collapses to the `max` of the two input wire depths. Stated with `g`
universally quantified so the structure `obtain` avoids the fragile
`generalize` over a gate that appears in dependent index proofs. -/
private theorem foldl_fanIn_two_max
    (circuit : Circuit Basis.andOr2 N M G) (g : Gate Basis.andOr2 (N + G)) :
    Fin.foldl g.fanIn (fun acc k => max acc (circuit.wireDepth (g.inputs k))) 0 =
      max (circuit.wireDepth (g.inputs ⟨0, by rw [fanIn_andOr2 g]; omega⟩))
        (circuit.wireDepth (g.inputs ⟨1, by rw [fanIn_andOr2 g]; omega⟩)) := by
  obtain ⟨op, fanIn, arityOk, inputs, negated⟩ := g
  change fanIn = 2 at arityOk
  subst arityOk
  simp [Fin.foldl_succ_last, Fin.foldl_zero]

theorem wireDepth_of_not_lt_two_internal
    (circuit : Circuit Basis.andOr2 N M G) (wire : Fin (N + G))
    (hinput : ¬ wire.val < N) :
    let gate := circuit.gates ⟨wire.val - N, by omega⟩
    let input₀ : Fin gate.fanIn :=
      ⟨0, by rw [fanIn_andOr2 gate]; omega⟩
    let input₁ : Fin gate.fanIn :=
      ⟨1, by rw [fanIn_andOr2 gate]; omega⟩
    circuit.wireDepth wire =
      1 + max (circuit.wireDepth (gate.inputs input₀))
        (circuit.wireDepth (gate.inputs input₁)) := by
  rw [Circuit.wireDepth_of_not_lt circuit wire hinput]
  dsimp only
  exact congrArg (1 + ·) (foldl_fanIn_two_max circuit (circuit.gates ⟨wire.val - N, by omega⟩))

theorem outputDepth_two_internal
    (circuit : Circuit Basis.andOr2 N M G) (output : Fin M) :
    let gate := circuit.outputs output
    let input₀ : Fin gate.fanIn :=
      ⟨0, by rw [fanIn_andOr2 gate]; omega⟩
    let input₁ : Fin gate.fanIn :=
      ⟨1, by rw [fanIn_andOr2 gate]; omega⟩
    circuit.outputDepth output =
      1 + max (circuit.wireDepth (gate.inputs input₀))
        (circuit.wireDepth (gate.inputs input₁)) := by
  unfold Circuit.outputDepth
  dsimp only
  exact congrArg (1 + ·) (foldl_fanIn_two_max circuit (circuit.outputs output))

theorem eval_wireFormula_internal
    (circuit : Circuit Basis.andOr2 N M G) (assignment : ℕ → Bool)
    (wire : Fin (N + G)) :
    BoolFormula.eval assignment (circuit.wireFormula wire) =
      circuit.wireValue (fun input => assignment input.val) wire := by
  induction hwire : wire.val using Nat.strong_induction_on generalizing wire with
  | h index ih =>
      by_cases hinput : wire.val < N
      · rw [wireFormula_of_lt_internal circuit wire hinput,
          Circuit.wireValue_of_lt circuit _ wire hinput]
        rfl
      · rw [wireFormula_of_not_lt_internal circuit wire hinput,
          Circuit.wireValue_of_not_lt circuit _ wire hinput,
          Gate.eval_toBoolFormula_internal]
        unfold Gate.eval
        congr 1
        funext input
        apply congrArg (fun value =>
          Bool.xor ((circuit.gates ⟨wire.val - N, by omega⟩).negated input) value)
        apply ih ((circuit.gates ⟨wire.val - N, by omega⟩).inputs input).val
        · have hacyclic :=
            circuit.acyclic ⟨wire.val - N, by omega⟩ input
          change ((circuit.gates ⟨wire.val - N, by omega⟩).inputs input).val <
            N + (wire.val - N) at hacyclic
          omega
        · rfl

theorem eval_outputFormula_internal
    (circuit : Circuit Basis.andOr2 N M G) (assignment : ℕ → Bool)
    (output : Fin M) :
    BoolFormula.eval assignment (circuit.outputFormula output) =
      circuit.eval (fun input => assignment input.val) output := by
  rw [outputFormula, Gate.eval_toBoolFormula_internal]
  unfold Circuit.eval Gate.eval
  congr 1
  funext input
  exact congrArg (fun value => Bool.xor ((circuit.outputs output).negated input) value)
    (eval_wireFormula_internal circuit assignment ((circuit.outputs output).inputs input))

theorem vars_wireFormula_lt_internal
    (circuit : Circuit Basis.andOr2 N M G) (wire : Fin (N + G)) :
    ∀ index ∈ (circuit.wireFormula wire).vars, index < N := by
  induction hwire : wire.val using Nat.strong_induction_on
      generalizing wire with
  | h wireIndex ih =>
      by_cases hinput : wire.val < N
      · rw [wireFormula_of_lt_internal circuit wire hinput]
        simp only [BoolFormula.vars, Finset.mem_singleton]
        intro index hindex
        simpa only [hindex] using hinput
      · rw [wireFormula_of_not_lt_internal circuit wire hinput]
        apply Gate.vars_toBoolFormula_lt_internal
        intro input index hindex
        apply ih
          ((circuit.gates ⟨wire.val - N, by omega⟩).inputs input).val
        · have hacyclic :=
            circuit.acyclic ⟨wire.val - N, by omega⟩ input
          change
            ((circuit.gates ⟨wire.val - N, by omega⟩).inputs input).val <
              N + (wire.val - N) at hacyclic
          omega
        · rfl
        · exact hindex

theorem vars_outputFormula_lt_internal
    (circuit : Circuit Basis.andOr2 N M G) (output : Fin M) :
    ∀ index ∈ (circuit.outputFormula output).vars, index < N := by
  rw [Circuit.outputFormula]
  apply Gate.vars_toBoolFormula_lt_internal
  intro input index hindex
  exact vars_wireFormula_lt_internal circuit _ index hindex

theorem depth_wireFormula_le_internal
    (circuit : Circuit Basis.andOr2 N M G) (wire : Fin (N + G)) :
    (circuit.wireFormula wire).depth ≤ 2 * circuit.wireDepth wire := by
  induction hwire : wire.val using Nat.strong_induction_on generalizing wire with
  | h index ih =>
      by_cases hinput : wire.val < N
      · rw [wireFormula_of_lt_internal circuit wire hinput,
          Circuit.wireDepth_of_lt circuit wire hinput]
        rfl
      · have hgate : wire.val - N < G := by omega
        let gate := circuit.gates ⟨wire.val - N, hgate⟩
        let input₀ : Fin gate.fanIn :=
          ⟨0, by rw [fanIn_andOr2 gate]; omega⟩
        let input₁ : Fin gate.fanIn :=
          ⟨1, by rw [fanIn_andOr2 gate]; omega⟩
        have hacyclic₀ : (gate.inputs input₀).val < wire.val := by
          have h := circuit.acyclic ⟨wire.val - N, hgate⟩ input₀
          change (gate.inputs input₀).val < N + (wire.val - N) at h
          omega
        have hacyclic₁ : (gate.inputs input₁).val < wire.val := by
          have h := circuit.acyclic ⟨wire.val - N, hgate⟩ input₁
          change (gate.inputs input₁).val < N + (wire.val - N) at h
          omega
        have ih₀ := ih (gate.inputs input₀).val (by omega)
          (gate.inputs input₀) rfl
        have ih₁ := ih (gate.inputs input₁).val (by omega)
          (gate.inputs input₁) rfl
        have hformula := Gate.depth_toBoolFormula_le_internal gate
          fun source => circuit.wireFormula source
        dsimp only at hformula
        change (gate.toBoolFormula fun source => circuit.wireFormula source).depth ≤
          2 + max (circuit.wireFormula (gate.inputs input₀)).depth
            (circuit.wireFormula (gate.inputs input₁)).depth at hformula
        have hmax :
            max (circuit.wireFormula (gate.inputs input₀)).depth
                (circuit.wireFormula (gate.inputs input₁)).depth ≤
              2 * max (circuit.wireDepth (gate.inputs input₀))
                (circuit.wireDepth (gate.inputs input₁)) :=
          max_le
            (le_trans ih₀ (Nat.mul_le_mul_left 2 (le_max_left _ _)))
            (le_trans ih₁ (Nat.mul_le_mul_left 2 (le_max_right _ _)))
        rw [wireFormula_of_not_lt_internal circuit wire hinput,
          wireDepth_of_not_lt_two_internal circuit wire hinput]
        change (gate.toBoolFormula fun source => circuit.wireFormula source).depth ≤
          2 * (1 + max (circuit.wireDepth (gate.inputs input₀))
            (circuit.wireDepth (gate.inputs input₁)))
        omega

theorem depth_outputFormula_le_outputDepth_internal
    (circuit : Circuit Basis.andOr2 N M G) (output : Fin M) :
    (circuit.outputFormula output).depth ≤
      2 * circuit.outputDepth output := by
  let gate := circuit.outputs output
  let input₀ : Fin gate.fanIn :=
    ⟨0, by rw [fanIn_andOr2 gate]; omega⟩
  let input₁ : Fin gate.fanIn :=
    ⟨1, by rw [fanIn_andOr2 gate]; omega⟩
  have hformula := Gate.depth_toBoolFormula_le_internal gate
    fun source => circuit.wireFormula source
  dsimp only at hformula
  change (gate.toBoolFormula fun source => circuit.wireFormula source).depth ≤
    2 + max (circuit.wireFormula (gate.inputs input₀)).depth
      (circuit.wireFormula (gate.inputs input₁)).depth at hformula
  have h₀ := depth_wireFormula_le_internal circuit (gate.inputs input₀)
  have h₁ := depth_wireFormula_le_internal circuit (gate.inputs input₁)
  have hmax :
      max (circuit.wireFormula (gate.inputs input₀)).depth
          (circuit.wireFormula (gate.inputs input₁)).depth ≤
        2 * max (circuit.wireDepth (gate.inputs input₀))
          (circuit.wireDepth (gate.inputs input₁)) :=
    max_le
      (le_trans h₀ (Nat.mul_le_mul_left 2 (le_max_left _ _)))
      (le_trans h₁ (Nat.mul_le_mul_left 2 (le_max_right _ _)))
  rw [outputFormula, outputDepth_two_internal circuit output]
  change (gate.toBoolFormula fun source => circuit.wireFormula source).depth ≤
    2 * (1 + max (circuit.wireDepth (gate.inputs input₀))
      (circuit.wireDepth (gate.inputs input₁)))
  omega

end Circuit

end Complexity
