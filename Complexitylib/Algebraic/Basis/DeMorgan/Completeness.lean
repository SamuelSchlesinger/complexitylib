/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Expression
public import Complexitylib.Algebraic.Semantics

/-!
# Elementary completeness of the De Morgan basis

Shannon expansion on the first input constructs a formula for every Boolean
function. Compiling that formula gives a circuit, including for zero inputs.
This elementary existence argument is independent of circuit counting,
minimum complexity, and asymptotically efficient synthesis.
-/

@[expose] public section

namespace Algebraic.DeMorgan

/-- A truth-table formula obtained by recursively selecting between the two
restrictions of a Boolean function at its first input. -/
def Expression.ofFunction : {n : Nat} → ScalarFunction Bool n → Expression n
  | 0, function => .constant (function Fin.elim0)
  | n + 1, function =>
      .or
        (.and (.not (.input 0))
          ((ofFunction (n := n) (fun input => function (Fin.cons false input))).mapInputs
            Fin.succ))
        (.and (.input 0)
          ((ofFunction (n := n) (fun input => function (Fin.cons true input))).mapInputs
            Fin.succ))

/-- Truth-table synthesis computes the supplied Boolean function. -/
@[simp] theorem Expression.ofFunction_eval
    (function : ScalarFunction Bool n) (input : Fin n → Bool) :
    (Expression.ofFunction function).eval input = function input := by
  induction n with
  | zero =>
      have equal : (Fin.elim0 : Fin 0 → Bool) = input := Subsingleton.elim _ _
      simp [ofFunction, eval, equal]
  | succ n ih =>
      simp only [ofFunction, eval, mapInputs_eval, ih]
      have reconstruct := Fin.cons_self_tail input
      cases first : input 0 <;>
        simpa +unfoldPartialApp [first, Fin.tail, Function.comp_def] using
          congrArg function reconstruct

/-- Every scalar Boolean function has a De Morgan circuit. -/
theorem exists_circuit (function : ScalarFunction Bool n) :
    ∃ circuit : Circuit signature n 1,
      circuit.ComputesWith interpretation (fun input _ => function input) := by
  refine ⟨(Expression.ofFunction function).circuit, ?_⟩
  intro input
  funext output
  have equal : output = 0 := Fin.eq_zero output
  simp [equal]

/-- The De Morgan interpretation computes every finite-output Boolean target,
including targets with no inputs or no outputs. -/
theorem functionallyComplete :
    Interpretation.FunctionallyComplete (σ := signature) interpretation := by
  intro n m target
  let expressions (output : Fin m) := Expression.ofFunction (fun input => target input output)
  refine ⟨Circuit.parallelFin m (fun output => (expressions output).circuit), ?_⟩
  intro input
  funext output
  simp [expressions]

end Algebraic.DeMorgan
