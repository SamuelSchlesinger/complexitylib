/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Complexity
public import Complexitylib.Algebraic.Translation.Contextual

/-!
# Comparing standard and native De Morgan gate costs

Constants and identities are free in `standardCost`, while native complexity
counts every internal gate. A contextual translation shares two constant
gates across the whole circuit and removes identities. Its native size is
exactly the original standard cost plus two.
-/

@[expose] public section

namespace Algebraic.DeMorgan

private def contextExpression (op : Op) : Expression (2 + arity op) :=
  match op with
  | .false => .input ⟨0, by decide⟩
  | .true => .input ⟨1, by decide⟩
  | .id => .input ⟨2, by decide⟩
  | .not => .not (.input ⟨2, by decide⟩)
  | .and => .and (.input ⟨2, by decide⟩) (.input ⟨3, by decide⟩)
  | .or => .or (.input ⟨2, by decide⟩) (.input ⟨3, by decide⟩)

private def nativeTranslation : ContextualTranslation signature signature 2 where
  operation op := (contextExpression op).circuit

private def constantContext : Fin 2 → Bool := Fin.cons false (Fin.cons true Fin.elim0)

private theorem nativeTranslation_pull : nativeTranslation.pull interpretation constantContext = interpretation := by
  funext op input
  cases op <;> simp [ContextualTranslation.pull, nativeTranslation, contextExpression,
    Expression.circuit_eval, Expression.eval, ContextualTranslation.appendInputs,
    constantContext, interpretation, Fin.addCases]

private theorem nativeTranslation_pullCost : nativeTranslation.pullCost OperationCost.unit = standardCost := by
  funext op
  cases op <;> simp [ContextualTranslation.pullCost, nativeTranslation, contextExpression]

private def initializeConstants (n : Nat) : Circuit signature n (2 + n) :=
  ((Expression.constant false : Expression n).circuit.parallel
    (Expression.constant true : Expression n).circuit).parallel (Circuit.id signature n)

private theorem initializeConstants_eval (input : Fin n → Bool) :
    (initializeConstants n).eval interpretation input = ContextualTranslation.appendInputs constantContext input := by
  funext output
  refine Fin.addCases ?_ ?_ output
  · intro index
    fin_cases index <;> simp [initializeConstants, Circuit.eval_parallel,
      Expression.circuit_eval, Expression.eval, ContextualTranslation.appendInputs, constantContext,
      Fin.append, Fin.addCases]
  · intro index
    simp [initializeConstants, Circuit.eval_parallel, ContextualTranslation.appendInputs]

private def rawWithSharedConstants (circuit : Circuit signature n m) :
    Circuit signature n m :=
  (nativeTranslation.compile circuit).comp (initializeConstants n)

private theorem rawWithSharedConstants_eval (circuit : Circuit signature n m) (input : Fin n → Bool) :
    (rawWithSharedConstants circuit).eval interpretation input = circuit.eval interpretation input := by
  rw [rawWithSharedConstants, Circuit.eval_comp, initializeConstants_eval,
    ContextualTranslation.compile_eval, nativeTranslation_pull]

private theorem initializeConstants_size : (initializeConstants n).size = 2 := by
  simp [initializeConstants, Expression.gateCount]

private theorem rawWithSharedConstants_size (circuit : Circuit signature n m) :
    (rawWithSharedConstants circuit).size = circuit.cost standardCost + 2 := by
  have size := nativeTranslation.compile_size circuit
  rw [nativeTranslation_pullCost] at size
  rw [rawWithSharedConstants, Circuit.size_comp, size, initializeConstants_size]
  omega

/-- Compile a circuit while sharing two constant gates and eliminating identity gates. -/
@[no_expose] def withSharedConstants (circuit : Circuit signature n m) :
    Circuit signature n m :=
  rawWithSharedConstants circuit

/-- Sharing constants preserves every designated output. -/
theorem withSharedConstants_eval (circuit : Circuit signature n m) (input : Fin n → Bool) :
    (withSharedConstants circuit).eval interpretation input = circuit.eval interpretation input := by
  rw [withSharedConstants]
  exact rawWithSharedConstants_eval circuit input

/-- The translated native size is precisely standard logical-gate cost plus two. -/
theorem withSharedConstants_size (circuit : Circuit signature n m) :
    (withSharedConstants circuit).size = circuit.cost standardCost + 2 := by
  rw [withSharedConstants]
  exact rawWithSharedConstants_size circuit

/-- Any standard-cost circuit yields a native upper bound with only two extra gates. -/
theorem complexity_le_standardCost_add_two (circuit : Circuit signature n 1)
    {function : ScalarFunction Bool n}
    (computes : circuit.ComputesWith interpretation (fun input _ => function input)) :
    complexity function ≤ circuit.cost standardCost + 2 := by
  have bound := complexity_le (withSharedConstants circuit) (by
    intro input
    rw [withSharedConstants_eval]
    exact computes input)
  rwa [withSharedConstants_size] at bound

end Algebraic.DeMorgan
