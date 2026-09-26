/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.Semantics

/-!
# Boolean relation environments and FO-matrix evaluation

Existential SO witnesses supply relation tables. `DecREnv` presents those tables
as Boolean functions, while `toREnv` gives their propositional meaning. A matrix
evaluator reads both the vocabulary relations and these supplied relations;
first-order quantifiers enumerate the finite universe.

The evaluator requires an `IsFOMatrix` certificate, so its interface excludes
second-order quantifiers. This is the verification step in Immerman's
*Descriptive Complexity*, Section 7.1, Proposition 7.6. `SecondOrder.Certificate`
supplies the binary certificate format; `SecondOrder.PolynomialTime` proves
polynomial-time checking against the machine definitions.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

/-- Boolean truth tables for the relation variables in a fixed arity context. -/
def DecREnv (card : Nat) (rctx : List Nat) : Type :=
  (r : Fin rctx.length) → (Fin (rctx.get r) → Fin card) → Bool

namespace DecREnv

/-- Interpret the supplied Boolean tables as propositional relations. -/
def toREnv {card : Nat} {rctx : List Nat} (ρ : DecREnv card rctx) : REnv card rctx :=
  fun r args => ρ r args = true

/-- The unique Boolean relation environment for an empty context. -/
def empty (card : Nat) : DecREnv card [] := fun r => Fin.elim0 r

/-- Supply a fresh Boolean relation at de Bruijn index zero. -/
def cons {card k : Nat} {rctx : List Nat}
    (S : (Fin k → Fin card) → Bool) (ρ : DecREnv card rctx) : DecREnv card (k :: rctx) :=
  fun r => match r with
    | ⟨0, _⟩ => S
    | ⟨i + 1, h⟩ => ρ ⟨i, by simpa using h⟩

end DecREnv

/-- Evaluate an FO matrix with supplied Boolean relation tables and element values. -/
def SOFormula.evalMatrixB {V : Vocabulary} (A : DecFinStruct V) :
    {rctx : List Nat} → {n : Nat} → (φ : SOFormula V rctx n) →
      φ.IsFOMatrix → Env A.card n → DecREnv A.card rctx → Bool
  | _, _, .relApp i args, _, σ, _ => A.rel i (fun j => (args j).eval A.toFinStruct σ)
  | _, _, .soRelApp r args, _, σ, ρ => ρ r (fun j => (args j).eval A.toFinStruct σ)
  | _, _, .eq a b, _, σ, _ => decide (a.eval A.toFinStruct σ = b.eval A.toFinStruct σ)
  | _, _, .neg φ, h, σ, ρ => !(φ.evalMatrixB A h σ ρ)
  | _, _, .conj φ ψ, h, σ, ρ => φ.evalMatrixB A h.1 σ ρ && ψ.evalMatrixB A h.2 σ ρ
  | _, _, .disj φ ψ, h, σ, ρ => φ.evalMatrixB A h.1 σ ρ || ψ.evalMatrixB A h.2 σ ρ
  | _, _, .exist φ, h, σ, ρ =>
    (List.finRange A.card).any (fun a => φ.evalMatrixB A h (envCons a σ) ρ)
  | _, _, .all φ, h, σ, ρ =>
    (List.finRange A.card).all (fun a => φ.evalMatrixB A h (envCons a σ) ρ)
  | _, _, .soExist _ _, h, _, _ => h.elim
  | _, _, .soAll _ _, h, _, _ => h.elim

end Complexity.DescriptiveComplexity
