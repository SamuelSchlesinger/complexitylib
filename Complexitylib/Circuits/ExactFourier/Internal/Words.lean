/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Tactic

/-!
# Exact Fourier circuits: words

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/Words.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
namespace ExactFourier
/-- A permutation matrix times an invertible diagonal matrix, literally P D. -/
def IsMonomial {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin q)) (d : Fin q → ℂ),
    (∀ j, d j ≠ 0) ∧ ∀ i j, A i j = if i = σ j then d j else 0

/-- A call on an ordered tuple of distinct coordinates; all other values are fixed. -/
noncomputable def embeddedCall {q w : ℕ} (A : Matrix (Fin q) (Fin q) ℂ)
    (e : Fin q ↪ Fin w) : Matrix (Fin w) (Fin w) ℂ := by
  classical
  exact fun u v => (∑ i, ∑ j, if e i = u then (if e j = v then A i j else 0) else 0) +
    if u = v ∧ ¬ ∃ i, e i = u then 1 else 0

/-- Only forward calls to the specified A are allowed. -/
inductive WordStep {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (w : ℕ) where
  | monomial (M : Matrix (Fin w) (Fin w) ℂ) (hM : IsMonomial M)
  | call (e : Fin q ↪ Fin w)

/-- The ambient matrix of a monomial step or an embedded call to the fixed matrix. -/
noncomputable def WordStep.matrix {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} :
    WordStep A w → Matrix (Fin w) (Fin w) ℂ
  | .monomial M _ => M
  | .call e => embeddedCall A e

/-- Charge one call for a matrix invocation and zero for a monomial step. -/
def WordStep.calls {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} : WordStep A w → ℕ
  | .monomial _ _ => 0
  | .call _ => 1

/-- Stored chronologically, so a new step left-multiplies earlier steps. -/
noncomputable def wordMatrix {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (W : List (WordStep A w)) : Matrix (Fin w) (Fin w) ℂ :=
  (W.map WordStep.matrix).reverse.prod

/-- The total number of calls to the fixed matrix in the finite-win word. -/
def wordCalls {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (W : List (WordStep A w)) : ℕ := (W.map WordStep.calls).sum

/-- A fixed coordinate relabeling of the ordinary Kronecker tensor power. -/
noncomputable def tensorCoordinates (q b : ℕ) : Fin (q ^ b) ≃ (Fin b → Fin q) := by
  classical
  exact (Equiv.cast (by simp) : Fin (q ^ b) ≃ Fin (Fintype.card (Fin b → Fin q))) |>.trans
    (Fintype.equivFin (Fin b → Fin q)).symm

/-- The ordinary matrix tensor power under the fixed finite-coordinate numbering. -/
noncomputable def tensorPower {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (b : ℕ) :
    Matrix (Fin (q ^ b)) (Fin (q ^ b)) ℂ :=
  fun i j => ∏ k : Fin b, A (tensorCoordinates q b i k) (tensorCoordinates q b j k)

/-- An invertible nonmonomial matrix has a tensor power using fewer calls than the standard
construction. -/
def FiniteWinStatement : Prop :=
  ∃ (q : ℕ) (A : Matrix (Fin q) (Fin q) ℂ), IsUnit A ∧ ¬ IsMonomial A ∧
    ∃ b : ℕ, 2 ≤ b ∧ ∃ W : List (WordStep A (q ^ b)),
      wordMatrix W = tensorPower A b ∧ wordCalls W < b * q ^ (b - 1)

end ExactFourier

end

end Complexity
