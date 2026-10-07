/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Exact Fourier circuits: core

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/Core.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
namespace ExactFourier

/-- One charged scalar gate, referencing only available values. -/
inductive Gate (w : ℕ) where
  /-- One charged addition. -/
  | add (i j : Fin w)
  /-- One charged subtraction. -/
  | sub (i j : Fin w)
  /-- One charged multiplication by an arbitrary complex scalar. -/
  | scale (c : ℂ) (i : Fin w)

/-- Evaluate a scalar gate on the currently available values. -/
def Gate.eval {w : ℕ} (v : Fin w → ℂ) : Gate w → ℂ
  | .add i j => v i + v j
  | .sub i j => v i - v j
  | .scale c i => c * v i

/-- A topologically ordered scalar DAG; available values are never consumed. -/
inductive Program (n : ℕ) : ℕ → Type where
  /-- Initial inputs and a free zero wire. -/
  | nil : Program n 0
  /-- Append one operation whose operands are already available. -/
  | step {k : ℕ} (p : Program n k) (g : Gate (n + 1 + k)) : Program n (k + 1)

/-- All available values, with inputs first, then zero, then computed gate values. -/
def Program.eval {n : ℕ} : {k : ℕ} → Program n k → (Fin n → ℂ) →
    (Fin (n + 1 + k) → ℂ)
  | 0, .nil, x => Fin.snoc x 0
  | _ + 1, .step p g, x =>
      let v := p.eval x
      Fin.snoc v (g.eval v)

/-- Outputs name available values, so permutations and arbitrary fanout are uncharged. -/
structure Circuit (n : ℕ) where
  /-- The number of charged scalar operations. -/
  size : ℕ
  /-- The topologically ordered operations. -/
  program : Program n size
  /-- A freely chosen available wire for each output coordinate. -/
  outputs : Fin n → Fin (n + 1 + size)

/-- Read all designated outputs after evaluating the program. -/
def Circuit.eval {n : ℕ} (C : Circuit n) (x : Fin n → ℂ) : Fin n → ℂ :=
  fun i => C.program.eval x (C.outputs i)

/-- The standard complex root used by the exact discrete Fourier transform. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
/-- The unnormalized DFT matrix, with positive exponential sign. -/
noncomputable def fourierMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => zeta n ^ (j.val * k.val)

/-- Exact matrix multiplication on every complex input vector. -/
def Circuit.Computes {n : ℕ} (C : Circuit n) (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ x, C.eval x = A.mulVec x

/-- Arbitrarily large sizes admit circuits below any fixed multiple of `n * log₂ n`. -/
def MainStatement : Prop :=
  ∀ c : ℝ, 0 < c → ∀ N₀ : ℕ, 2 ≤ N₀ → ∃ n : ℕ, N₀ ≤ n ∧
    ∃ C : Circuit n, C.Computes (fourierMatrix n) ∧
      (C.size : ℝ) < c * (n : ℝ) * Real.logb 2 (n : ℝ)

end ExactFourier
end

end Complexity
