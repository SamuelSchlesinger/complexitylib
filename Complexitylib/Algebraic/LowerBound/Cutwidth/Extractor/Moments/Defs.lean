/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-!
# Finite sign averages and low-order parity bias

These finite weighted sums describe the moment hypotheses needed after the
source reduction in Chattopadhyay and Liao, *Extractors for Sum of Two Sources*
(2021), Lemma 5.4, equation (5). No source reduction is assumed or constructed
here. The `m` selected good coordinates are indexed by `Fin m`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Weighted average over a finite sample set. Probability applications use
nonnegative weights of total mass one. -/
def weightedMean {α : Type*} (s : Finset α) (w X : α → ℝ) : ℝ :=
  ∑ a ∈ s, w a * X a

/-- Sum of the selected sign coordinates at a sample. -/
def signSum {α : Type*} {m : Nat} (σ : α → Fin m → ℝ) (a : α) : ℝ :=
  ∑ i, σ a i

/-- Every nonempty parity on at most four selected coordinates has absolute
weighted sign bias at most `δ`. The signs being `±1` is a separate hypothesis. -/
def ParityBiasBound {α : Type*} {m : Nat} (s : Finset α) (w : α → ℝ)
    (σ : α → Fin m → ℝ) (δ : ℝ) : Prop :=
  ∀ T : Finset (Fin m), T.Nonempty → T.card ≤ 4 →
    |weightedMean s w (fun a => ∏ i ∈ T, σ a i)| ≤ δ

end Algebraic.Cutwidth.Extractor
