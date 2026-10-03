/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import
Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Conditional.Internal

/-!
# Correlated marginal replacement with an external transcript

Two normalized laws with the same transcript marginal can be coupled
without changing that transcript. The coupling keeps the entire original
joint law and gives the replacement coordinate its prescribed joint law
with the transcript. Disagreement is exactly their joint marginal distance.
Its kernel makes the replacement conditionally independent of the old
second coordinate given the transcript and old first coordinate.

Projecting to the repaired pair preserves the transcript and second
coordinate together. Its full joint distance from the original law is
exactly the prescribed marginal distance. These are global average
identities; no per-transcript error bound or positive-row premise is used.

This extends the finite coupling construction across the conditioning
variable in Chattopadhyay--Goodman--Liao, *Affine Extractors for Almost
Logarithmic Entropy*, Lemma 4.19, which credits Li's 2015 Lemma 3.20:
<https://eccc.weizmann.ac.il/report/2021/075/download/>.
It supplies a probability repair used by affine correlation-breaker
arguments, without constructing a correlation breaker.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open scoped Classical

/-- Replace one marginal while keeping the original law and transcript. The
last identity is conditional independence, including zero-mass rows. -/
theorem exists_conditional_marginal_replacement_kernel {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    {p : Z × (A × B) → ℝ} {q : Z × A → ℝ}
    (hp : IsProbabilityWeight p) (hq : IsProbabilityWeight q)
    (same : firstWeight p = firstWeight q) :
    ∃ ρ : (Z × (A × B)) × A → ℝ, IsProbabilityWeight ρ ∧
      (∀ zab, ∑ a', ρ (zab, a') = p zab) ∧
      (∀ z a', ∑ ab, ρ ((z, ab), a') = q (z, a')) ∧
      (∑ t with t.1.2.1 ≠ t.2, ρ t) =
        weightDist (mapWeight (fun zab => (zab.1, zab.2.1)) p) q ∧
      ∀ z a b a', (∑ b', p (z, (a, b'))) * ρ ((z, (a, b)), a') =
        p (z, (a, b)) * (∑ b', ρ ((z, (a, b')), a')) :=
  Internal.exists_conditional_marginal_replacement_kernel hp hq same

/-- Replacing the transcript-and-first marginal preserves the full
transcript-and-second marginal at exactly the prescribed marginal distance. -/
theorem exists_conditional_joint_marginal_replacement {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    {p : Z × (A × B) → ℝ} {q : Z × A → ℝ}
    (hp : IsProbabilityWeight p) (hq : IsProbabilityWeight q)
    (same : firstWeight p = firstWeight q) :
    ∃ p' : Z × (A × B) → ℝ, IsProbabilityWeight p' ∧
      mapWeight (fun zab => (zab.1, zab.2.1)) p' = q ∧
      (∀ z b, ∑ a, p' (z, (a, b)) = ∑ a, p (z, (a, b))) ∧
      weightDist p p' = weightDist (mapWeight (fun zab => (zab.1, zab.2.1)) p) q :=
  Internal.exists_conditional_joint_marginal_replacement hp hq same

end Algebraic.Cutwidth.Extractor
