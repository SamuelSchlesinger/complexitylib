/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Defs
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Internal.Wires

/-!
# Korten's top-down communication adversary

The improved mirror set maintains a density rectangle through arbitrary
bounded-alphabet messages. The speaker may depend on the transcript. Early
termination is ruled out by the absence of a fixed separating coordinate.

The finite bound with bilateral initial limits uses only `d` mirror steps
for a protocol with at most `d+1` messages. Parity initialization then proves
the communication lower bound and its exponential wire corollary in Theorem 3 of
Oliver Korten, *Top-Down Lower Bounds for All Depths*, ECCC TR26-221 (2026),
https://eccc.weizmann.ac.il/report/2026/221/.
-/

public section

namespace Complexity.KarchmerWigderson.RoundProtocol

open BooleanAnalysis

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]

/-- The density-rectangle adversary for any parameter sequences satisfying
the one-message deficit and sampling-rate recurrences. -/
theorem not_solves_density {d : ℕ} (P : RoundProtocol ι M d)
    {X Y : Finset (ι → Bool)} {m : ℝ} (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m)
    (k p : ℕ → ℝ)
    (hstep : ∀ i < d, 1 ≤ k i ∧ 194 * k i ≤ k (i + 1) ∧
      2 * k i + 2 + m ≤ k (i + 1) ∧ 32768 * k i * p i ≤ p (i + 1))
    (hcap : ∀ i ≤ d, p i ≤ 1 / 4) (h : DensityRectangle X Y (p 0) (k 0)) :
    ¬ P.Solves X Y := not_solves_density_internal P hM k p hstep hcap h

/-- Explicit finite specialization of the adversary for `d` rounds. -/
theorem not_solves_bounded_density {d : ℕ} (P : RoundProtocol ι M d)
    {X Y : Finset (ι → Bool)} {m k p : ℝ}
    (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) (hk : 1 ≤ k) (hmk : m + 1 ≤ k)
    (hbudget : (32768 * (194 : ℝ) ^ d * k) ^ d * p ≤ 1 / 4)
    (h : DensityRectangle X Y p k) : ¬ P.Solves X Y :=
  not_solves_bounded_density_internal P hM hk hmk hbudget h

/-- Bilateral initial limits save the first mirror step. This is the
finite obstruction with an arbitrary initial deficit bound `k ≥ 1`. -/
theorem not_solves_bilateral_density_with_deficit {d : ℕ} (P : RoundProtocol ι M (d + 1))
    {X Y : Finset (ι → Bool)} {m p k : ℝ}
    (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) (hm : 0 ≤ m) (hk : 1 ≤ k) (hp : 0 < p)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hdX : uniformDeficit X ≤ k) (hdY : uniformDeficit Y ≤ k)
    (hleft : ∀ x ∈ X, IsDensityLimit Y p k x) (hright : ∀ y ∈ Y, IsDensityLimit X p k y)
    (hbudget : (32768 * (194 : ℝ) ^ d * (m + k)) ^ d * p ≤ 1 / 4) :
    ¬ P.Solves X Y :=
  not_solves_bilateral_density_with_deficit_internal
    P hM hm hk hp hX hY hdX hdY hleft hright hbudget

/-- Bilateral initial limits save the first mirror step. This is the
`d`-th-power obstruction for protocols with at most `d+1` rounds. -/
theorem not_solves_bilateral_density {d : ℕ} (P : RoundProtocol ι M (d + 1))
    {X Y : Finset (ι → Bool)} {m p : ℝ}
    (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) (hm : 0 ≤ m) (hp : 0 < p)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hdX : uniformDeficit X ≤ 1) (hdY : uniformDeficit Y ≤ 1)
    (hleft : ∀ x ∈ X, IsDensityLimit Y p 1 x) (hright : ∀ y ∈ Y, IsDensityLimit X p 1 y)
    (hbudget : (32768 * (194 : ℝ) ^ d * (m + 1)) ^ d * p ≤ 1 / 4) :
    ¬ P.Solves X Y :=
  not_solves_bilateral_density_internal P hM hm hp hX hY hdX hdY hleft hright hbudget

/-- Explicit finite obstruction for parity protocols with `d+1` messages.
The alphabet has at most `2^m` symbols, and the displayed `d`-th-power
condition is the checked finite form of the top-down bound. -/
theorem not_solves_parity_finite {n d : ℕ} (P : RoundProtocol (Fin n) M (d + 1))
    {m : ℝ} (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) (hm : 0 ≤ m)
    (hsize : 16 * (32768 * (194 : ℝ) ^ d * (m + 1)) ^ d ≤ (n : ℝ)) :
    ¬ P.SolvesKW (Schnorr.xorBool n) :=
  not_solves_parity_finite_internal P hM hm hsize

end Complexity.KarchmerWigderson.RoundProtocol

universe u

namespace Complexity.KarchmerWigderson

/-- Communication part of Korten's Theorem 3: for every `rounds ≥ 2`, a
positive constant depending only on `rounds` rules out all parity protocols
whose per-message cost is at most `epsilon*n^(1/(rounds-1))`, for sufficiently
large `n`. The quantifiers include every finite message alphabet. -/
theorem parity_communication_lower_bound (rounds : ℕ) (hrounds : 2 ≤ rounds) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ {M : Type u} [Fintype M] [DecidableEq M] (m : ℝ), 0 ≤ m →
        (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m →
        m ≤ ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹) →
        ∀ P : RoundProtocol (Fin n) M rounds, ¬ P.SolvesKW (Schnorr.xorBool n) :=
  parity_communication_lower_bound_internal rounds hrounds

end Complexity.KarchmerWigderson

namespace Complexity.Circuit

/-- Circuit part of Korten's Theorem 3. For every fixed depth at least two,
all sufficiently large parity circuits over the unbounded De Morgan basis
have more than `2^(epsilon*n^(1/(depth-1)))` input-wire occurrences.
The constant depends only on depth. Per-input negations are free. -/
theorem parity_wire_lower_bound (rounds : ℕ) (hrounds : 2 ≤ rounds) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ [NeZero n] (g : ℕ)
      (c : Circuit Basis.unboundedAndOr n 1 g), c.depth ≤ rounds →
      (∀ x, c.eval x 0 = Schnorr.xorBool n x) →
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹)) < c.totalFanIn :=
  parity_wire_lower_bound_internal rounds hrounds

end Complexity.Circuit
