/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Power.Defs
public import Complexitylib.Classes.Randomized.ApproximateCounting.Weak.Hashing.Defs

/-!
# Relative approximate counting -- definitions

The amplified relative estimator runs the factor-`16` hashing estimator on a
Cartesian power and recovers an integer count through the upper-root rounding
convention. A parameter `failureBits` sets the failure probability, which the
surface module bounds by `2^-failureBits`; constant success probability `3/4`
is the case `failureBits = 2`.
-/


@[expose] public section

namespace Complexity

namespace ApproximateCounting

namespace Relative

/-- Input width of the powered set supplied to the weak estimator. -/
def poweredWidth (domainWidth precision : ℕ) : ℕ :=
  relativeCopies precision * domainWidth

/-- Per-level amplification used inside the weak estimator. The extra
`poweredWidth + 2` bits pay for the union over all hash widths; `failureBits`
is the remaining global failure exponent. -/
def errorBits (domainWidth precision failureBits : ℕ) : ℕ :=
  poweredWidth domainWidth precision + 2 + failureBits

/-- Total random-seed width of the amplified relative estimator with failure
exponent `failureBits` (failure probability at most `2^-failureBits`). -/
def seedWidth (domainWidth precision failureBits : ℕ) : ℕ :=
  Weak.hashingSeedWidth (poweredWidth domainWidth precision)
    (errorBits domainWidth precision failureBits)

/-- Amplified relative cardinality estimate for a fixed finite set. -/
def hashingEstimate {domainWidth : ℕ} (precision failureBits : ℕ)
    (set : Finset (BitString domainWidth))
    (seed : BitString (seedWidth domainWidth precision failureBits)) : ℕ :=
  boostedEstimate precision <|
    Weak.hashingEstimate
      (cartesianPower set (relativeCopies precision)) seed

/-- Seeds on which the relative hashing estimate satisfies its target
accuracy contract. -/
def successEvent {domainWidth : ℕ} (precision failureBits : ℕ)
    (set : Finset (BitString domainWidth)) :
    Finset (BitString (seedWidth domainWidth precision failureBits)) :=
  Finset.univ.filter fun seed =>
    IsRelativeApproximation precision set.card
      (hashingEstimate precision failureBits set seed)

/-- Seeds on which the amplified relative estimator misses its accuracy
contract. -/
def failureEvent {domainWidth : ℕ} (precision failureBits : ℕ)
    (set : Finset (BitString domainWidth)) :
    Finset (BitString (seedWidth domainWidth precision failureBits)) :=
  (successEvent precision failureBits set)ᶜ

end Relative

end ApproximateCounting

end Complexity
