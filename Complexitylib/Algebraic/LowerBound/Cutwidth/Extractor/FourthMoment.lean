/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.FourthMoment.Internal

/-!
# A fourth-moment certificate for both majority tails

The constant-error sumset-extractor route only needs each Boolean outcome to
have some fixed positive probability. Four-wise independent fair bits provide
the first four moments of an independent sign sum. After normalization, the
quartic `u * (u + 1)^2 * (3 - u)` proves that each tail beyond `1/8` has mass at
least `1/36`. This elementary certificate avoids a general theorem about
bounded independence fooling halfspaces. Together with the deterministic margin
lemmas, it permits fewer than one eighth of a standard deviation in arbitrary
bad votes.

The intended source reduction is Chattopadhyay and Liao, *Extractors for Sum
of Two Sources* (2021), Lemma 5.4. The quartic estimate here is a direct
calculation. `Moments` bounds raw sign-sum moments from parity bias, and
`Moments.Tails` supplies the normalization used by `Majority.Probability`.
`SourceReduction.Construction` constructs the source reduction that supplies
these parity bounds (`sourceReductionExtractor_flat`).
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Approximate first four normal moments suffice for a positive tail of
mass at least `1/36`, beyond the normalized margin `1/8`. -/
theorem fourthMoment_positive_tail_of_approx {α : Type*} (s : Finset α) (w Z : α → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : |∑ i ∈ s, w i * Z i| ≤ 1 / 100)
    (hsecond : (99 / 100 : ℝ) ≤ ∑ i ∈ s, w i * Z i ^ 2)
    (hthird : |∑ i ∈ s, w i * Z i ^ 3| ≤ 1 / 100)
    (hfourth : ∑ i ∈ s, w i * Z i ^ 4 ≤ 301 / 100) :
    (1 / 36 : ℝ) ≤ ∑ i ∈ s, if 1 / 8 < Z i then w i else 0 :=
  Internal.fourthMoment_positive_tail_of_approx s w Z hw hmass hmean hsecond hthird hfourth

/-- Approximate first four normal moments also force the negative tail,
by applying the same certificate to the negated variable. -/
theorem fourthMoment_negative_tail_of_approx {α : Type*} (s : Finset α) (w Z : α → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : |∑ i ∈ s, w i * Z i| ≤ 1 / 100)
    (hsecond : (99 / 100 : ℝ) ≤ ∑ i ∈ s, w i * Z i ^ 2)
    (hthird : |∑ i ∈ s, w i * Z i ^ 3| ≤ 1 / 100)
    (hfourth : ∑ i ∈ s, w i * Z i ^ 4 ≤ 301 / 100) :
    (1 / 36 : ℝ) ≤ ∑ i ∈ s, if Z i < -(1 / 8) then w i else 0 :=
  Internal.fourthMoment_negative_tail_of_approx s w Z hw hmass hmean hsecond hthird hfourth

/-- Exact normal moments through degree three and fourth moment at most
three imply the positive-tail bound. -/
theorem fourthMoment_positive_tail {α : Type*} (s : Finset α) (w Z : α → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * Z i = 0)
    (hsecond : ∑ i ∈ s, w i * Z i ^ 2 = 1)
    (hthird : ∑ i ∈ s, w i * Z i ^ 3 = 0)
    (hfourth : ∑ i ∈ s, w i * Z i ^ 4 ≤ 3) :
    (1 / 36 : ℝ) ≤ ∑ i ∈ s, if 1 / 8 < Z i then w i else 0 :=
  Internal.fourthMoment_positive_tail s w Z hw hmass hmean hsecond hthird hfourth

/-- The corresponding negative-tail bound under exact moment identities. -/
theorem fourthMoment_negative_tail {α : Type*} (s : Finset α) (w Z : α → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * Z i = 0)
    (hsecond : ∑ i ∈ s, w i * Z i ^ 2 = 1)
    (hthird : ∑ i ∈ s, w i * Z i ^ 3 = 0)
    (hfourth : ∑ i ∈ s, w i * Z i ^ 4 ≤ 3) :
    (1 / 36 : ℝ) ≤ ∑ i ∈ s, if Z i < -(1 / 8) then w i else 0 :=
  Internal.fourthMoment_negative_tail s w Z hw hmass hmean hsecond hthird hfourth

end Algebraic.Cutwidth.Extractor
