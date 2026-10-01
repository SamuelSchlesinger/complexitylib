/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.FiniteCounting
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Hamming layers and the initial majority deficit

Strict majority uses the library predicate `Complexity.majority`, so a tie
is false. The two layers at weights `n/2` and `n/2+1` straddle its threshold.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis

open Finset

/-- The Boolean vectors with exactly `r` true coordinates. -/
def weightLayer (n r : ℕ) : Finset (Fin n → Bool) :=
  univ.filter (fun x => popCount x = r)

/-- A common deficit and density-limit bound for the two majority boundary layers.
The logarithmic term bounds their entropy deficit; `128` bounds the mask size. -/
noncomputable def majorityDeficitBound (n : ℕ) : ℝ :=
  128 + Real.logb 2 (2 * ((n : ℝ) + 1))

end Complexity.BooleanAnalysis
