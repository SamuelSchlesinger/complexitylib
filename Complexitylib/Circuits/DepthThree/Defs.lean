/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.NormalForm.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Nat

/-!
# Depth-three formulas with bounded bottom fan-in -- definitions

A `Σ₃^k` formula is an OR of CNFs of width at most `k`: a depth-three `OR`-`AND`-`OR` formula
whose bottom gates have fan-in at most `k`. Its size is the number of CNFs (the top fan-in). Dually,
a `Π₃^k` formula is an AND of DNFs of width at most `k`. The CNFs and DNFs are the library's
`Complexity.CNF` and `Complexity.DNF`; the size measures count only the top gate's inputs, so they
lower-bound every reasonable size measure of these formulas.

## Main definitions

* `IsSigmaThree k f Fs`: the OR of the CNFs `Fs`, each of width at most `k`, computes `f`.
* `IsPiThree k f Gs`: the AND of the DNFs `Gs`, each of width at most `k`, computes `f`.
* `sigmaThreeSize k f`, `piThreeSize k f`: the least number of CNFs, respectively DNFs, in such a
  formula for `f` (`Σ₃^k(f)` and `Π₃^k(f)`).
-/

@[expose] public section

namespace Complexity

variable {N : ℕ}

/-- `Fs` is a `Σ₃^k` formula for `f`: an OR of CNFs, each of width at most `k`, that computes
`f`. -/
def IsSigmaThree (k : ℕ) (f : BitString N → Bool) (Fs : List (CNF N)) : Prop :=
  (∀ F ∈ Fs, F.width ≤ k) ∧ ∀ x, f x = Fs.any fun F => F.eval x

/-- `Gs` is a `Π₃^k` formula for `f`: an AND of DNFs, each of width at most `k`, that computes
`f`. -/
def IsPiThree (k : ℕ) (f : BitString N → Bool) (Gs : List (DNF N)) : Prop :=
  (∀ G ∈ Gs, G.width ≤ k) ∧ ∀ x, f x = Gs.all fun G => G.eval x

/-- `Σ₃^k(f)`: the least number of CNFs of width at most `k` whose OR computes `f`. For `k ≥ 1`
such formulas exist (`Complexity.exists_isSigmaThree`). -/
noncomputable def sigmaThreeSize (k : ℕ) (f : BitString N → Bool) : ℕ :=
  sInf {t | ∃ Fs, IsSigmaThree k f Fs ∧ Fs.length = t}

/-- `Π₃^k(f)`: the least number of DNFs of width at most `k` whose AND computes `f`. -/
noncomputable def piThreeSize (k : ℕ) (f : BitString N → Bool) : ℕ :=
  sInf {t | ∃ Gs, IsPiThree k f Gs ∧ Gs.length = t}

end Complexity
