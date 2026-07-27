/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BarringtonConverse.Defs
public import Complexitylib.Circuits.BitString

/-!
# Fixed-arity nonuniform Barrington families -- definitions

The earlier Barrington family layer evaluates syntax on total assignments
`ℕ → Bool`. This file defines the fixed-arity objects needed for an actual
class of typed Boolean-function families:

* the formula selected at arity `n` may mention only variables below `n`;
* the positive-arity branching program selected at arity `n + 1` may query
  only variables below `n + 1`;
* the unique zero-bit answer of a branching-program family is stored
  separately, because a nonempty instruction necessarily carries a variable
  index.

Both objects denote `BoolFunFamily`, so the eventual equivalence has the
correct fixed-arity semantic domain.
-/

@[expose] public section

namespace Complexity

/-- A nonuniform family of formulas with an explicit arity bound on every
member. -/
structure FixedArityFormulaFamily where
  /-- The formula selected at each input length. -/
  formula : ℕ → BoolFormula
  /-- Every variable mentioned by the length-`n` formula is below `n`. -/
  variables_lt :
    ∀ n index, index ∈ (formula n).vars → index < n

namespace FixedArityFormulaFamily

/-- The typed Boolean-function family denoted by a fixed-arity formula family.
Out-of-range variables are canonically set to `false`, though `variables_lt`
ensures they are not read. -/
def function (F : FixedArityFormulaFamily) : BoolFunFamily :=
  fun n input => BoolFormula.eval input.toTotal (F.formula n)

/-- The formula depth at each input length. -/
def depth (F : FixedArityFormulaFamily) (n : ℕ) : ℕ :=
  (F.formula n).depth

/-- A fixed-arity formula family has logarithmic depth. -/
def LogDepth (F : FixedArityFormulaFamily) : Prop :=
  ∃ c, ∀ n, F.depth n ≤ c * Nat.log 2 n + c

/-- A fixed-arity formula family computes a typed Boolean-function family. -/
def Computes (F : FixedArityFormulaFamily) (f : BoolFunFamily) : Prop :=
  F.function = f

end FixedArityFormulaFamily

/-- A nonuniform width-`w` branching-program family with explicit positive
input arities and a separate zero-input answer. -/
structure FixedArityBPFamily (w : ℕ) where
  /-- The answer on the unique zero-bit input. -/
  emptyOutput : Bool
  /-- The program at input length `n + 1`. -/
  positiveProgram : ℕ → BP w
  /-- The point whose movement decides acceptance at input length `n + 1`. -/
  positiveQuery : ℕ → Fin w
  /-- The length-`n + 1` program queries only variables below `n + 1`. -/
  variables_lt :
    ∀ n instruction, instruction ∈ positiveProgram n →
      instruction.var < n + 1

namespace FixedArityBPFamily

/-- The program length at each typed input length. The separately stored
zero-input answer has length zero. -/
def length {w : ℕ} (R : FixedArityBPFamily w) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (R.positiveProgram n).length

/-- The typed Boolean-function family decided by movement of the designated
query point. -/
def function {w : ℕ} (R : FixedArityBPFamily w) : BoolFunFamily
  | 0, _ => R.emptyOutput
  | n + 1, input =>
      decide
        (BP.eval input.toTotal (R.positiveProgram n) (R.positiveQuery n) ≠
          R.positiveQuery n)

/-- A fixed-arity branching-program family has polynomial length. -/
def PolynomialLength {w : ℕ} (R : FixedArityBPFamily w) : Prop :=
  ∃ C p, ∀ n, R.length n ≤ C * (n + 1) ^ p

/-- A fixed-arity branching-program family decides a typed Boolean-function
family. -/
def Decides {w : ℕ} (R : FixedArityBPFamily w)
    (f : BoolFunFamily) : Prop :=
  R.function = f

end FixedArityBPFamily

/-- Typed Boolean-function families computed by variable-bounded,
logarithmic-depth formula families. -/
def FormulaNC1 : Set BoolFunFamily :=
  {f | ∃ F : FixedArityFormulaFamily, F.LogDepth ∧ F.Computes f}

/-- Typed Boolean-function families decided by variable-bounded,
polynomial-length width-`5` permutation branching-program families. -/
def Width5BP : Set BoolFunFamily :=
  {f | ∃ R : FixedArityBPFamily 5, R.PolynomialLength ∧ R.Decides f}

end Complexity
