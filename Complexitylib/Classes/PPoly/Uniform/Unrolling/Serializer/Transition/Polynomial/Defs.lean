/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Next.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Fixed transition-schedule size polynomials -- definitions

Once a machine, atom kind, and finite transition selection table are fixed,
every nested transition-formula size is affine in the tableau horizon. These
polynomials let the executable serializer recover dynamic recent-wire offsets
with the verified binary polynomial evaluator instead of replaying a formula
tree or counting emitted gates.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- Gate count of one read-formula schedule as a polynomial in the horizon. -/
noncomputable def readSchedulePolynomial : Polynomial ℕ :=
  Polynomial.C 4 * (Polynomial.X + Polynomial.C 1) + Polynomial.C 1

/-- Gate count of one fixed transition-case schedule. -/
noncomputable def caseSchedulePolynomial
    (workCount : ℕ) (choiceValue : Bool) : Polynomial ℕ :=
  Polynomial.C (caseChoiceLiteralSize choiceValue + 1) +
    Polynomial.C (workCount + 2) * readSchedulePolynomial +
    Polynomial.C (1 + caseFormulaMemberCount workCount)

/-- Gate count of one selected or unselected effect member. -/
noncomputable def effectCasePolynomial (workCount : ℕ)
    (selected choiceValue : Bool) : Polynomial ℕ :=
  if selected then caseSchedulePolynomial workCount choiceValue
  else Polynomial.C 1

/-- Gate count of one fixed effect-formula schedule. -/
noncomputable def effectSchedulePolynomial
    (caseCount workCount : ℕ) (selectedAt choiceAt : ℕ → Bool) :
    Polynomial ℕ :=
  ((List.range caseCount).map fun caseIndex =>
      effectCasePolynomial workCount (selectedAt caseIndex)
        (choiceAt caseIndex)).sum +
    Polynomial.C (1 + caseCount)

/-- Gate count of one predecessor-head schedule. -/
noncomputable def predecessorHeadSchedulePolynomial : Polynomial ℕ :=
  Polynomial.C 2 * (Polynomial.X + Polynomial.C 1) + Polynomial.C 1

/-- Gate count of one fixed moved-head direction member. -/
noncomputable def movedHeadMemberPolynomial
    (caseCount workCount : ℕ) (selectedAt choiceAt : ℕ → Bool) :
    Polynomial ℕ :=
  effectSchedulePolynomial caseCount workCount selectedAt choiceAt +
    predecessorHeadSchedulePolynomial + Polynomial.C 1

/-- Gate count of a complete three-direction moved-head schedule. -/
noncomputable def movedHeadSchedulePolynomial
    (caseCount workCount : ℕ) (selectedAt : ℕ → ℕ → Bool)
    (choiceAt : ℕ → Bool) : Polynomial ℕ :=
  ((List.range movedHeadDirectionCount).map fun directionCode =>
      movedHeadMemberPolynomial caseCount workCount
        (selectedAt directionCode) choiceAt).sum +
    Polynomial.C (1 + movedHeadDirectionCount)

/-- Gate count of a complete positive writable-cell schedule. -/
noncomputable def writtenCellSchedulePolynomial
    (caseCount workCount : ℕ) (selectedAt choiceAt : ℕ → Bool) :
    Polynomial ℕ :=
  effectSchedulePolynomial caseCount workCount selectedAt choiceAt +
    Polynomial.C 7

/-- Gate count of a complete next-atom schedule for fixed numeric atom and
selection data. -/
noncomputable def nextSchedulePolynomial
    (caseCount workCount atomKind : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool) :
    Polynomial ℕ :=
  if atomKind = nextStateAtomKind then
    effectSchedulePolynomial caseCount workCount (selectedAt 0) choiceAt +
      Polynomial.C 7
  else if atomKind = nextHeadAtomKind then
    movedHeadSchedulePolynomial caseCount workCount selectedAt choiceAt +
      Polynomial.C 7
  else if atomKind = nextWritableCellAtomKind then
    writtenCellSchedulePolynomial caseCount workCount (selectedAt 0) choiceAt +
      Polynomial.C 7
  else Polynomial.C 1

end Serializer

end CircuitUnrolling

end Complexity
