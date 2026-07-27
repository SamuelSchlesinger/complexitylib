/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Family.Defs
public import Complexitylib.Circuits.AndOrNot.Defs
public import Complexitylib.Models.TuringMachine

/-!
# Nonuniform circuit classes — definitions

This module defines language semantics for circuit families, pointwise circuit
size classes, and `PPoly`, the class conventionally written `P/poly`.

`PPoly` is initially specialized to the library's fan-in-two AND/OR basis with
free per-gate-input negation flags. Primary input vertices are also excluded
from `Circuit.size`. These choices preserve the usual polynomial-size class
after elementary overhead simulations, but exact `SIZE` bounds are
convention-dependent. Basis/size invariance must be proved rather than treated
as definitional.
-/

@[expose] public section

namespace Complexity

namespace BoolFunFamily

/-- The language whose characteristic function is `f`, using the canonical
    list-to-fixed-length representation. -/
def toLanguage (f : BoolFunFamily) : Language :=
  {x | f x.length x.get = true}

end BoolFunFamily

namespace CircuitFamily

variable {B : Basis}

/-- The language recognized by a circuit family. -/
def language (F : CircuitFamily B) : Language :=
  F.function.toLanguage

/-- `F` decides `L` when its recognized language is exactly `L`. -/
def Decides (F : CircuitFamily B) (L : Language) : Prop :=
  F.language = L

end CircuitFamily

/-- Languages decided by `B`-circuit families with the pointwise size bound
    `s`, using this library's non-input-gate count. -/
def SIZEWithBasis (B : Basis) (s : ℕ → ℕ) : Set Language :=
  {L | ∃ F : CircuitFamily B, F.Decides L ∧ F.SizeBoundedBy s}

/-- The fan-in-two AND/OR circuit-size class under the library's free-negation,
    non-input-gate convention. -/
def SIZE (s : ℕ → ℕ) : Set Language :=
  SIZEWithBasis Basis.andOr2 s

/-- **P/poly**: languages decided by polynomial-size nonuniform fan-in-two
    AND/OR circuit families under the library's size convention, expressed
    through the `SIZE` class as the union of the pointwise size classes over
    all natural-coefficient polynomials. Equivalent to the pointwise
    `PolynomialSize` formulation; see `PPoly_eq_iUnion_SIZE` (definitional) and
    the big-O characterization `mem_PPoly_iff`. -/
def PPoly : Set Language :=
  ⋃ p : Polynomial ℕ, SIZE fun n => p.eval n

end Complexity
