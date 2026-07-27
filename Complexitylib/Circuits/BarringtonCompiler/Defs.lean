/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Barrington
public import Complexitylib.Circuits.BarringtonS5
public import Complexitylib.Circuits.Formula

/-!
# An executable Barrington compiler -- definitions

The original existence proof chooses conjugators and commutator factors inside
`Prop`. This module instead searches the finite group `S₅` explicitly, making
the target-cycle decomposition and the resulting formula compiler executable.
-/

@[expose] public section

open scoped commutatorElement
open Equiv

namespace Complexity

/-- A computable enumeration of every permutation of `Fin n`, obtained from
the recursive decomposition `S_(n+1) ≃ Fin (n+1) × S_n`. -/
def allPermutationsFin : (n : ℕ) → List (Perm (Fin n))
  | 0 => [1]
  | n + 1 =>
      (List.finRange (n + 1)).flatMap fun imageZero =>
        (allPermutationsFin n).map fun tail =>
          Equiv.Perm.decomposeFin.symm (imageZero, tail)

/-- Test whether `g` conjugates `source` to `target`. -/
def isConjugator5 (source target g : Perm (Fin 5)) : Bool :=
  decide (g * source * g⁻¹ = target)

/-- The first conjugator in the canonical finite enumeration of `S₅`, or the
identity if no conjugator exists. -/
def firstConjugator5 (source target : Perm (Fin 5)) : Perm (Fin 5) :=
  ((allPermutationsFin 5).find? (isConjugator5 source target)).getD 1

/-- The first fixed `5`-cycle in the explicit Barrington commutator. -/
def barringtonLeftBase : Perm (Fin 5) :=
  finRotate 5

/-- The second fixed `5`-cycle in the explicit Barrington commutator. -/
def barringtonRightBase : Perm (Fin 5) :=
  ([0, 2, 4, 3, 1] : List (Fin 5)).formPerm

/-- The fixed target cycle obtained as the commutator of the two base cycles. -/
def barringtonTargetBase : Perm (Fin 5) :=
  ⁅barringtonLeftBase, barringtonRightBase⁆

/-- Canonically search for a permutation conjugating the fixed target cycle to
`target`. -/
def barringtonConjugator (target : Perm (Fin 5)) : Perm (Fin 5) :=
  firstConjugator5 barringtonTargetBase target

/-- The left factor in the canonical commutator decomposition of `target`. -/
def barringtonLeft (target : Perm (Fin 5)) : Perm (Fin 5) :=
  barringtonConjugator target * barringtonLeftBase *
    (barringtonConjugator target)⁻¹

/-- The right factor in the canonical commutator decomposition of `target`. -/
def barringtonRight (target : Perm (Fin 5)) : Perm (Fin 5) :=
  barringtonConjugator target * barringtonRightBase *
    (barringtonConjugator target)⁻¹

namespace BP

/-- The four-block program commutator `p q p⁻¹ q⁻¹`. -/
def commutatorProgram {w : ℕ} (p q : BP w) : BP w :=
  p ++ q ++ BP.inverse p ++ BP.inverse q

end BP

/-- Compile a Boolean formula to a width-`5` permutation branching program
representing it through `target`.

The definition is total for every target permutation. Its correctness theorem
assumes that `target` is a `5`-cycle. Binary gates use the executable canonical
commutator decomposition above; no choice from an existential proof remains. -/
def barringtonCompile : BoolFormula → Perm (Fin 5) → BP 5
  | .var i, target => [⟨i, 1, target⟩]
  | .tru, target => [BPInstr.const target]
  | .fls, _ => []
  | .neg formula, target =>
      BP.postMul (barringtonCompile formula target⁻¹) target
  | .conj left right, target =>
      BP.commutatorProgram
        (barringtonCompile left (barringtonLeft target))
        (barringtonCompile right (barringtonRight target))
  | .disj left right, target =>
      let innerTarget := target⁻¹
      let leftTarget := barringtonLeft innerTarget
      let rightTarget := barringtonRight innerTarget
      let leftProgram := BP.postMul
        (barringtonCompile left leftTarget⁻¹) leftTarget
      let rightProgram := BP.postMul
        (barringtonCompile right rightTarget⁻¹) rightTarget
      BP.postMul (BP.commutatorProgram leftProgram rightProgram) target

end Complexity
