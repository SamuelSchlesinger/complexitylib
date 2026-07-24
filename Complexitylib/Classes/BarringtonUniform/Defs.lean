/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform
import Complexitylib.Circuits.BarringtonCodeGenerator
import Complexitylib.Circuits.BarringtonConverse

/-!
# Uniform Barrington classes -- definitions

This file gives formula families and width-`5` branching-program families the
same canonical log-space uniformity contract already used for circuit families:
an `FL` transducer emits the codec for the length-`n` member on unary input
`1^n`.

It also names the exact remaining forward-uniformity obligation. The executable
compiler defines a concrete program family; `UniformBarringtonCompilation` says
that a log-depth uniform formula family makes that concrete family uniform.
Unlike a claim about the unbounded formula-code transformer on every input,
this promise-family statement permits a total generator to stay polynomial on
off-family inputs.
-/

namespace Complexity

namespace FormulaFamily

/-- A formula family is log-space uniform when an `FL` generator emits its
canonical postfix code on unary family indices. -/
def Uniform (family : FormulaFamily) : Prop :=
  ∃ generator ∈ FL, ∀ n,
    generator (unaryList n) = FormulaCode.encode (family n)

/-- The concrete width-`5` family produced by the executable Barrington
compiler at its fixed canonical target cycle. -/
def barringtonProgram (family : FormulaFamily) : BPFamily 5 :=
  fun n => barringtonCompile (family n) barringtonTargetBase

end FormulaFamily

namespace BPFamily

/-- A width-`5` branching-program family is log-space uniform when an `FL`
generator emits its canonical program code on unary family indices. -/
def Uniform (family : BPFamily 5) : Prop :=
  ∃ generator ∈ FL, ∀ n,
    generator (unaryList n) = BPCode.Program.encode (family n)

end BPFamily

/-- Functions computed by log-depth, log-space-uniform formula families. -/
def UniformFormulaNC1 : Set (ℕ → (ℕ → Bool) → Bool) :=
  {function | ∃ family : FormulaFamily,
    family.LogDepth ∧ family.Uniform ∧ family.Computes function}

/-- Functions decided by polynomial-length, log-space-uniform width-`5`
permutation branching-program families. -/
def UniformWidth5BP : Set (ℕ → (ℕ → Bool) → Bool) :=
  {function | ∃ (family : BPFamily 5) (point : ℕ → Fin 5),
    family.PolynomialLength ∧ family.Uniform ∧
      family.Decides point function}

/-- The exact remaining forward-uniformity obligation: explicit Barrington
compilation preserves uniformity under the logarithmic-depth promise. -/
def UniformBarringtonCompilation : Prop :=
  ∀ family : FormulaFamily,
    family.LogDepth → family.Uniform → family.barringtonProgram.Uniform

end Complexity
