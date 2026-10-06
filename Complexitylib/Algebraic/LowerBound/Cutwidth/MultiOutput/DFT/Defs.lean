/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# The discrete Fourier transform matrix

For an element `ω` of a field and `N : ℕ`, `dft ω N` is the `N × N` matrix `(ω ^ (r c))` with
rows `r` (the outputs) and columns `c` (the inputs), both indexed by `0, …, N - 1`. When `ω` is
a primitive `N`-th root of unity, `x ↦ dft ω N x` is the `N`-point discrete Fourier transform:
over `ℂ` with `ω = e^{2πi/N}` it is the classical DFT (for `N = 2^k`, the map computed by the
fast Fourier transform), and over `ZMod q` with `N ∣ q - 1` it is a number-theoretic transform.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

/-- The `N × N` discrete Fourier transform matrix `(ω ^ (r c))`: row `r`, column `c`. -/
def dft {F : Type*} [Monoid F] (ω : F) (N : ℕ) : Matrix (Fin N) (Fin N) F :=
  Matrix.of fun r c => ω ^ ((r : ℕ) * c)

end Algebraic.Cutwidth.MultiOutput
