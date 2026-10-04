/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Defs

/-!
# Restricted splits: definitions

The rank-cut bound of `MultiOutput.Rank` counts all inputs. Restricted to the inputs agreeing
with a base point `z₀` off a set `J` of free coordinates, a function that changes by `g d` when
its input changes by a vector `d` supported on `J` is bounded through the following sets.

* `supportedKernel g P Q`: the vectors `d` supported on `P` (zero on every coordinate outside
  `P`) whose image `g d` vanishes on every coordinate in `Q`. For a linear `g` it is the kernel
  of the block of `g` with rows `Q` and columns `P`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

variable {n m : Nat}

/-- The vectors supported on `P` whose image under `g` vanishes on every coordinate in `Q`. -/
def supportedKernel {U : Type*} [Zero U] [Fintype U] [DecidableEq U]
    (g : (Fin n → U) → Fin m → U) (P : Finset (Fin n)) (Q : Finset (Fin m)) :
    Finset (Fin n → U) :=
  Finset.univ.filter fun d => (∀ k, k ∉ P → d k = 0) ∧ ∀ i ∈ Q, g d i = 0

end Algebraic.Cutwidth.MultiOutput
