/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly
public import Complexitylib.Classes.L
public import Complexitylib.Circuits.Encoding.Family

/-!
# Uniform P/poly

The **logspace-uniform** polynomial-size circuit class (Arora–Barak Definition 6.5).
A circuit family is logspace-uniform when its tagged code map `1ⁿ ↦ (code of the
length-n member)` is computable by a deterministic log-space transducer (`FL`).
`UniformPPoly` restricts `PPoly` to such families.

Uniformity is what makes a nonuniform circuit class comparable to a uniform machine
class: the headline `UniformPPoly = P` (Arora–Barak Theorem 6.7; roadmap M1) rests on
this definition — the easy containment `UniformPPoly ⊆ P` runs the log-space generator
(`FL ⊆ FP`) and evaluates the produced code, and `P ⊆ UniformPPoly` unrolls a
time-bounded DTM into a logspace-uniform tableau family.

Logspace-uniformity (rather than the weaker P-uniformity) is the Arora–Barak
convention and is what lets the same uniformity notion later scale down to `NC`/`AC`.

## Main definitions and results

- `unaryList` — the unary input `1ⁿ`.
- `CircuitFamily.Uniform` — logspace-uniformity of a family (its `encodeAt` code map
  is in `FL`).
- `UniformPPoly` — the logspace-uniform polynomial-size class.
- `UniformPPoly_subset_PPoly` — uniform P/poly is contained in nonuniform P/poly.

The circuits-to-machines containment is exposed separately as
`UniformPPoly_subset_P` in `Complexitylib.Classes.PPoly.Uniform.Containment`.
-/

@[expose] public section

namespace Complexity

/-- The unary encoding of `n` as `1ⁿ` (n `true` bits): the standard generator input
    that keeps generator time polynomial in `n` rather than in `log n`. -/
def unaryList (n : ℕ) : List Bool := List.replicate n true

/-- A circuit family is **logspace-uniform** (Arora–Barak Definition 6.5) when its
    tagged code map `1ⁿ ↦ (code of the length-n member)` is computable by a
    deterministic log-space transducer. The tagged `encodeAt` codec already carries
    the length-zero answer explicitly, so a single generator function produces the
    whole family. -/
def CircuitFamily.Uniform (F : CircuitFamily Basis.andOr2) : Prop :=
  ∃ gen ∈ FL, ∀ n, gen (unaryList n) = F.encodeAt n

/-- **Uniform P/poly**: languages decided by a logspace-uniform polynomial-size
    fan-in-two AND/OR circuit family. The uniform companion of `PPoly`; the M1
    headline is `UniformPPoly = P` (Arora–Barak Theorem 6.7). -/
def UniformPPoly : Set Language :=
  { L | ∃ (F : CircuitFamily Basis.andOr2) (p : Polynomial ℕ),
      F.Decides L ∧ F.SizeBoundedBy (fun n => p.eval n) ∧ F.Uniform }

/-- **Uniform P/poly is contained in nonuniform P/poly.** Forgetting the uniformity
    generator leaves exactly a polynomial-size family deciding the language. -/
theorem UniformPPoly_subset_PPoly : UniformPPoly ⊆ PPoly := by
  rintro L ⟨F, p, hdec, hsize, -⟩
  exact Set.mem_iUnion.mpr ⟨p, F, hdec, hsize⟩

end Complexity
