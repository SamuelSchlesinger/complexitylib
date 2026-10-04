/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Defs

/-!
# Slice restrictions, tight tensors, and hyperplane projections

Definitions for border substitution on the first factor `A = ℂ^α` of a 3-tensor
`T : Tensor3 α β γ`, whose `A`-slices are the matrices `T i : β → γ → ℂ` (see
`Complexitylib.Algebraic.LinearAlgebra.Tensor.Substitution`).

* `Tensor3.restrictSlices T S` keeps the `A`-slices `T i` with `i ∈ S` and replaces the others
  by zero. In the language of Landsberg and Michałek, *Towards finding hay in a haystack*
  (Theory of Computing 2025, Definition 2.1), it is the restriction of `T` to the subspace of
  `A^*` spanned by the dual basis vectors `a_i^*`, `i ∈ S`, kept inside the ambient space
  `A ⊗ B ⊗ C` instead of being re-expressed over `ℂ^S`.
* `Tensor3.Tight T`: there are integer weights `τA`, `τB`, `τC` on the three coordinate bases,
  with `τA` injective, such that `τA i + τB j + τC k = 0` whenever `T i j k ≠ 0`. Landsberg and
  Michałek (Definition 2.2) ask for all three weight functions to be injective; only `τA` is
  needed here, so a tensor that is tight in their sense, in the given bases, satisfies
  `Tight`. The weights make `T` invariant under the one-parameter subgroup
  `t ↦ diag(t ^ τA i) ⊗ diag(t ^ τB j) ⊗ diag(t ^ τC k)` of `GL(A) × GL(B) × GL(C)`.
* `Tensor3.orthProj u` is the orthogonal projection `1 - (u^* u)⁻¹ u u^*` of `ℂ^α` onto the
  hyperplane orthogonal to `u`. For `u ≠ 0` its kernel is the line `ℂ u`; for `u = 0` it is the
  identity.
-/

@[expose] public section

namespace Algebraic.Tensor3

variable {α β γ : Type*}

/-- Keep the `A`-slices `T i` with `i ∈ S` and replace the others by zero: the `(i, j, k)`
coordinate is `T i j k` if `i ∈ S` and `0` otherwise. -/
def restrictSlices [DecidableEq α] (T : Tensor3 α β γ) (S : Finset α) : Tensor3 α β γ :=
  fun i j k => if i ∈ S then T i j k else 0

/-- `T` is tight with respect to its first factor: there are integer weights `τA`, `τB`, `τC` on
the coordinate bases of the three factors, with `τA` injective, such that every coordinate
`(i, j, k)` in the support of `T` has total weight `τA i + τB j + τC k = 0`. This is weaker than
tightness in the sense of Landsberg and Michałek, which also asks `τB` and `τC` to be
injective. -/
def Tight (T : Tensor3 α β γ) : Prop :=
  ∃ (τA : α → ℤ) (τB : β → ℤ) (τC : γ → ℤ), Function.Injective τA ∧
    ∀ i j k, T i j k ≠ 0 → τA i + τB j + τC k = 0

open Matrix in
/-- The orthogonal projection `1 - (u^* u)⁻¹ u u^*` of `ℂ^α` onto the hyperplane orthogonal to
`u`, where `u^*` is the conjugate transpose. Its kernel is the line `ℂ u` when `u ≠ 0`
(`Tensor3.orthProj_mulVec_eq_zero_iff`); `orthProj 0` is the identity. -/
noncomputable def orthProj [Fintype α] [DecidableEq α] (u : α → ℂ) : Matrix α α ℂ :=
  1 - (star u ⬝ᵥ u)⁻¹ • vecMulVec u (star u)

end Algebraic.Tensor3
