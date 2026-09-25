/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Systematic encoding from independent evaluation functions

Independent functions on a finite point set have an information set of the
same cardinality. A basis chosen from the evaluation rows gives an encoder
that is systematic on those points and preserves every linear identity
satisfied by the evaluation rows.
-/

@[expose] public section

namespace Algebraic.MassProduction.HighRate

open scoped BigOperators

/-- Independent evaluation functions admit a full-size information set.
The encoder is a linear functional applied to the evaluation row, so every
linear relation among rows is preserved. -/
theorem existsSystematicEncoder
    {K Index Point : Type*} [Field K] [Fintype Index] [Fintype Point]
    (functions : Index → Point → K) (independent : LinearIndependent K functions) :
    ∃ information : Set Point,
      Nat.card information = Fintype.card Index ∧
      ∃ encoder : (information → K) → ((Index → K) →ₗ[K] K),
        ∀ message index, encoder message (fun coordinate => functions coordinate index.val) =
          message index := by
  classical
  let row := flip functions
  have rowsSpan : Submodule.span K (Set.range row) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr independent
  obtain ⟨information, _, _, rowsCovered, independentRows⟩ :=
    exists_linearIndepOn_extension (v := row) (linearIndepOn_empty K row)
      (Set.empty_subset (Set.univ : Set Point))
  have selectedSpan : ⊤ ≤ Submodule.span K (Set.range fun index : information => row index.val) := by
    have rangeEquality : (Set.range fun index : information => row index.val) = row '' information := by
      ext value
      simp
    rw [rangeEquality]
    rw [← rowsSpan]
    apply Submodule.span_le.mpr
    intro value membership
    apply rowsCovered
    simpa only [Set.image_univ] using membership
  let basis : Module.Basis information K (Index → K) :=
    Module.Basis.mk independentRows selectedSpan
  have informationCard : Nat.card information = Fintype.card Index := by
    have cardBasis := Module.finrank_eq_card_basis basis
    rw [Module.finrank_fintype_fun_eq_card] at cardBasis
    simpa only [Nat.card_eq_fintype_card] using cardBasis.symm
  refine ⟨information, informationCard, fun message => basis.constr K message, ?_⟩
  intro message index
  have basisRow : basis index = row index.val :=
    Module.Basis.mk_apply independentRows selectedSpan index
  change (basis.constr K message) (row index.val) = message index
  rw [← basisRow]
  exact basis.constr_basis K message index

end Algebraic.MassProduction.HighRate
