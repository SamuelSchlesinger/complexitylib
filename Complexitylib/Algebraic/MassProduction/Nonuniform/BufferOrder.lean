/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferAdvance

/-!
# Request identities through buffer advancement

Tagged completed/pending indices form one permutation of the original
requests. Moving a selected prefix into the completed side is an explicit
equivalence, so no request is lost or duplicated during phase compaction.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BufferOrder

open BufferAdvance

/-- Reassociate the accepted prefix into the completed side, then apply the
phase's request permutation and the previous global request order. -/
def advance (order : (Fin completed ⊕ Fin pending) ≃ Fin total)
    (permutation : Equiv.Perm (Fin pending)) (split : accepted + remaining = pending) :
    (Fin (completed + accepted) ⊕ Fin remaining) ≃ Fin total :=
  ((((Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl (Fin remaining))).trans
    (Equiv.sumAssoc (Fin completed) (Fin accepted) (Fin remaining))).trans
    (Equiv.sumCongr (Equiv.refl (Fin completed))
      ((finSumFinEquiv.trans (finCongr split)).trans permutation))).trans order)

/-- Previously completed request identities do not change. -/
theorem advance_completed (order : (Fin completed ⊕ Fin pending) ≃ Fin total)
    (permutation : Equiv.Perm (Fin pending)) (split : accepted + remaining = pending)
    (index : Fin completed) :
    advance order permutation split (.inl (Fin.castAdd accepted index)) = order (.inl index) := by
  simp [advance]

/-- The newly completed identities are exactly the selected permuted prefix. -/
theorem advance_accepted (order : (Fin completed ⊕ Fin pending) ≃ Fin total)
    (permutation : Equiv.Perm (Fin pending)) (split : accepted + remaining = pending)
    (index : Fin accepted) :
    advance order permutation split (.inl (Fin.natAdd completed index)) =
      order (.inr (permutation (acceptedIndex split index))) := by
  simp only [advance, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_symm_apply_natAdd, Equiv.sumAssoc_apply_inl_inr, Sum.map_inr,
    finSumFinEquiv_apply_left]
  rfl

/-- The remaining identities are exactly the selected permuted suffix. -/
theorem advance_pending (order : (Fin completed ⊕ Fin pending) ≃ Fin total)
    (permutation : Equiv.Perm (Fin pending)) (split : accepted + remaining = pending)
    (index : Fin remaining) :
    advance order permutation split (.inr index) = order (.inr (permutation (pendingIndex split index))) := by
  simp only [advance, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply,
    Equiv.sumAssoc_apply_inr, Sum.map_inr, finSumFinEquiv_apply_right]
  rfl

end Algebraic.MassProduction.Nonuniform.BufferOrder
