/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Splitting successive pairs of blocks

Each pair keeps its two coordinates next to each other: pair `i` occupies
positions `2*i` and `2*i+1`. The tuple equivalence and the two-coordinate
prepend equivalence also cover empty tails and empty alphabets.

This is the coordinate map in Chattopadhyay--Goodman--Liao, Corollary 5.4
of *Affine Extractors for Almost Logarithmic Entropy*:
<https://eccc.weizmann.ac.il/report/2021/075/download/>.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Pair number `i` and within-pair coordinate `j` occupy position `j + 2*i`. -/
def splitBlockIndexEquiv (t : Nat) : Fin t × Fin 2 ≃ Fin (2 * t) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm t 2))

/-- Flatten pairs in their original order, retaining both coordinates of each pair. -/
def splitBlockEquiv (α : Type*) (t : Nat) :
    (Fin t → α × α) ≃ (Fin (2 * t) → α) :=
  (Equiv.piCongrRight fun _ : Fin t => (finTwoArrowEquiv α).symm).trans
    ((Equiv.curry (Fin t) (Fin 2) α).symm.trans
      (Equiv.arrowCongr (splitBlockIndexEquiv t) (Equiv.refl α)))

/-- Prepend the two coordinates of a pair to a tail tuple. -/
def pairPrependEquiv (α : Type*) (t : Nat) :
    ((α × α) × (Fin t → α)) ≃ (Fin (t + 2) → α) :=
  (Equiv.prodAssoc α α (Fin t → α)).trans
    ((Equiv.prodCongr (Equiv.refl α) (Fin.consEquiv (fun _ : Fin (t + 1) => α))).trans
      (Fin.consEquiv (fun _ : Fin (t + 2) => α)))

end Algebraic.Cutwidth.Extractor
