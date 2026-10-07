/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Recognition

/-!
# Transport of the liveness lower bound through word encodings

Apply OpenAI's `matching_recognition_degree` to the product of crossing diagrams
for each encoded letter. The encoding can have arbitrary, even varying, lengths.
No explicit deterministic simulation is needed and no state factor is lost.
-/

public section

namespace Complexity.FiniteAutomaton

theorem Machine.encoded_liveness_rank_bound {H Alpha Q : Type}
    [Fintype H] [Fintype Q] (M : Machine Alpha Q) (code : BRel H → List Alpha)
    (hM : ∀ w, M.Accepts false (w.flatMap code) ↔ BRel.Live w)
    (x y : H) (hxy : x ≠ y) :
    rankLoss (Fintype.card H) ≤ 4 * (Fintype.card Q + 1) ^ 2 := by
  classical
  let S := M.sinkCopy
  let cell := fun b => CellNetwork.bodyDiagram S none (.letter b)
  let η := fun R => ((code R).map cell).prod
  have hprod (w : List (BRel H)) :
      ((w.flatMap code).map cell).prod = (w.map η).prod := by
    induction w with
    | nil => rfl
    | cons a w ih =>
      simp only [List.flatMap_cons, List.map_append, List.prod_append, List.map_cons,
        List.prod_cons, ih]
      rfl
  have hr (w : List (BRel H)) :
      CellNetwork.recognitionTest S none (w.map η).prod ↔ BRel.Live w := by
    rw [← hprod, CellNetwork.recognitionTest_iff S none (by rfl)]
    exact (M.sinkCopy_accepts (w.flatMap code)).trans (hM w)
  have hb := matching_recognition_degree η (CellNetwork.recognitionTest S none) hr x y hxy
  have hc : Fintype.card (CellNetwork.Port (Option Q)) =
      4 * (Fintype.card Q + 1) ^ 2 := by
    simp only [CellNetwork.Port, CellNetwork.Slot, Fintype.card_prod, Fintype.card_bool,
      Fintype.card_option]
    ring
  rwa [hc] at hb

theorem encoded_oneWayLiveness_lower_bound_proof {Alpha : Type}
    (h : ℕ) (hh : 2 ≤ h) (code : Alphabet h → List Alpha)
    (positive : Bool) (s : ℕ) (D : DMachine Alpha s)
    (hD : ∀ w, D.Accepts positive (w.flatMap code) ↔ w ∈ oneWayLiveness h) :
    2 ^ ((h - 2) / 31) ≤ 4 * (s + if positive then 2 else 1) ^ 2 := by
  let x : Fin h := ⟨0, by lia⟩
  let y : Fin h := ⟨1, by lia⟩
  have hxy : x ≠ y := by
    intro he
    have := congrArg Fin.val he
    simp [x, y] at this
  cases positive with
  | false =>
    have hb := D.toMachine.encoded_liveness_rank_bound code hD x y hxy
    simpa only [rankLoss, Fintype.card_fin, Bool.false_eq_true, ↓reduceIte] using hb
  | true =>
    have hd (w) : D.toMachine.positiveCopy.Accepts false (w.flatMap code) ↔ BRel.Live w :=
      (D.toMachine.positiveCopy_accepts (w.flatMap code)).trans (hD w)
    have hb := D.toMachine.positiveCopy.encoded_liveness_rank_bound code hd x y hxy
    simpa only [rankLoss, Fintype.card_fin, Fintype.card_option, ↓reduceIte,
      Nat.add_assoc] using hb

end Complexity.FiniteAutomaton
