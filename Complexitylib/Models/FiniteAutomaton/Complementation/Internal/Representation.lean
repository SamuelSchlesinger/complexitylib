/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Tape

/-!
# Two-way complementation: representation

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Representation.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

open scoped SetRel

/-- Every 2NFA has an exact diagram representation with one additional state label. -/
theorem TwoNFA.diagram_representation {Sigma : Type*} {s : ℕ} (A : TwoNFA Sigma (Fin s)) :
    ∃ τ : List Sigma → Diagram (s + 1), ∃ l r : Diagram (s + 1), ∃ a b : Fin (s + 1),
      τ [] = Diagram.identity (s + 1) ∧
      (∀ u v, τ (u ++ v) = Diagram.comp (τ u) (τ v)) ∧
      (∀ w, w ∈ A.language ↔ (a, b) ∈ (Diagram.comp (Diagram.comp l (τ w)) r).forward) := by
  let e := finSuccEquiv s
  let moves (symbol : Fin 2 ⊕ Sigma) (move : Fin 3) : SetRel (Fin (s + 1)) (Fin (s + 1)) :=
    {qr | (e qr.1, e qr.2) ∈ A.augmentedMove symbol move}
  let d (symbol : Fin 2 ⊕ Sigma) := cellDiagram (s + 1)
    (moves symbol 1) (moves symbol 2) (moves symbol 0)
  let a := e.symm (some A.initial)
  let b := e.symm none
  refine ⟨wordDiagram (fun symbol => d (Sum.inr symbol)), d (Sum.inl 0), d (Sum.inl 1),
    a, b, wordDiagram_nil _, wordDiagram_append _, ?_⟩
  intro w
  let cells : List (Fin 2 ⊕ Sigma) := Sum.inl 0 :: w.map Sum.inr
  let ec : (Fin (s + 1) × Fin (cells.length + 2)) ≃
      (Option (Fin s) × Fin (w.length + 3)) :=
    Equiv.prodCongr e (finCongr (by simp [cells]))
  have hread (c : ChainNode (s + 1) cells.length) (p : Fin (w.length + 2))
      (hp : c.position = p.val) : chainSymbol cells (Sum.inl 1) c = tapeSymbol w p := by
    rw [chainSymbol_getElem]
    simpa only [cells, List.cons_append, hp] using marked_getElem w p
  have hstep (x y : Fin (s + 1) × Fin (cells.length + 2)) :
      (ec x, ec y) ∈ A.augmentedStep w ↔ (x, y) ∈ chainStep moves cells (Sum.inl 1) := by
    rw [A.augmentedStep_local_iff]
    constructor
    · rintro ⟨p, hp, move, hmove, hdisp⟩
      have hpx : p.val = x.2.val := (congrArg Fin.val hp).symm
      have hbound : p.val ≤ cells.length := by simp [cells]; omega
      obtain ⟨c, _, hc⟩ := ChainNode.coordinates_surjective x.1 p.val hbound
      refine ⟨c, hpx.symm.trans hc.symm, move, ?_, ?_⟩
      · change (e x.1, e y.1) ∈ A.augmentedMove (chainSymbol cells (Sum.inl 1) c) move
        rw [hread c p hc]
        exact hmove
      · change (y.2.val : ℤ) = (p.val : ℤ) + (move.val : ℤ) - 1 at hdisp
        rwa [hpx] at hdisp
    · rintro ⟨c, hpos, move, hmove, hdisp⟩
      have hc : c.position < w.length + 2 := by
        have hbound := c.position_le
        simp only [cells, List.length_cons, List.length_map] at hbound
        omega
      let p : Fin (w.length + 2) := ⟨c.position, hc⟩
      refine ⟨p, Fin.ext hpos, move, ?_, ?_⟩
      · change (e x.1, e y.1) ∈ A.augmentedMove (tapeSymbol w p) move
        rw [← hread c p rfl]
        exact hmove
      · change (y.2.val : ℤ) = (c.position : ℤ) + (move.val : ℤ) - 1
        rwa [hpos] at hdisp
  have hstart : ec (a, ⟨0, by omega⟩) =
      TwoNFA.augmentConfig (A.initial, ⟨0, by omega⟩) :=
    Prod.ext (e.apply_symm_apply _) (Fin.ext rfl)
  have hend : ec (b, ⟨cells.length + 1, by omega⟩) =
      (none, ⟨w.length + 2, by omega⟩) := by
    apply Prod.ext (e.apply_symm_apply _)
    apply Fin.ext
    change cells.length + 1 = w.length + 2
    simp [cells]
  have hpaths := relStar_equiv_iff ec (chainStep moves cells (Sum.inl 1))
    (A.augmentedStep w) hstep (a, ⟨0, by omega⟩) (b, ⟨cells.length + 1, by omega⟩)
  rw [hstart, hend, ← A.augmented_acceptance w] at hpaths
  rw [hpaths, chainStep_recognition, chainNetwork_summary]
  have hprod : wordDiagram d (cells ++ [Sum.inl 1]) =
      Diagram.comp (Diagram.comp (d (Sum.inl 0))
        (wordDiagram (fun symbol => d (Sum.inr symbol)) w)) (d (Sum.inl 1)) := by
    simp only [wordDiagram, cells, List.cons_append, List.map_cons, List.map_append,
      List.prod_cons, List.prod_append, List.map_map, List.map_nil, List.prod_nil, mul_one]
    exact (mul_assoc _ _ _).symm
  change (a, b) ∈ (wordDiagram d (cells ++ [Sum.inl 1])).forward ↔ _
  rw [hprod]

end Complementation.Internal

end Complexity.FiniteAutomaton
