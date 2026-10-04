/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Graph.Internal.Insert
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Graph.Internal.Constants

/-!
# Edge-insertion assembly of local conditional weights

The induction uses the exact number of new endpoints. An edge with no new endpoint
uses two earlier incident edges, an edge with one new endpoint uses one, and an
edge with two new endpoints uses its unconditional weight.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph

open scoped Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

/-- Local zero-, one-, and two-parent kernels assemble into a joint edge-message weight. -/
theorem exists_weightBound_tuple_of_local
    (seed : ∀ e : SignedEdge V, WeightBound e.eval (Real.binEntropy (1 / 4)))
    (one : ∀ e f : SignedEdge V,
      e.left = f.left ∨ e.left = f.right ∨ e.right = f.left ∨ e.right = f.right →
      ConditionalWeightBound e.eval f.eval (3 / 4 * Real.log 2))
    (two : ∀ e f g : SignedEdge V,
      (e.left = f.left ∨ e.left = f.right) →
      (e.right = g.left ∨ e.right = g.right) →
      ConditionalWeightBound e.eval (fun x => (f.eval x, g.eval x)) edgeCost)
    (edge : E → SignedEdge V) (selected : Finset E) :
    Nonempty (WeightBound (tuple edge selected)
      (selected.card * edgeCost +
        (support (fun e => (edge e).left) (fun e => (edge e).right) selected).card *
          vertexCost)) := by
  induction selected using Finset.induction_on with
  | empty =>
    simpa using (⟨WeightBound.subsingleton (tuple edge ∅)⟩ :
      Nonempty (WeightBound (tuple edge ∅) 0))
  | @insert e selected fresh ih =>
    obtain ⟨previous⟩ := ih
    let left (i : E) := (edge i).left
    let right (i : E) := (edge i).right
    have extension : ∃ d : ℕ,
        (support left right (insert e selected)).card =
          (support left right selected).card + d ∧
        Nonempty (ConditionalWeightBound (edge e).eval (tuple edge selected)
          (edgeCost + d * vertexCost)) := by
      by_cases hl : left e ∈ support left right selected
      · obtain ⟨f, hf, hlf⟩ := (mem_support left right selected (left e)).mp hl
        by_cases hr : right e ∈ support left right selected
        · obtain ⟨g, hg, hrg⟩ := (mem_support left right selected (right e)).mp hr
          let readout (m : selected → Bool) := (m ⟨f, hf⟩, m ⟨g, hg⟩)
          have bound := ConditionalWeightBound.pullParent readout (tuple edge selected)
            (fun _ => rfl) (two (edge e) (edge f) (edge g) hlf hrg)
          refine ⟨0, ?_, ?_⟩
          · simpa using card_support_insert_of_mem_mem left right selected e hl hr
          · simpa using (⟨bound⟩ : Nonempty _)
        · let readout (m : selected → Bool) := m ⟨f, hf⟩
          have overlap : (edge e).left = (edge f).left ∨
              (edge e).left = (edge f).right ∨ (edge e).right = (edge f).left ∨
              (edge e).right = (edge f).right := by tauto
          have bound := ConditionalWeightBound.pullParent readout (tuple edge selected)
            (fun _ => rfl) (one (edge e) (edge f) overlap)
          refine ⟨1, card_support_insert_of_mem_notMem left right selected e hl hr,
            ⟨bound.mono ?_⟩⟩
          unfold edgeCost vertexCost
          norm_num
          ring_nf
          rfl
      · by_cases hr : right e ∈ support left right selected
        · obtain ⟨f, hf, hrf⟩ := (mem_support left right selected (right e)).mp hr
          let readout (m : selected → Bool) := m ⟨f, hf⟩
          have overlap : (edge e).left = (edge f).left ∨
              (edge e).left = (edge f).right ∨ (edge e).right = (edge f).left ∨
              (edge e).right = (edge f).right := by tauto
          have bound := ConditionalWeightBound.pullParent readout (tuple edge selected)
            (fun _ => rfl) (one (edge e) (edge f) overlap)
          refine ⟨1, card_support_insert_of_notMem_mem left right selected e hl hr,
            ⟨bound.mono ?_⟩⟩
          unfold edgeCost vertexCost
          norm_num
          ring_nf
          rfl
        · have bound := (seed (edge e)).toConditional (tuple edge selected)
          refine ⟨2, card_support_insert_of_notMem_notMem left right selected e
            (edge e).distinct hl hr, ⟨bound.mono ?_⟩⟩
          unfold edgeCost vertexCost
          norm_num
          ring_nf
          rfl
    obtain ⟨d, cardinality, ⟨next⟩⟩ := extension
    refine ⟨(insertWeight edge selected e fresh previous next).mono ?_⟩
    change (selected.card : ℝ) * edgeCost + (support left right selected).card *
      vertexCost + (edgeCost + d * vertexCost) ≤
      (insert e selected).card * edgeCost + (support left right (insert e selected)).card *
        vertexCost
    rw [Finset.card_insert_of_notMem fresh, cardinality]
    push_cast
    ring_nf
    rfl

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph
