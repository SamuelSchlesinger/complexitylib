/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Dependency.Defs
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Circuit dependency graphs -- proof internals
-/

@[expose] public section

namespace Complexity

namespace Circuit

variable {B : Basis} {N M G : ℕ} [NeZero N] [NeZero M]

private theorem dependencyEdge_val_lt
    (c : Circuit B N M G) (occurrence : DependencyOccurrence c) :
    (c.dependencyEdge occurrence).1.val <
      (c.dependencyEdge occurrence).2.val := by
  cases occurrence with
  | inl occurrence =>
      rcases occurrence with ⟨i, input⟩
      exact c.acyclic i input
  | inr occurrence =>
      rcases occurrence with ⟨j, input⟩
      have hsource := ((c.outputs j).inputs input).isLt
      simp only [dependencyEdge]
      omega

theorem dependencyGraph_adj_val_lt_internal
    (c : Circuit B N M G)
    {source target : Fin (N + G + M)}
    (edge : c.dependencyGraph.Adj source target) :
    source.val < target.val := by
  change (source, target) ∈ c.dependencyEdges at edge
  simp only [dependencyEdges, Finset.mem_image, Finset.mem_univ,
    true_and] at edge
  obtain ⟨occurrence, hedge⟩ := edge
  have hsource : (c.dependencyEdge occurrence).1 = source :=
    congrArg Prod.fst hedge
  have htarget : (c.dependencyEdge occurrence).2 = target :=
    congrArg Prod.snd hedge
  rw [← hsource, ← htarget]
  exact dependencyEdge_val_lt c occurrence

private theorem walk_val_add_le
    (c : Circuit B N M G) {m : ℕ}
    {path : Fin m → Fin (N + G + M)}
    (walk : c.dependencyGraph.IsDirectedWalk path) :
    ∀ k a (ha : a < m) (hak : a + k < m),
      (path ⟨a, ha⟩).val + k ≤ (path ⟨a + k, hak⟩).val := by
  intro k
  induction k with
  | zero =>
      intro a _ _
      rfl
  | succ k ih =>
      intro a ha hak
      have hak' : a + k < m := by omega
      have hih := ih a ha hak'
      have hedge := walk ⟨a + k, hak'⟩ hak
      change c.dependencyGraph.Adj
        (path ⟨a + k, hak'⟩) (path ⟨a + k + 1, hak⟩) at hedge
      have hlt := dependencyGraph_adj_val_lt_internal c hedge
      show (path ⟨a, ha⟩).val + (k + 1) ≤
        (path ⟨a + k + 1, hak⟩).val
      omega

private theorem walk_val_strictMono
    (c : Circuit B N M G) {m : ℕ}
    {path : Fin m → Fin (N + G + M)}
    (walk : c.dependencyGraph.IsDirectedWalk path) :
    StrictMono (fun i : Fin m => (path i).val) := by
  intro i j hij
  have hile : i.val < j.val := hij
  have hj : i.val + (j.val - i.val) < m := by
    have : i.val + (j.val - i.val) = j.val := by omega
    rw [this]
    exact j.isLt
  have key :=
    walk_val_add_le c walk (j.val - i.val) i.val i.isLt hj
  have hi : (⟨i.val, i.isLt⟩ : Fin m) = i := rfl
  have heq :
      (⟨i.val + (j.val - i.val), hj⟩ : Fin m) = j := by
    apply Fin.ext
    show i.val + (j.val - i.val) = j.val
    omega
  rw [hi, heq] at key
  change (path i).val < (path j).val
  have hpos : 0 < j.val - i.val := by omega
  omega

theorem dependencyGraph_isAcyclic_internal
    (c : Circuit B N M G) :
    c.dependencyGraph.IsAcyclic := by
  refine ⟨N + G + M, ?_⟩
  rintro m ⟨path, walk⟩
  have hinjective : Function.Injective path := by
    intro i j hij
    exact (walk_val_strictMono c walk).injective
      (congrArg Fin.val hij)
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective path hinjective

theorem dependencyGraph_edgeFinset_internal
    (c : Circuit B N M G) :
    c.dependencyGraph.edgeFinset = c.dependencyEdges := by
  ext edge
  simp [Digraph.edgeFinset, dependencyGraph]

theorem dependencyGraph_edge_card_le_totalFanIn_internal
    (c : Circuit B N M G) :
    c.dependencyGraph.edgeFinset.card ≤ c.totalFanIn := by
  rw [dependencyGraph_edgeFinset_internal]
  calc
    c.dependencyEdges.card ≤ Fintype.card (DependencyOccurrence c) := by
      simpa [dependencyEdges] using
        (Finset.card_image_le :
          (Finset.univ.image c.dependencyEdge).card ≤
            (Finset.univ : Finset (DependencyOccurrence c)).card)
    _ = c.totalFanIn := by
      simp [DependencyOccurrence, totalFanIn]

end Circuit

end Complexity
