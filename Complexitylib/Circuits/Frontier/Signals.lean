/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Compiler
public import Complexitylib.Circuits.Frontier.Boundary.Hypergraph

/-!
# Frontiers measured by distinct circuit signals

The compiler labels every edge by the wire it carries. Exactness makes all edges with the
same label equal on every accepting run. `ncard_accepted_le_signals` therefore charges only
the distinct signals on the union of adjacent frontiers, together with the input read at the
step. This is a capacity theorem, not a new universal layout bound.
-/

@[expose] public section

namespace Complexity.Frontier.Compiler

open Cslib.Circuits Set

variable {σ : Signature} {n s : ℕ} {O U : Type*} [Finite O] [Finite U] [Nonempty U]
  {p : Program σ n s} {out : O → Wire n s} (I : Interpretation σ U) (Acc : O → Set U)

omit [Finite U] [Nonempty U] in
/-- All occurrences of a signal are joined by edges carrying that same signal. -/
theorem signal_junction_path (w : Signal p out) :
    ∀ k (hk : k < fanout p out w),
      Relation.ReflTransGen ((network p out I Acc).toMultigraph.labelGraph Edge.signal w).Adj
        (.junction ⟨w, ⟨k, hk⟩⟩) (.signal w)
  | 0, _ => .single ⟨⟨.feed ⟨w, ⟨0, _⟩⟩, rfl⟩,
      Or.inr ⟨by simp [Multigraph.labelGraph, network, src, feeder], rfl⟩⟩
  | k + 1, hk => .head ⟨⟨.feed ⟨w, ⟨k + 1, hk⟩⟩, rfl⟩,
      Or.inr ⟨by simp [Multigraph.labelGraph, network, src, feeder], rfl⟩⟩
      (signal_junction_path w k (by lia))

omit [Finite U] [Nonempty U] in
theorem signal_occurrence_path (w : Signal p out) (v : Vertex p out)
    (hv : v ∈ (network p out I Acc).toMultigraph.signalHypergraph Edge.signal w) :
    Relation.ReflTransGen ((network p out I Acc).toMultigraph.labelGraph Edge.signal w).Adj
      v (.signal w) := by
  obtain ⟨e, rfl, he⟩ := hv
  cases e with
  | feed j =>
    have hj := signal_junction_path I Acc j.1 j.2.val j.2.isLt
    rcases he with rfl | rfl
    · exact .head ⟨⟨.feed j, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩ hj
    · exact hj
  | deliver j =>
    have hj := signal_junction_path I Acc j.1 j.2.val j.2.isLt
    rcases he with rfl | rfl
    · exact hj
    · exact .head ⟨⟨.deliver j, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩ hj

omit [Finite U] [Nonempty U] in
/-- The junction compiler realizes exactly the native signal-hypergraph separator. -/
theorem signalCut_eq_hypergraph_cut (X : Set (Vertex p out)) :
    Edge.signal '' (network p out I Acc).cut X =
      ((network p out I Acc).toMultigraph.signalHypergraph Edge.signal).cut X := by
  apply Multigraph.image_cut_eq_hypergraph_cut
  intro w u hu v hv
  exact (signal_occurrence_path I Acc w u hu).trans
    (Multigraph.reflTransGen_adj_symm (signal_occurrence_path I Acc w v hv))

omit [Finite U] [Nonempty U] in
/-- Distinct-signal capacity is a symmetric submodular separator function. -/
theorem signalCut_submodular (X Y : Set (Vertex p out)) :
    (Edge.signal '' (network p out I Acc).cut (X ∩ Y)).ncard +
      (Edge.signal '' (network p out I Acc).cut (X ∪ Y)).ncard ≤
        (Edge.signal '' (network p out I Acc).cut X).ncard +
          (Edge.signal '' (network p out I Acc).cut Y).ncard := by
  simp only [signalCut_eq_hypergraph_cut]
  exact Hypergraph.ncard_cut_submodular _ _ _

/-- The signal labels on a frontier. Repeated edges of the same wire are charged once. -/
noncomputable def signalFrontier (π : Layout (Vertex p out)) (t : ℕ) : Set (Signal p out) :=
  Edge.signal '' (network p out I Acc).frontier π t

omit [Finite U] [Nonempty U] in
/-- Signal capacity never exceeds edge capacity. -/
theorem ncard_signalFrontier_le (π : Layout (Vertex p out)) (t : ℕ) :
    (signalFrontier I Acc π t).ncard ≤ ((network p out I Acc).frontier π t).ncard :=
  ncard_image_le (toFinite _)

/-- **Counting with signal capacity.** The step budget charges distinct signals across both
frontiers and the inputs read at the vertex. It can be strictly smaller than the edge budget. -/
theorem ncard_accepted_le_signals (π : Layout (Vertex p out)) {K b : ℕ}
    (hfree : RectangleFree (network p out I Acc).accepted K)
    (hK : K ≤ (network p out I Acc).accepted.ncard)
    (hb : ∀ t, ∀ ht : t < Nat.card (Vertex p out),
      (signalFrontier I Acc π t ∪ signalFrontier I Acc π (t + 1)).ncard +
        ((network p out I Acc).readAt (π.symm ⟨t, ht⟩)).ncard ≤ b) :
    (network p out I Acc).accepted.ncard ≤ (K - 1) ^ 2 *
      (Nat.card (Vertex p out) * Nat.card U ^ b +
        Nat.card U ^ (network p out I Acc).readᶜ.ncard) := by
  apply (network p out I Acc).ncard_accepted_le_labels π Edge.signal
    (fun x w => p.trace I x w.1)
    (fun _ hx e => eq_trace ((network p out I Acc).satisfies_witness hx) e) hfree hK
  simpa only [image_union, signalFrontier] using hb

end Complexity.Frontier.Compiler
