/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Wiring

/-!
# Direction in the wiring graph

The wiring graph is undirected for the layout lemma, but every edge runs from
the vertex producing its signal (`fst`) to the vertex consuming it (`snd`).
Relative to a vertex set `L`, an edge is *backward-crossing* when it is
produced outside `L` and consumed inside, and *forward-crossing* in the
opposite case.

The determination lemma `trace_eq_of_agree_backward` says that the values of
all signals with an edge touching `L` are determined by the inputs read in
`L` together with the bits on the backward-crossing edges: two evaluations
that agree on those agree on every such signal. Applied to the complement of
`L`, the inputs read outside `L` and the forward-crossing bits determine
every signal with an edge touching the outside. These are the two facts the
average-case bound needs beyond the cut-counting lemma.
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth
namespace Wiring

open scoped Classical

variable {n s : Nat} (p : Program Binary.signature n s) (out : Fin s)

/-- If no edge of a signal is backward-crossing and its signal vertex lies
outside `L`, then none of its copy vertices lies in `L`. -/
theorem copy_not_mem_of_no_backward {L : Finset (Vertex p out)} {w : Signal p out}
    (hA : ∀ e, signal p out e = w → fst p out e ∉ L → snd p out e ∈ L → False)
    (hw : (.inl w : Vertex p out) ∉ L) :
    ∀ k (hk : k < fanout p out w - 1), (.inr ⟨w, ⟨k, hk⟩⟩ : Vertex p out) ∉ L := by
  intro k
  induction k with
  | zero =>
    intro hk hmem
    refine hA (.inr ⟨w, ⟨0, hk⟩⟩) rfl ?_ ?_
    · rw [fst_inr_zero]
      exact hw
    · rw [snd_inr]
      exact hmem
  | succ k ih =>
    intro hk hmem
    refine hA (.inr ⟨w, ⟨k + 1, hk⟩⟩) rfl ?_ ?_
    · rw [fst_inr_succ]
      exact ih _
    · rw [snd_inr]
      exact hmem

/-- **Determination.** Two evaluations agreeing on the inputs read in `L` and on
the backward-crossing edges of `L` agree on every signal with an edge
touching `L`. -/
theorem trace_eq_of_agree_backward {L : Finset (Vertex p out)} {x x' : Fin n → Bool}
    (hpast : ∀ j ∈ (network p out).past L, x j = x' j)
    (hback : ∀ e, fst p out e ∉ L → snd p out e ∈ L →
      traceAssignment p out x e = traceAssignment p out x' e) :
    ∀ (w : Signal p out) (e : Edge p out), signal p out e = w →
      (fst p out e ∈ L ∨ snd p out e ∈ L) →
      p.trace Binary.interpretation x w.1 = p.trace Binary.interpretation x' w.1 := by
  suffices key : ∀ m, ∀ w : Signal p out, w.1.index.val = m → ∀ e, signal p out e = w →
      (fst p out e ∈ L ∨ snd p out e ∈ L) →
      p.trace Binary.interpretation x w.1 = p.trace Binary.interpretation x' w.1 from
    fun w e he ht => key _ w rfl e he ht
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro w hm e he ht
  by_cases hA : ∃ e', signal p out e' = w ∧ fst p out e' ∉ L ∧ snd p out e' ∈ L
  · obtain ⟨e', he', hf, hs⟩ := hA
    have := hback e' hf hs
    unfold traceAssignment at this
    rwa [he'] at this
  · have hA' : ∀ e', signal p out e' = w → fst p out e' ∉ L → snd p out e' ∈ L → False :=
      fun e' h₁ h₂ h₃ => hA ⟨e', h₁, h₂, h₃⟩
    -- The signal vertex lies in `L`: otherwise the touching edge is backward-crossing.
    have hwL : (.inl w : Vertex p out) ∈ L := by
      by_contra hw
      have hcopy := copy_not_mem_of_no_backward p out hA' hw
      have hfst : fst p out e ∉ L := by
        rcases h : fst p out e with w' | ⟨w', k⟩
        · have hw' := signal_eq_of_fst_eq_inl p out h
          rw [he] at hw'
          rw [← hw']
          exact hw
        · have hw' := signal_eq_of_fst_eq_inr p out h
          rw [he] at hw'
          subst hw'
          exact hcopy k.val k.isLt
      rcases ht with h | h
      · exact hfst h
      · exact hA' e he hfst h
    -- Compute the value at the signal vertex.
    obtain ⟨w, hw⟩ := w
    revert hm hwL
    cases w with
    | input j =>
      intro hm hwL
      have hj : j ∈ (network p out).past L := by
        rw [Network.mem_past]
        refine ⟨(mem_read p out).mpr hw, ?_⟩
        show portVertex p out j ∈ L
        rw [portVertex_of_reach p out hw]
        exact hwL
      simp only [Program.trace_input]
      exact hpast j hj
    | gate g =>
      intro hm hwL
      simp only [Program.trace_gateWire, Program.gateFunction_apply]
      rw [eval_eq_op, eval_eq_op]
      have slot (a : Fin 2) : p.trace Binary.interpretation x ((p.lines g).wires a) =
          p.trace Binary.interpretation x' ((p.lines g).wires a) := by
        refine ih _ ?_ (slotSignal p out ⟨(g, a), hw⟩) rfl (.inl ⟨(g, a), hw⟩) rfl (Or.inr ?_)
        · rw [← hm]
          exact lines_wires_lt p g a
        · rw [snd_inl]
          exact hwL
      rw [slot 0, slot 1]

/-- The past of the complement of `L` consists of the read variables outside the past of `L`. -/
theorem mem_past_compl {L : Finset (Vertex p out)} {j : Fin n} :
    j ∈ (network p out).past Lᶜ ↔ j ∈ (network p out).read ∧ j ∉ (network p out).past L := by
  rw [Network.mem_past, Network.mem_past]
  simp only [Finset.mem_compl]
  tauto

end Wiring

end Cutwidth
end Algebraic
