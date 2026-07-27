/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.UTM.Internal.BodyIteration

/-!
# `TerminatedRegion` for encoded descriptions

The body machine's per-iteration theorem carries the side condition
`TerminatedRegion α`, ruling out the one machine/decoder divergence: an
entry region starting with an empty segment followed by junk. This file
discharges that condition for the inputs the universal machine actually
runs on: canonical encodings `encodeDesc d` of well-formed descriptions
with a nonempty table, with arbitrary trailing junk.

The proof redoes the field decomposition of `decodeDesc_encodeDesc_append`:
after two `takeField`s the region is the encoded entry table, which starts
with the (nonempty, blank-free) symbols of the first entry — never with a
separator `□`. Extracted tables are nonempty (`descOfTM_entries_ne_nil`),
since every machine has at least its start state.
-/

@[expose] public section

namespace Complexity

namespace TM.UTMBody

/-- **Encoded descriptions have terminated entry regions**: the entry
    region of `encodeDesc d ++ junk` starts with the first table entry's
    symbols — nonempty and blank-free — so the `TerminatedRegion` premise
    (a region starting with `□`) never fires. -/
theorem terminatedRegion_encodeDesc {d : TMDesc} (_hd : d.WF)
    (hne : d.entries ≠ []) (junk : List Bool) :
    TerminatedRegion (encodeDesc d ++ junk) := by
  have hgroup : groupPairs (encodeDesc d ++ junk) = d.syms ++ groupPairs junk := by
    rw [encodeDesc, groupPairs_append_of_even (flatMap_encode_length_even _),
        groupPairs_flatMap_encode]
  have hassoc : d.syms ++ groupPairs junk
      = bitsToSyms (Nat.toBits d.w d.qstart) ++ Γw.blank ::
          (bitsToSyms (Nat.toBits d.w d.qhalt) ++ Γw.blank ::
            ((d.entries.flatMap fun e => e.syms d.w ++ [Γw.blank]) ++
              Γw.blank :: groupPairs junk)) := by
    simp [TMDesc.syms, List.append_assoc]
  have hregion : (takeField (takeField (groupPairs (encodeDesc d ++ junk))).2).2
      = (d.entries.flatMap fun e => e.syms d.w ++ [Γw.blank]) ++
          Γw.blank :: groupPairs junk := by
    rw [hgroup, hassoc, takeField_append (fun t ht => bitsToSyms_ne_blank ht)]
    dsimp only
    rw [takeField_append (fun t ht => bitsToSyms_ne_blank ht)]
  intro s rest hR
  rw [hregion] at hR
  obtain ⟨e₀, es, hE⟩ : ∃ e₀ es, d.entries = e₀ :: es := by
    cases hE : d.entries with
    | nil => exact absurd hE hne
    | cons a t => exact ⟨a, t, rfl⟩
  obtain ⟨s₀, tail, hsyms⟩ : ∃ s₀ tail, e₀.syms d.w = s₀ :: tail := by
    cases h : e₀.syms d.w with
    | nil =>
      have hlen := e₀.syms_length d.w
      rw [h] at hlen
      simp at hlen
    | cons a t => exact ⟨a, t, rfl⟩
  have hs₀ : s₀ ≠ Γw.blank :=
    DescEntry.syms_ne_blank (hsyms ▸ List.mem_cons_self ..)
  rw [hE] at hR
  simp only [List.flatMap_cons, hsyms, List.cons_append, List.append_assoc] at hR
  injection hR with h₁ _
  exact absurd h₁ hs₀

/-- `terminatedRegion_encodeDesc` for the bare encoding (no junk). -/
theorem terminatedRegion_encodeDesc_plain {d : TMDesc} (hd : d.WF)
    (hne : d.entries ≠ []) : TerminatedRegion (encodeDesc d) := by
  simpa using terminatedRegion_encodeDesc hd hne []

/-- Extracted tables are nonempty: every machine has at least its start
    state, and the dense table lists a row for each state/symbols key. -/
theorem descOfTM_entries_ne_nil (M : TM 1) : (TM.descOfTM M).entries ≠ [] := by
  have hpos : 0 < Fintype.card M.Q := Fintype.card_pos_iff.mpr ⟨M.qstart⟩
  have hmem : M.descEntry ⟨0, hpos⟩ Γ.zero Γ.zero Γ.zero ∈ (M.descOfTM).entries := by
    simp only [TM.descOfTM, List.mem_flatMap, List.mem_map]
    exact ⟨⟨0, hpos⟩, List.mem_finRange _, Γ.zero, mem_allΓ _, Γ.zero,
      mem_allΓ _, ⟨Γ.zero, mem_allΓ _, rfl⟩⟩
  exact List.ne_nil_of_mem hmem

end TM.UTMBody

end Complexity
