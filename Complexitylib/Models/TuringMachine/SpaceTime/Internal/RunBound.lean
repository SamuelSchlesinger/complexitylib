/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.SpaceTime.Internal.Reachability
public import Complexitylib.Models.TuringMachine.SpaceTime.Internal.Snapshot

/-!
# Finite-configuration run bounds — proof internals

A halting deterministic transducer run cannot repeat a reduced snapshot. If it
did, finite snapshot determinism would reproduce the final halt state at an
earlier time. The run's time indices therefore inject into the finite snapshot
type.
-/

@[expose] public section

namespace Complexity

namespace TM

variable {k : ℕ} {tm : TM k}

/-- The time indices of a halting transducer run staying within auxiliary
space `space` inject into the reduced transducer snapshots. -/
theorem IsTransducer.reachesIn_succ_le_transducerConfigBound_internal
    (htrans : tm.IsTransducer) {x : List Bool} {space t : ℕ}
    {c : Cfg k tm.Q}
    (hreach : tm.reachesIn t (tm.initCfg x) c)
    (hhalt : tm.halted c)
    (hspace : ∀ d, tm.reaches (tm.initCfg x) d →
      d.WithinAuxSpace x.length space) :
    t + 1 ≤ tm.transducerConfigBound x.length space := by
  classical
  have hexists : ∀ i : Fin (t + 1), ∃ d,
      tm.reachesIn i.val (tm.initCfg x) d ∧
      tm.reachesIn (t - i.val) d c := by
    intro i
    exact reachesIn_prefix_internal hreach (by omega)
  let cfgAt : Fin (t + 1) → Cfg k tm.Q := fun i => Classical.choose (hexists i)
  have hcfgAt (i : Fin (t + 1)) :
      tm.reachesIn i.val (tm.initCfg x) (cfgAt i) ∧
      tm.reachesIn (t - i.val) (cfgAt i) c :=
    Classical.choose_spec (hexists i)
  have hspaceAt (i : Fin (t + 1)) :
      (cfgAt i).WithinAuxSpace x.length space :=
    hspace (cfgAt i) (reaches_of_reachesIn (hcfgAt i).1)
  let encode : Fin (t + 1) → tm.TransducerSnapshot x.length space :=
    fun i => tm.transducerSnapshot (cfgAt i) x.length space (hspaceAt i)
  have hnoRepeat (i j : Fin (t + 1)) (hij : i.val < j.val) :
      encode i ≠ encode j := by
    intro hsnap
    let u := t - j.val
    have hu : u ≤ t - i.val := by
      dsimp only [u]
      omega
    obtain ⟨early, hrunEarly, _⟩ :=
      reachesIn_prefix_internal (hcfgAt i).2 hu
    have hrunFinal : tm.reachesIn u (cfgAt j) c := by
      simpa [u] using (hcfgAt j).2
    have hspaceFromI : ∀ {v : ℕ} {d : Cfg k tm.Q},
        tm.reachesIn v (cfgAt i) d → d.WithinAuxSpace x.length space := by
      intro v d hrun
      exact hspace d (reaches_of_reachesIn
        (reachesIn_trans tm (hcfgAt i).1 hrun))
    have hspaceFromJ : ∀ {v : ℕ} {d : Cfg k tm.Q},
        tm.reachesIn v (cfgAt j) d → d.WithinAuxSpace x.length space := by
      intro v d hrun
      exact hspace d (reaches_of_reachesIn
        (reachesIn_trans tm (hcfgAt j).1 hrun))
    have hinput : (cfgAt i).input.cells = (cfgAt j).input.cells := by
      rw [input_cells_eq_of_reachesIn (hcfgAt i).1,
        input_cells_eq_of_reachesIn (hcfgAt j).1]
    have hblankI : (cfgAt i).output.BlankAfterHead :=
      htrans.initCfg_output_blankAfterHead_reachesIn (hcfgAt i).1
    have hblankJ : (cfgAt j).output.BlankAfterHead :=
      htrans.initCfg_output_blankAfterHead_reachesIn (hcfgAt j).1
    have hsnapStart :
        tm.transducerSnapshot (cfgAt i) x.length space (hspaceFromI .zero) =
          tm.transducerSnapshot (cfgAt j) x.length space (hspaceFromJ .zero) := by
      simpa [encode] using hsnap
    have hsnapEnd := transducerSnapshot_reachesIn_congr htrans
      hrunEarly hrunFinal hspaceFromI hspaceFromJ hinput hblankI hblankJ hsnapStart
    have hstate : early.state = c.state :=
      state_eq_of_transducerSnapshot_eq
        (hspaceFromI hrunEarly) (hspaceFromJ hrunFinal) hsnapEnd
    have hhaltEarly : tm.halted early := hstate.trans hhalt
    have hreachEarly : tm.reachesIn (i.val + u) (tm.initCfg x) early :=
      reachesIn_trans tm (hcfgAt i).1 hrunEarly
    have hle := tm.reachesIn_le_halt hreach hreachEarly hhaltEarly
    dsimp only [u] at hle
    omega
  have hinjective : Function.Injective encode := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hnoRepeat i j hlt hij
    · exact hnoRepeat j i hgt hij.symm
  have hcard := Fintype.card_le_of_injective encode hinjective
  simpa only [Fintype.card_fin, card_transducerSnapshot] using hcard

/-- A total space-bounded transducer computes within its finite reduced-
configuration bound. -/
theorem ComputesInSpace.computesInTime_configBound_internal
    {f : List Bool → List Bool} {S : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f S) :
    tm.ComputesInTime f
      (fun n => tm.transducerConfigBound n (S n)) := by
  intro x
  obtain ⟨c, hreach, hhalt, hout⟩ := hcomp.2.2 x
  obtain ⟨t, hreachIn⟩ := tm.reaches_to_reachesIn hreach
  refine ⟨c, t, ?_, hreachIn, hhalt, hout⟩
  have := hcomp.1.reachesIn_succ_le_transducerConfigBound_internal
    hreachIn hhalt (fun d hd => hcomp.2.1 x d hd)
  exact (Nat.le_succ t).trans this

/-- A total space-bounded language decider that also has one-way output decides
within its finite reduced-configuration bound. -/
theorem DecidesInSpace.decidesInTime_configBound_internal
    {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (htrans : tm.IsTransducer) :
    tm.DecidesInTime L
      (fun n => tm.transducerConfigBound n (S n)) := by
  intro x
  obtain ⟨c, hreach, hhalt, hyes, hno⟩ := hdec.2 x
  obtain ⟨t, hreachIn⟩ := tm.reaches_to_reachesIn hreach
  refine ⟨c, t, ?_, hreachIn, hhalt, hyes, hno⟩
  have := htrans.reachesIn_succ_le_transducerConfigBound_internal
    hreachIn hhalt (fun d hd => (hdec.1 x d hd).1)
  exact (Nat.le_succ t).trans this

end TM

end Complexity
