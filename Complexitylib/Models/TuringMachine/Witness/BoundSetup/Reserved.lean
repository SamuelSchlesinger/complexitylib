/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Witness.BoundSetup
public import Complexitylib.Models.TuringMachine.Lift
public import Complexitylib.Models.TuringMachine.SpaceTime.Internal.Reachability

/-!
# Fresh tapes reserved alongside bound setup

The setup uses private scratch. Separate future verifier, pair, and witness
tapes start genuinely blank at head zero and become parked blank during the
setup's first actual step. The extra tapes do not borrow the setup's private
scratch contents and do not add a running-time charge.
-/

@[expose] public section

namespace Complexity
namespace WitnessBoundSetup

/-- Setup's canonical endpoint projected to its own block, with separately
reserved tapes still blank and parked. -/
def reservedReady (x : List Bool) (bound extra : ℕ) : TapePred ((r + 1) + extra) :=
  fun inp work out => ready x bound inp (fun i => work (Fin.castAdd extra i)) out ∧
    ∀ i, r + 1 ≤ i.val → work i = (Tape.init []).move Dir3.right

/-- Every reserved-setup work tape is parked and start-invariant, including
both genuinely private setup scratch and separately reserved blank tapes. -/
theorem reservedReady_work (x : List Bool) (B extra : ℕ)
    {inp : Tape} {work : Fin ((r + 1) + extra) → Tape} {out : Tape}
    (h : reservedReady x B extra inp work out) (i : Fin ((r + 1) + extra)) :
    (work i).head = 1 ∧ (work i).StartInvariant := by
  by_cases hi : i.val < r + 1
  · let j : Fin (r + 1) := ⟨i.val, hi⟩
    have he : Fin.castAdd extra j = i := Fin.ext rfl
    rw [← he]
    exact h.1.2.2.1 j
  · rw [h.2 i (by omega)]
    exact ⟨rfl, Tape.StartInvariant.init_nil.move Dir3.right⟩

/-- A completed setup run is nonempty because it parks the initially zero
output head at cell one. This covers the initialization mismatch of `liftCfg`. -/
theorem prepares_time_pos (setup : WitnessBoundSetup r bound) (x : List Bool)
    {c : Cfg (r + 1) setup.machine.Q} {t : ℕ}
    (hr : setup.machine.reachesIn t (setup.machine.initCfg x) c)
    (hready : ready x (bound x.length) c.input c.work c.output) : 0 < t := by
  by_contra h
  have ht : t = 0 := by omega
  subst t
  have hc := TM.reachesIn_zero_iff.mp hr
  have ho := congrArg (fun d : Cfg (r + 1) setup.machine.Q => d.output.head) hc
  rw [hready.2.2.2] at ho
  change 0 = 1 at ho
  omega

/-- An actual initialized setup run reserves fresh tapes without extra steps. -/
theorem prepares_reserved (setup : WitnessBoundSetup r bound) (extra : ℕ) (x : List Bool) :
    (setup.machine.liftTM extra).HoareTime (fresh x)
      (reservedReady x (bound x.length) extra) (setup.time x.length) := by
  intro inp work out hp
  rcases hp with ⟨rfl, rfl, rfl⟩
  obtain ⟨c, t, ht, hr, hh, hp⟩ := setup.prepares x
    (Tape.init (x.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init []) ⟨rfl, rfl, rfl⟩
  have htpos := prepares_time_pos setup x hr hp
  refine ⟨setup.machine.liftCfg extra c, t, ht,
    TM.liftTM_reachesIn_initCfg_of_pos setup.machine extra x htpos hr, hh, ?_, ?_⟩
  · have hw : (fun i : Fin (r + 1) =>
        (setup.machine.liftCfg extra c).work (Fin.castAdd extra i)) = c.work := by
      funext i
      exact TM.liftCfg_work_lt setup.machine extra c _ i.isLt
    change ready x (bound x.length) c.input _ c.output
    rw [hw]
    exact hp
  · intro i hi
    exact TM.liftCfg_work_ge setup.machine extra c i hi

/-- Reserving blank tapes costs at most the parked cell, independently of time. -/
theorem safety_reserved (setup : WitnessBoundSetup r bound) (extra : ℕ) (x : List Bool) :
    (setup.machine.liftTM extra).HoareSafety (fresh x)
      (fun inp work out =>
        (⟨(), inp, work, out⟩ : Cfg ((r + 1) + extra) Unit).WithinDecisionSpace
          x.length (max (setup.space x.length) 1)) := by
  intro inp work out hp C hC
  rcases hp with ⟨rfl, rfl, rfl⟩
  obtain ⟨c, haltTime, htime, hr, hh, hp⟩ := setup.prepares x
    (Tape.init (x.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init []) ⟨rfl, rfl, rfl⟩
  have htpos := prepares_time_pos setup x hr hp
  have hfull := TM.liftTM_reachesIn_initCfg_of_pos setup.machine extra x htpos hr
  obtain ⟨t, ht⟩ := (setup.machine.liftTM extra).reaches_to_reachesIn hC
  have hle : t ≤ haltTime := (setup.machine.liftTM extra).reachesIn_le_halt ht hfull hh
  by_cases hz : t = 0
  · subst t
    have hc := TM.reachesIn_zero_iff.mp ht
    subst C
    exact ⟨⟨fun _ => Nat.zero_le _, Nat.zero_le _⟩, Nat.zero_le _⟩
  · obtain ⟨d, hd, _⟩ := TM.reachesIn_prefix_internal hr hle
    have hd' := TM.liftTM_reachesIn_initCfg_of_pos setup.machine extra x (by omega) hd
    have heq := (setup.machine.liftTM extra).reachesIn_right_unique ht hd'
    subst C
    have hs := setup.withinSpace x _ _ _ ⟨rfl, rfl, rfl⟩ d
      (TM.reaches_of_reachesIn hd)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      by_cases hi : i.val < r + 1
      · have he := TM.liftCfg_work_lt setup.machine extra d i hi
        change ((setup.machine.liftCfg extra d).work i).head ≤ _
        rw [he]
        exact (hs.1.1 ⟨i.val, hi⟩).trans (le_max_left _ _)
      · have he := TM.liftCfg_work_ge setup.machine extra d i (by omega)
        change ((setup.machine.liftCfg extra d).work i).head ≤ _
        rw [he]
        exact le_max_right _ _
    · have h := hs.1.2
      change d.input.head ≤ _
      dsimp only at h
      omega
    · have h := hs.2
      change d.output.head ≤ _
      dsimp only at h
      omega

end WitnessBoundSetup
end Complexity
