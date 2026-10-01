/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Lift
public import Complexitylib.Models.TuringMachine.Hoare.Defs

/-!
# Hoare contracts through work-tape lifting

A lifted machine keeps its source's time bound and preserves arbitrary non-marker
extra tapes exactly. These frame rules need no universal-machine or clock infrastructure.
-/

public section

namespace Complexity
namespace TM

/-- **Frame rule for `liftTM` Hoare specs** (ghost-pinned extras). If
    `tm : TM n` satisfies `{pre} tm {post} [≤ b]`, then `tm.liftTM m`
    satisfies the same triple on its first `n` work tapes while the `m`
    extra tapes — holding *arbitrary* parked content `extras` (head ≥ 1,
    reading a non-`▷` symbol) — are preserved **exactly**, with the same
    time bound. This is what lets lifted 6-tape UTM phases run while tape
    6 holds the clock. -/
theorem liftTM_hoareTime_frame {n m : ℕ} (tm : TM n) {pre post : TapePred n}
    {b : ℕ} (extras : Fin m → Tape)
    (hex : ∀ j : Fin m, 1 ≤ (extras j).head ∧ (extras j).read ≠ Γ.start)
    (h : tm.HoareTime pre post b) :
    (tm.liftTM m).HoareTime
      (fun inp work out => pre inp (fun i => work (Fin.castAdd m i)) out ∧
        ∀ j : Fin m, work (Fin.natAdd n j) = extras j)
      (fun inp work out => post inp (fun i => work (Fin.castAdd m i)) out ∧
        ∀ j : Fin m, work (Fin.natAdd n j) = extras j)
      b := by
  have hex' : ∀ j : Fin m, (extras j).read ≠ Γ.start := fun j => (hex j).2
  rintro inp work out ⟨hpre, hpark⟩
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ :=
    h inp (fun i => work (Fin.castAdd m i)) out hpre
  -- the lifted start configuration is the embedded n-tape start configuration
  have hstart :
      ({ state := (tm.liftTM m).qstart, input := inp, work := work, output := out }
        : Cfg (n + m) (tm.liftTM m).Q)
      = liftCfgWith tm m extras
          { state := tm.qstart, input := inp,
            work := fun i => work (Fin.castAdd m i), output := out } := by
    refine Cfg.ext rfl rfl (funext fun i => ?_) rfl
    by_cases hik : i.val < n
    · rw [liftCfgWith_work_lt tm m extras _ i hik]
      rfl
    · rw [liftCfgWith_work_ge tm m extras _ i (Nat.le_of_not_lt hik),
        ← hpark (extraIdx i (Nat.le_of_not_lt hik))]
      exact congrArg work (Fin.ext (show i.val = n + (i.val - n) by
        have := Nat.le_of_not_lt hik; omega))
  refine ⟨liftCfgWith tm m extras c', t, ht, ?_, ?_, ?_, ?_⟩
  · rw [hstart]
    exact reachesIn_map' (tm' := tm.liftTM m) (liftCfgWith tm m extras)
      (fun a a' ha => by rw [liftTM_step_liftCfgWith tm m hex', ha]; rfl) hreach
  · exact hhalt
  · have hwl : (fun i => (liftCfgWith tm m extras c').work (Fin.castAdd m i))
        = c'.work := by
      funext i
      rw [liftCfgWith_work_lt tm m extras c' (Fin.castAdd m i) i.isLt]
      rfl
    rw [liftCfgWith_input, liftCfgWith_output, hwl]
    exact hpost
  · intro j
    rw [liftCfgWith_work_ge tm m extras c' (Fin.natAdd n j)
      (Nat.le_add_right n j.val)]
    exact congrArg extras (Fin.ext (show n + j.val - n = j.val by omega))

/-- **`liftTM` preserves Hoare specs** (blank extras). Special case of
    `liftTM_hoareTime_frame`: the extra tapes start and end as the
    canonical parked blank tape `(Tape.init []).move Dir3.right`. -/
theorem liftTM_hoareTime {n m : ℕ} (tm : TM n) {pre post : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b) :
    (tm.liftTM m).HoareTime
      (fun inp work out => pre inp (fun i => work (Fin.castAdd m i)) out ∧
        ∀ j : Fin m, work (Fin.natAdd n j) = (Tape.init []).move Dir3.right)
      (fun inp work out => post inp (fun i => work (Fin.castAdd m i)) out ∧
        ∀ j : Fin m, work (Fin.natAdd n j) = (Tape.init []).move Dir3.right)
      b := by
  have hblank : ((Tape.init []).move Dir3.right).read ≠ Γ.start := by decide
  exact liftTM_hoareTime_frame tm (fun _ => (Tape.init []).move Dir3.right)
    (fun _ => ⟨Nat.le_refl 1, hblank⟩) h

end TM
end Complexity
