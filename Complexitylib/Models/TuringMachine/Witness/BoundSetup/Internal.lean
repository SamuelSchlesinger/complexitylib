/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Witness.BoundSetup.Defs
public import Complexitylib.Models.TuringMachine.Registers.InputLen

/-!
# Linear witness-bound setup: proof internals

The concrete setup initializes the heads, records the input length in unary,
and increments that counter. Its explicit time also gives a conservative
all-prefix decision-space bound; no setup resource is treated as free.
-/

@[expose] public section

namespace Complexity
namespace WitnessBoundSetup

/-- A unary register respects the unique left-end-marker invariant. -/
private theorem regTape_startInvariant (v : ℕ) : (TM.regTape v).StartInvariant := by
  refine ⟨rfl, ?_⟩
  intro j hj
  exact TM.regCells_ne_start (by omega)

/-- The concrete linear setup has a canonical endpoint and explicit linear time. -/
theorem linearMachine_prepares_internal (x : List Bool) :
    linearMachine.HoareTime (fresh x) (ready x (x.length + 1))
      (4 * x.length + 11) := by
  let inp := (Tape.init (x.map Γ.ofBool)).move Dir3.right
  let zero : Fin 1 → Tape := fun _ => TM.regTape 0
  let len := Function.update zero 0 (TM.regTape x.length)
  have hp : TM.Parked inp := TM.parked_init_input x
  have hz : ∀ i, TM.Parked (zero i) := fun _ => TM.parked_regTape 0
  have hl : ∀ i, TM.Parked (len i) := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa [len] using TM.parked_regTape x.length
  have hstart : TM.bumpTM.HoareTime (fresh x) (TM.EmitPred inp zero []) 1 := by
    refine (TM.bumpTM_hoareTime x).consequence ?_ ?_ le_rfl
    · rintro i w o ⟨hi, hw, ho⟩
      exact ⟨hi, fun j => congrFun hw j, ho⟩
    · rintro i w o ⟨hi, hw, ho⟩
      exact ⟨hi, funext fun j => (hw j).eq_regT, ho⟩
  have hlen := TM.inputLenRegTM_hoareTime (0 : Fin 1) x zero []
    (fun i _ => hz i) rfl
  have hinc := TM.incRegTM_hoareTime (0 : Fin 1) x.length inp len [] hp
    (fun i _ => hl i) (by simp [len])
  have htail := TM.seqTM_hoareTime _ _ hlen (TM.emitPred_transition hp hl []) hinc
  have hfull := TM.seqTM_hoareTime _ _ hstart (TM.emitPred_transition hp hz []) htail
  refine hfull.consequence (fun _ _ _ h => h) ?_ (by omega)
  rintro i w o ⟨hi, hw, ho⟩
  refine ⟨hi, ?_, ?_, ho.eq TM.outAcc_nil_init⟩
  · rw [hw]
    have hi0 : Fin.last 0 = (0 : Fin 1) := rfl
    simp [hi0]
  · intro j
    have hj : j = (0 : Fin 1) := Fin.ext (by have := j.isLt; omega)
    subst j
    rw [hw, Function.update_self]
    exact ⟨rfl, regTape_startInvariant _⟩

/-- The setup's actual running time bounds every charged head on every prefix. -/
theorem linearMachine_withinSpace_internal (x : List Bool) :
    linearMachine.HoareSafety (fresh x)
      (fun inp work out =>
        (⟨(), inp, work, out⟩ : Cfg 1 Unit).WithinDecisionSpace
          x.length (4 * x.length + 11)) := by
  intro inp work out hpre c hreach
  obtain ⟨d, haltTime, htime, hrun, hhalt, _⟩ := linearMachine_prepares_internal x _ _ _ hpre
  obtain ⟨t, ht⟩ := linearMachine.reaches_to_reachesIn hreach
  have hle : t ≤ haltTime := linearMachine.reachesIn_le_halt ht hrun hhalt
  rcases hpre with ⟨rfl, rfl, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro j
    have hb := linearMachine.work_head_reachesIn_bound ht j
    simp only [Tape.init] at hb
    dsimp only
    omega
  · have hb := linearMachine.input_head_reachesIn_bound ht
    simp only [Tape.init] at hb
    dsimp only
    omega
  · have hb := linearMachine.output_head_reachesIn_bound ht
    simp only [Tape.init] at hb
    dsimp only
    omega

end WitnessBoundSetup
end Complexity
