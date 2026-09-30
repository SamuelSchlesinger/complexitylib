/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Witness.Store.Defs

/-!
# Finite certificate materialization: proof internals

The existing bounded NTM guess phase supplies its endpoint semantics. The
choice-tape simulation transfers it to a composable deterministic phase, with
separate projected resource accounting for the certificate that it stores.
-/

public section

namespace Complexity
namespace NTM

/-- An actual choice-machine run advances the source exactly once per step
and leaves every source cell unchanged. -/
theorem choiceTM_reachesIn_source_internal (N : NTM k) :
    ∀ (t : ℕ) (c c' : Cfg (k + 1) N.Q),
      (N.choiceTM).reachesIn t c c' →
      (c.work (Fin.last k)).StartInvariant → 1 ≤ (c.work (Fin.last k)).head →
      c'.work (Fin.last k) =
        ⟨(c.work (Fin.last k)).head + t, (c.work (Fin.last k)).cells⟩ := by
  intro t
  induction t with
  | zero =>
    intro c c' hr _ _
    have hc : c = c' := TM.reachesIn_zero_iff.mp hr
    rw [← hc]
    rfl
  | succ t ih =>
    intro c c' hr hsi hp
    obtain ⟨d, hstep, hrest⟩ := (TM.reachesIn_succ_iff).mp hr
    have hne := TM.state_ne_qhalt_of_step hstep
    obtain ⟨e, he, _, hs⟩ := N.choiceTM_step c hne (hsi.read_ne_start hp)
    have hde : d = e := Option.some.inj (hstep.symm.trans he)
    subst d
    have hsi' : (e.work (Fin.last k)).StartInvariant := by
      rw [hs]
      exact hsi.move Dir3.right
    have hp' : 1 ≤ (e.work (Fin.last k)).head := by
      rw [hs]
      change 1 ≤ (c.work (Fin.last k)).head + 1
      omega
    have ht := ih e c' hrest hsi' hp'
    rw [ht, hs]
    simp [Tape.move, Nat.add_assoc, Nat.add_comm]

end NTM
namespace WitnessTM

/-- Every stream run stores a bounded canonical witness, with explicit frames. -/
theorem storeBounded_hoareTime_internal (witness counter : Fin k) (hne : witness ≠ counter)
    (B : ℕ) (inp : Tape) (work : Fin k → Tape) (out source : Tape)
    (hwitness : work witness = (Tape.init []).move Dir3.right)
    (hcounter : (work counter).HasUnaryCounter B)
    (hinput : inp.read ≠ Γ.start) (houtput : out.read ≠ Γ.start)
    (hother : ∀ i, i ≠ witness → i ≠ counter → (work i).read ≠ Γ.start)
    (hsource : source.StartInvariant) (hhead : 1 ≤ source.head) :
    (storeBounded witness counter).machine.HoareTime
      (storeEntry inp work out source) (storePost witness counter B inp work out source)
      (NTM.guessBoundedTime B 0) := by
  intro inp' work' out' hp
  rcases hp with ⟨hi, hw, ho⟩
  subst inp'
  subst work'
  subst out'
  let N := NTM.guessBoundedNTM witness counter
  let c : Cfg (k + 1) N.Q :=
    ⟨N.qstart, inp, Fin.snoc work source, out⟩
  let choices : Fin (NTM.guessBoundedTime B 0) → Bool :=
    fun j => NTM.choiceStream c j.val
  have hprefix : (work witness).HasBinaryPrefix [] := by
    rw [hwitness]
    simp [Tape.HasBinaryPrefix, Tape.init, Tape.move]
  have hzero : (work witness).cells 0 = Γ.start := by
    rw [hwitness]
    rfl
  have hg := NTM.guessBoundedNTM_halted_hasBoundedBinaryString_of_choose
    witness counter hne B [] (NTM.dropChoice c) rfl
    (by simpa [c, NTM.dropChoice] using hprefix)
    (by simpa [c, NTM.dropChoice] using hzero)
    (by simpa [c, NTM.dropChoice] using hcounter) choices
  obtain ⟨c', t, ht, hr, _, heq⟩ :=
    N.choiceTM_simulates (NTM.guessBoundedTime B 0) c
      (by simpa [c] using hsource) (by simpa [c] using hhead)
  have hh : N.choiceTM.halted c' := by
    have heq' := congrArg (fun d : Cfg k N.Q => d.state) heq
    exact heq'.trans hg.1
  obtain ⟨y, hy, hbinary, hcell⟩ := hg.2
  have hstored : c'.work witness.castSucc =
      (Tape.init (y.map Γ.ofBool)).move Dir3.right := by
    have hwy := congrArg (fun d : Cfg k N.Q => d.work witness) heq
    exact hwy.trans (Tape.eq_init_move_right_of_hasBinaryString hbinary hcell)
  have hi : c'.input = inp := by
    have he := congrArg (fun d : Cfg k N.Q => d.input) heq
    exact he.trans (NTM.guessBoundedNTM_trace_preserves_input witness counter _ choices
      (NTM.dropChoice c) (by simpa [c, NTM.dropChoice] using hinput))
  have ho : c'.output = out := by
    have he := congrArg (fun d : Cfg k N.Q => d.output) heq
    exact he.trans (NTM.guessBoundedNTM_trace_preserves_output witness counter _ choices
      (NTM.dropChoice c) (by simpa [c, NTM.dropChoice] using houtput))
  refine ⟨c', t, ht, hr, hh, y, ?_, hi, ho, hstored, ?_, t, ht, ?_⟩
  · simpa using hy
  · intro i hiw hic
    have he := congrArg (fun d : Cfg k N.Q => d.work i) heq
    have hf := NTM.guessBoundedNTM_trace_preserves_other_work witness counter i _ choices
      (NTM.dropChoice c) hiw hic (by simpa [c, NTM.dropChoice] using hother i hiw hic)
    exact he.trans (hf.trans (by simp [c, NTM.dropChoice]))
  · simpa [c] using NTM.choiceTM_reachesIn_source_internal N t c c' hr
      (by simpa [c] using hsource) (by simpa [c] using hhead)

/-- Every bounded finite certificate is generated by an external Boolean stream. -/
theorem storeBounded_generates_internal (witness counter : Fin k) (hne : witness ≠ counter)
    (B : ℕ) (inp : Tape) (work : Fin k → Tape) (out : Tape)
    (hwitness : work witness = (Tape.init []).move Dir3.right)
    (hcounter : (work counter).HasUnaryCounter B)
    (y : List Bool) (hy : y.length ≤ B) :
    ∃ (g : ℕ → Bool) (c' : Cfg (k + 1) (storeBounded witness counter).machine.Q) (t : ℕ),
      t ≤ NTM.guessBoundedTime B 0 ∧
      (storeBounded witness counter).machine.reachesIn t
        ⟨(storeBounded witness counter).machine.qstart, inp,
          Fin.snoc work (NTM.loadTape g), out⟩ c' ∧
      (storeBounded witness counter).machine.halted c' ∧
      c'.work witness.castSucc = (Tape.init (y.map Γ.ofBool)).move Dir3.right := by
  let N := NTM.guessBoundedNTM witness counter
  let d : Cfg k N.Q := ⟨N.qstart, inp, work, out⟩
  have hprefix : (work witness).HasBinaryPrefix [] := by
    rw [hwitness]
    simp [Tape.HasBinaryPrefix, Tape.init, Tape.move]
  have hzero : (work witness).cells 0 = Γ.start := by rw [hwitness]; rfl
  obtain ⟨choices, hh, hstored⟩ :=
    NTM.guessBoundedNTM_choose_generates_witness_initTape_move_right
      witness counter hne B [] y d hy rfl hprefix hzero hcounter
  let g : ℕ → Bool := fun i =>
    if hi : i < NTM.guessBoundedTime B 0 then choices ⟨i, hi⟩ else false
  let c : Cfg (k + 1) N.Q := NTM.attach d (NTM.loadTape g)
  have hstream : (fun j : Fin (NTM.guessBoundedTime B 0) =>
      NTM.choiceStream c j.val) = choices := by
    funext j
    have hj : NTM.choiceStream c j.val = g j.val :=
      NTM.choiceStream_of_loaded (T := NTM.guessBoundedTime B 0)
        (fun i _ => by simp [c, NTM.attach, NTM.loadTape, Nat.add_comm]) j.isLt
    rw [hj]
    simp [g, j.isLt]
  obtain ⟨c', t, ht, hr, _, heq⟩ :=
    N.choiceTM_simulates (NTM.guessBoundedTime B 0) c
      (by simpa [c, NTM.attach] using NTM.loadTape_startInvariant g)
      (by simp [c, NTM.attach, NTM.loadTape])
  rw [hstream, NTM.dropChoice_attach] at heq
  refine ⟨g, c', t, ht, hr, ?_, ?_⟩
  · exact (congrArg (fun e : Cfg k N.Q => e.state) heq).trans hh
  · have he := congrArg (fun e : Cfg k N.Q => e.work witness) heq
    exact he.trans (by simpa using hstored)

/-- The phase stores the certificate in charged space while leaving its source
stream uncharged. The conservative bound depends on `B`, never verifier time. -/
theorem storeBounded_hoareSafety_internal (witness counter : Fin k) (hne : witness ≠ counter)
    (B inputLength initialSpace : ℕ)
    (inp : Tape) (work : Fin k → Tape) (out source : Tape)
    (hwitness : work witness = (Tape.init []).move Dir3.right)
    (hcounter : (work counter).HasUnaryCounter B)
    (hinput : inp.read ≠ Γ.start) (houtput : out.read ≠ Γ.start)
    (hother : ∀ i, i ≠ witness → i ≠ counter → (work i).read ≠ Γ.start)
    (hsource : source.StartInvariant) (hhead : 1 ≤ source.head)
    (hspace : (⟨(), inp, work, out⟩ : Cfg k Unit).WithinDecisionSpace
      inputLength initialSpace) :
    (storeBounded witness counter).machine.HoareSafety (storeEntry inp work out source)
      (fun i w o =>
        (⟨(), i, (fun j => w j.castSucc), o⟩ : Cfg k Unit).WithinDecisionSpace
          inputLength (initialSpace + NTM.guessBoundedTime B 0)) := by
  apply (storeBounded_hoareTime_internal witness counter hne B inp work out source
    hwitness hcounter hinput houtput hother hsource hhead).projectedSafety
  intro i w o hp
  rcases hp with ⟨rfl, rfl, rfl⟩
  simpa using hspace

end WitnessTM
end Complexity
