/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Witness.Verifier.Defs
public import Complexitylib.Models.TuringMachine.Hoare.StartInvariant

/-!
# Realize a bound and store a finite witness

The initialized prefix keeps setup scratch separate, preserves fresh verifier
work, and materializes a certificate on a charged tape. Its endpoint resets
all later resource accounting to parked heads plus the bounded guess time.
-/

@[expose] public section

namespace Complexity
namespace WitnessTM.Verifier

/-- Initial visible tapes with a live, immutable external source at cell one. -/
def prefixEntry (r k : ℕ) (x : List Bool) : TapePred (tapes r k + 1) :=
  fun inp work out =>
    WitnessBoundSetup.fresh x inp (fun i => work i.castSucc) out ∧
    (work (Fin.last (tapes r k))).StartInvariant ∧
    (work (Fin.last (tapes r k))).head = 1

/-- Setup's canonical reserved frame alongside the same live external source. -/
def prefixReady (r k : ℕ) (x : List Bool) (B : ℕ) : TapePred (tapes r k + 1) :=
  fun inp work out =>
    WitnessBoundSetup.reservedReady x B (k + 2) inp (fun i => work i.castSucc) out ∧
    (work (Fin.last (tapes r k))).StartInvariant ∧
    (work (Fin.last (tapes r k))).head = 1

/-- A bounded certificate is stored; reserved verifier/pair tapes remain blank.
All marker invariants and charged head bounds are retained for the later seam. -/
def prefixPost (r k : ℕ) (x : List Bool) (B : ℕ) : TapePred (tapes r k + 1) :=
  fun inp work out => ∃ y : List Bool, y.length ≤ B ∧
    inp = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
    out = TM.parkedBlank ∧
    work (witnessIdx r k).castSucc = (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
    (∀ i : Fin (tapes r k), r + 1 ≤ i.val → i ≠ witnessIdx r k →
      work i.castSucc = TM.parkedBlank) ∧
    inp.StartInvariant ∧ (∀ i, (work i).StartInvariant) ∧ out.StartInvariant ∧
    (∀ i : Fin (tapes r k), (work i.castSucc).head ≤ 1 + NTM.guessBoundedTime B 0) ∧
    1 ≤ (work (Fin.last (tapes r k))).head

private theorem witness_ne_counter (r k : ℕ) : witnessIdx r k ≠ counterIdx r k := by
  intro h
  have he := congrArg Fin.val h
  simp [witnessIdx, counterIdx] at he
  omega

private theorem ready_work {inp out : Tape} {work : Fin (tapes r k + 1) → Tape}
    {x : List Bool} {B : ℕ} (h : prefixReady r k x B inp work out) :
    ∀ i, (work i).head = 1 ∧ (work i).StartInvariant := by
  intro i
  refine Fin.lastCases ?_ ?_ i
  · exact ⟨h.2.2, h.2.1⟩
  · intro j
    exact WitnessBoundSetup.reservedReady_work x B (k + 2) h.1 j

/-- Setup can run with its external source ignored and uncharged. -/
theorem setup_hoareTime (setup : WitnessBoundSetup r bound) (k : ℕ) (x : List Bool) :
    (ofDeterministic (setup.machine.liftTM (k + 2))).machine.HoareTime
      (prefixEntry r k x) (prefixReady r k x (bound x.length)) (setup.time x.length) := by
  intro inp work out hp
  have ht := TM.liftLast_hoareTime (setup.machine.liftTM (k + 2))
    (setup.prepares_reserved (k + 2) x) (work (Fin.last (tapes r k)))
    (hp.2.1.read_ne_start (by rw [hp.2.2]))
  obtain ⟨c, t, htime, hr, hh, hs, hready⟩ := ht inp work out ⟨rfl, hp.1⟩
  exact ⟨c, t, htime, hr, hh, hready, hs.symm ▸ hp.2.1, by rw [hs, hp.2.2]⟩

/-- The setup-to-store handoff is literally idle on the canonical parked frame. -/
theorem prefixReady_transition {x : List Bool} {B : ℕ}
    {inp out : Tape} {work : Fin (tapes r k + 1) → Tape}
    (h : prefixReady r k x B inp work out) :
    prefixReady r k x B (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
  have hin : inp.read ≠ Γ.start := by
    rw [h.1.1.1]
    exact (TM.parked_init_input x).read_ne_start
  have hout : out.read ≠ Γ.start := by
    rw [h.1.1.2.2.2]
    decide
  have hw : (fun i => TM.transitionTape (work i)) = work := by
    funext i
    have hi := ready_work h i
    exact TM.transitionTape_eq_self (hi.2.read_ne_start (by rw [hi.1]))
  rw [TM.transitionInput_eq_self hin, TM.transitionTape_eq_self hout, hw]
  exact h

/-- Storing after setup yields every frame needed by the deterministic suffix. -/
theorem store_ready_hoareTime (r k : ℕ) (x : List Bool) (B : ℕ) :
    (storeBounded (witnessIdx r k) (counterIdx r k)).machine.HoareTime
      (prefixReady r k x B) (prefixPost r k x B) (NTM.guessBoundedTime B 0) := by
  intro inp work out hp
  let visible : Fin (tapes r k) → Tape := fun i => work i.castSucc
  let source := work (Fin.last (tapes r k))
  have hwi : visible (witnessIdx r k) = TM.parkedBlank :=
    hp.1.2 (witnessIdx r k) (by simp [witnessIdx])
  have hcounter : (visible (counterIdx r k)).HasUnaryCounter B := by
    have he := hp.1.1.2.1
    change visible (counterIdx r k) = TM.regTape B at he
    rw [he]
    exact (TM.reg_regT B).hasUnaryCounter
  have hi : inp.read ≠ Γ.start := by
    rw [hp.1.1.1]
    exact (TM.parked_init_input x).read_ne_start
  have ho : out.read ≠ Γ.start := by rw [hp.1.1.2.2.2]; decide
  have hother : ∀ i, i ≠ witnessIdx r k → i ≠ counterIdx r k →
      (visible i).read ≠ Γ.start := by
    intro i _ _
    have hh := WitnessBoundSetup.reservedReady_work x B (k + 2) hp.1 i
    exact hh.2.read_ne_start (by rw [hh.1])
  have ht := storeBounded_hoareTime (witnessIdx r k) (counterIdx r k)
    (witness_ne_counter r k) B inp visible out source hwi hcounter hi ho hother hp.2.1
    (by change 1 ≤ (work (Fin.last (tapes r k))).head; rw [hp.2.2])
  obtain ⟨c, t, htime, hr, hh, y, hy, hinp, hout, hstored, hframe,
    used, hused, hsource⟩ := ht inp work out ⟨rfl, (Fin.snoc_init_self work).symm, rfl⟩
  have hsi := TM.reachesIn_startInvariant hr
    (by rw [hp.1.1.1]; exact (Tape.StartInvariant.init_ofBool x).move .right)
    (fun i => (ready_work hp i).2)
    (by rw [hp.1.1.2.2.2]; exact Tape.StartInvariant.init_nil.move .right)
  refine ⟨c, t, htime, hr, hh, y, hy, hinp.trans hp.1.1.1,
    hout.trans hp.1.1.2.2.2, hstored, ?_, hsi.1, hsi.2.1, hsi.2.2, ?_, ?_⟩
  · intro i hge hne
    have hic : i ≠ counterIdx r k := by
      intro he
      have hi' := congrArg Fin.val he
      simp [counterIdx] at hi'
      omega
    exact (hframe i hne hic).trans (hp.1.2 i hge)
  · intro i
    have hb := TM.work_head_reachesIn_bound
      (storeBounded (witnessIdx r k) (counterIdx r k)).machine hr i.castSucc
    have he := (ready_work hp i.castSucc).1
    dsimp only at hb
    omega
  · rw [hsource]
    change 1 ≤ source.head + used
    change 1 ≤ (work (Fin.last (tapes r k))).head + used
    rw [hp.2.2]
    omega

/-- The initialized prefix has the sum of its two concrete phase budgets. -/
theorem prefix_hoareTime (setup : WitnessBoundSetup r bound) (k : ℕ) (x : List Bool) :
    (guessPrefix setup k).machine.HoareTime (prefixEntry r k x)
      (prefixPost r k x (bound x.length))
      (setup.time x.length + 1 + NTM.guessBoundedTime (bound x.length) 0) :=
  TM.seqTM_hoareTime _ _ (setup_hoareTime setup k x)
    (fun _ _ _ h => prefixReady_transition h)
    (store_ready_hoareTime r k x (bound x.length))

private theorem mono_decisionSpace {c : Cfg n Q} {inputLength a b : ℕ}
    (h : c.WithinDecisionSpace inputLength a) (hle : a ≤ b) :
    c.WithinDecisionSpace inputLength b :=
  ⟨⟨fun i => (h.1.1 i).trans hle, by have := h.1.2; omega⟩, by have := h.2; omega⟩

/-- Prefix safety uses setup's independent space and the materialization bound,
without charging the external stream or any later verifier running time. -/
theorem prefix_hoareSafety (setup : WitnessBoundSetup r bound) (k : ℕ) (x : List Bool)
    (H : ℕ) (hs : setup.space x.length ≤ H)
    (hg : 1 + NTM.guessBoundedTime (bound x.length) 0 ≤ H) :
    (guessPrefix setup k).machine.HoareSafety (prefixEntry r k x)
      (fun inp work out =>
        (⟨(), inp, (fun i => work i.castSucc), out⟩ : Cfg (tapes r k) Unit).WithinDecisionSpace
          x.length H) := by
  have hsetup := TM.liftLast_hoareSafety (setup.machine.liftTM (k + 2))
    (setup.safety_reserved (k + 2) x)
  have hstore := (store_ready_hoareTime r k x (bound x.length)).projectedSafety
    (inputLength := x.length) (initialSpace := 1) (by
      intro inp work out hp
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro i
        exact le_of_eq (ready_work hp i.castSucc).1
      · rw [hp.1.1.1]
        change 1 ≤ x.length + 1 + 1
        omega
      · rw [hp.1.1.2.2.2]
        change (1 : ℕ) ≤ 2
        decide)
  refine TM.seqTM_hoareSafety _ _
    (safe := fun inp work out =>
      (⟨(), inp, (fun i => work i.castSucc), out⟩ : Cfg (tapes r k) Unit).WithinDecisionSpace
        x.length H)
    (setup_hoareTime setup k x) (fun _ _ _ h => prefixReady_transition h)
    (store_ready_hoareTime r k x (bound x.length)) ?_ ?_
  · exact hsetup.consequence (fun _ _ _ h => h.1)
      (fun _ _ _ h => mono_decisionSpace h (by omega))
  · exact hstore.consequence (fun _ _ _ h => h)
      (fun _ _ _ h => mono_decisionSpace h hg)

/-- Every bounded certificate is realized by the initialized prefix. The source
stream is chosen after the deterministic setup, which never consults that stream. -/
theorem prefix_generates (setup : WitnessBoundSetup r bound) (k : ℕ)
    (x y : List Bool) (hy : y.length ≤ bound x.length) :
    ∃ (g : ℕ → Bool) (c : Cfg (tapes r k + 1) (guessPrefix setup k).machine.Q) (t : ℕ),
      t ≤ setup.time x.length + 1 + NTM.guessBoundedTime (bound x.length) 0 ∧
      (guessPrefix setup k).machine.reachesIn t
        (NTM.loadCfg (guessPrefix setup k).machine x g) c ∧
      (guessPrefix setup k).machine.halted c ∧
      c.work (witnessIdx r k).castSucc = (Tape.init (y.map Γ.ofBool)).move Dir3.right := by
  let A := TM.liftLast (setup.machine.liftTM (k + 2))
  let G := (storeBounded (witnessIdx r k) (counterIdx r k)).machine
  obtain ⟨s, ts, hts, hrs, hhs, hready⟩ := setup.prepares_reserved (k + 2) x
    (Tape.init (x.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init []) ⟨rfl, rfl, rfl⟩
  have hwi : s.work (witnessIdx r k) = TM.parkedBlank :=
    hready.2 (witnessIdx r k) (by simp [witnessIdx])
  have hcounter : (s.work (counterIdx r k)).HasUnaryCounter (bound x.length) := by
    have he := hready.1.2.1
    change s.work (counterIdx r k) = TM.regTape (bound x.length) at he
    rw [he]
    exact (TM.reg_regT _).hasUnaryCounter
  obtain ⟨g, c, tg, htg, hrg, hhg, hstored⟩ := storeBounded_generates
    (witnessIdx r k) (counterIdx r k) (witness_ne_counter r k)
    (bound x.length) s.input s.work s.output hwi hcounter y hy
  have hsource : (NTM.loadTape g).read ≠ Γ.start :=
    (NTM.loadTape_startInvariant g).read_ne_start (by simp)
  have hra := TM.liftLast_reachesIn (setup.machine.liftTM (k + 2))
    (NTM.loadTape g) hsource ts hrs
  have hin : TM.transitionInput s.input = s.input := by
    apply TM.transitionInput_eq_self
    rw [hready.1.1]
    exact (TM.parked_init_input x).read_ne_start
  have hout : TM.transitionTape s.output = s.output := by
    apply TM.transitionTape_eq_self
    rw [hready.1.2.2.2]
    decide
  have hwork : (fun i : Fin (tapes r k + 1) =>
      TM.transitionTape (Fin.snoc (α := fun _ => Tape) s.work (NTM.loadTape g) i)) =
      Fin.snoc (α := fun _ => Tape) s.work (NTM.loadTape g) := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simpa using TM.transitionTape_eq_self hsource
    · intro j
      have hj := WitnessBoundSetup.reservedReady_work x (bound x.length) (k + 2) hready j
      simpa using TM.transitionTape_eq_self (hj.2.read_ne_start (by rw [hj.1]))
  have hrg' : G.reachesIn tg
      ⟨G.qstart, TM.transitionInput s.input,
        (fun i => TM.transitionTape ((NTM.attach s (NTM.loadTape g)).work i)),
        TM.transitionTape s.output⟩ c := by
    simpa only [NTM.attach, hin, hout, hwork] using hrg
  have hfull := TM.seqTM_reachesIn_of_reachesIn A G hra hhs hrg'
  refine ⟨g, TM.phase2Wrap A G c, ts + 1 + tg, by omega, ?_,
    (TM.phase2Wrap_halted_iff A G c).2 hhg, hstored⟩
  exact hfull

end WitnessTM.Verifier
end Complexity
