/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.BodyMatch
public import Complexitylib.Models.TuringMachine.UTM.Internal.BodyApply
public import Complexitylib.Models.TuringMachine.UTM.Internal.DescLayout
public import Complexitylib.Models.TuringMachine.UTM.Internal.Verdict
public import Complexitylib.Models.TuringMachine.UTM.Internal.Interp

/-!
# Body correctness: phase assembly

The per-iteration proof of the body machine, assembled from the phase
lemmas. This file starts with the standing invariant `SimInv` (the tape
shape between loop iterations, relative to the interpreted machine's
configuration) and the halt-check phase: from the body's start state, a
halted interpreted machine makes the body a bounded-time no-op, and a
running one brings it to the peek phase with all tapes restored.
-/


public section

namespace Complexity

namespace TM.UTMBody

open BodyQ

/-- `Γw.toΓ` is injective. -/
theorem Γw.toΓ_inj {x y : Γw} (h : x.toΓ = y.toΓ) : x = y := by
  cases x <;> cases y <;> simp_all [Γw.toΓ]

/-- `Γw.toΓ` hits `Γ.blank` only at `□`. -/
theorem Γw.toΓ_eq_blank {x : Γw} : x.toΓ = Γ.blank ↔ x = Γw.blank := by
  cases x <;> simp [Γw.toΓ]

/-- The body's standing tape shape between loop iterations, relative to a
    configuration `mc` of the interpreted machine `(decodeDesc α).toTM`.
    The state-tape clause is a disjunction: the running shape (the `w`-bit
    encoding of the current state) or the post-default shape (the qhalt
    field verbatim — the machine is then halted). -/
structure SimInv (α : List Bool) (mc : Cfg 1 (decodeDesc α).toTM.Q)
    (inp : Tape) (work : Fin 6 → Tape) (out : Tape) : Prop where
  vin : VShift mc.input (work vIn)
  vwk : VShift (mc.work 0) (work vWk)
  vout : VShift mc.output (work vOut)
  wf_in : mc.input.StartInvariant
  wf_wk : (mc.work 0).StartInvariant
  wf_out : mc.output.StartInvariant
  state : (mc.state.val < 2 ^ (decodeDesc α).w ∧
      (work stT).HoldsExact
        (bitsToSyms (Nat.toBits (decodeDesc α).w mc.state.val)))
    ∨ (mc.state = (decodeDesc α).toTM.qhalt ∧
      (work stT).HoldsExact (qhaltField (groupPairs α)))
  state_head : (work stT).head = 1
  desc : (work dsT).HoldsExact (groupPairs α)
  desc_head : (work dsT).head = 1
  scratch : (work scT).HoldsExact []
  scratch_head : (work scT).head = 1
  inp_read : inp.read ≠ Γ.start
  out_read : out.read ≠ Γ.start

namespace SimInv

/-- The state tape's contents (either disjunct) are blank-free. -/
theorem state_syms_ne_blank {α mc inp work out}
    (h : SimInv α mc inp work out) :
    ∃ S : List Γw, (work stT).HoldsExact S ∧ (∀ s ∈ S, s ≠ Γw.blank) ∧
      ((mc.state.val < 2 ^ (decodeDesc α).w ∧
        S = bitsToSyms (Nat.toBits (decodeDesc α).w mc.state.val)) ∨
       (mc.state = (decodeDesc α).toTM.qhalt ∧
        S = qhaltField (groupPairs α))) := by
  rcases h.state with ⟨hlt, hh⟩ | ⟨hq, hh⟩
  · exact ⟨_, hh, fun s hs => bitsToSyms_ne_blank hs, Or.inl ⟨hlt, rfl⟩⟩
  · exact ⟨_, hh, fun s hs => takeField_fst_ne_blank _ s hs, Or.inr ⟨hq, rfl⟩⟩

/-- Standard parked-reads package for the non-state, non-desc work tapes. -/
theorem others_read {α mc inp work out} (h : SimInv α mc inp work out) :
    ∀ i : Fin 6, i ≠ stT → i ≠ dsT → (work i).read ≠ Γ.start := by
  intro i hiS hiD
  rcases i with ⟨iv, hv⟩
  rcases iv with _ | _ | _ | _ | _ | _ | n
  · exact h.vin.read_ne_start h.wf_in
  · exact h.vwk.read_ne_start h.wf_wk
  · exact h.vout.read_ne_start h.wf_out
  · exact absurd rfl hiS
  · exact absurd rfl hiD
  · show (work scT).read ≠ Γ.start
    rw [Tape.read, h.scratch_head, show (1 : ℕ) = 0 + 1 from rfl,
      (Tape.HoldsExact.nil_iff.mp h.scratch).2 0]
    simp
  · exact absurd hv (by omega)

/-- Any `HoldsExact` tape with head off `▷` reads a non-`▷` symbol. -/
theorem read_ne_start_of_holdsExact {t : Tape} {l : List Γw}
    (h : t.HoldsExact l) (hh : 1 ≤ t.head) : t.read ≠ Γ.start :=
  (Tape.HoldsExact.startInvariant h).2 _ hh

end SimInv

-- ════════════════════════════════════════════════════════════════════════
-- Phase 0: the halt check
-- ════════════════════════════════════════════════════════════════════════

section HcPhase

variable {α : List Bool} {mc : Cfg 1 (decodeDesc α).toTM.Q}

/-- A tape whose head is known equals the literal rebuild. -/
private theorem tape_mk_eq {t : Tape} {h : ℕ} (hh : t.head = h) :
    (⟨h, t.cells⟩ : Tape) = t := by
  cases t
  subst hh
  rfl

private theorem takeField_fst_length_le (l : List Γw) :
    (takeField l).1.length ≤ l.length := by
  rcases takeField_structure l with hsp | ⟨hsp, -⟩
  · have := congrArg List.length hsp
    simp only [List.length_append, List.length_cons] at this
    omega
  · exact le_of_eq (congrArg List.length hsp)

private theorem takeField_snd_length_le (l : List Γw) :
    (takeField l).2.length ≤ l.length := by
  rcases takeField_structure l with hsp | ⟨-, hsp⟩
  · have := congrArg List.length hsp
    simp only [List.length_append, List.length_cons] at this
    omega
  · rw [hsp]
    simp

private theorem qhaltField_length_le (l : List Γw) :
    (qhaltField l).length ≤ l.length :=
  le_trans (takeField_fst_length_le (takeField l).2) (takeField_snd_length_le l)

/-- **Halt-check phase, halted case**: when the interpreted machine sits at
    its halt state, the body runs from its start state to `bodyDone` as a
    pure no-op — every tape is exactly restored — within
    `5·|groupPairs α| + 7` steps. -/
theorem hcPhase_halted (c : Cfg 6 bodyTM.Q)
    (hst : c.state = hc0)
    (hinv : SimInv α mc c.input c.work c.output)
    (hhalt : mc.state = (decodeDesc α).toTM.qhalt) :
    ∃ c' t, t ≤ 5 * (groupPairs α).length + 7 ∧
      bodyTM.reachesIn t c c' ∧
      c'.state = bodyDone ∧
      c'.input = c.input ∧ (∀ i, c'.work i = c.work i) ∧
      c'.output = c.output := by
  obtain ⟨S, hS_hold, hS_nb, hS_which⟩ := hinv.state_syms_ne_blank
  -- in the halted case the state tape holds exactly the qhalt field
  have hSq : S = qhaltField (groupPairs α) := by
    rcases hS_which with ⟨hlt, rfl⟩ | ⟨-, rfl⟩
    · exact (verdict_running α hlt).mpr (by rw [hhalt]; rfl)
    · rfl
  subst hSq
  have hS_wns : ∀ j, 1 ≤ j → (c.work stT).cells j ≠ Γ.start :=
    (Tape.HoldsExact.startInvariant hS_hold).2
  have hW_wns : ∀ j, 1 ≤ j → (c.work dsT).cells j ≠ Γ.start :=
    (Tape.HoldsExact.startInvariant hinv.desc).2
  have hoth_d : ∀ i, i ≠ dsT → (c.work i).read ≠ Γ.start := by
    intro i hiD
    by_cases hiS : i = stT
    · subst hiS
      exact SimInv.read_ne_start_of_holdsExact hS_hold (by rw [hinv.state_head])
    · exact hinv.others_read i hiS hiD
  -- Phase hc0: scan past field 1
  obtain ⟨c₁, hr₁, hst₁, hwtD₁, hin₁, hout₁, hoth₁⟩ :=
    scanRight_loop (cur := hc0) (next := hc1) (t := dsT)
      (fun hcon => nomatch hcon) arm_hc0
      (c.work dsT).cells hW_wns
      (takeField (groupPairs α)).1.length 1 (by omega)
      (fun j hj => descLayout_field1 hinv.desc j hj)
      (descLayout_sep1 hinv.desc)
      c hst rfl hinv.desc_head hinv.inp_read hinv.out_read
      (fun i hi => hoth_d i hi)
  have hstS₁ : c₁.work stT = c.work stT := hoth₁ stT (by decide)
  -- Phase hc1: lockstep match against the qhalt field
  obtain ⟨c₂, hr₂, hst₂, hwtS₂, hwtD₂, hin₂, hout₂, hoth₂⟩ :=
    hc1_match_loop (c.work stT).cells (c.work dsT).cells hS_wns hW_wns
      (qhaltField (groupPairs α)).length 1
      ((takeField (groupPairs α)).1.length + 2) (by omega) (by omega)
      (fun j hj => by
        constructor
        · rw [show 1 + j = j + 1 by omega,
            Tape.HoldsExact.cells_lt hS_hold hj]
          exact (descLayout_field2_val hinv.desc j hj).symm
        · rw [show 1 + j = j + 1 by omega,
            Tape.HoldsExact.cells_lt hS_hold hj]
          intro hcon
          exact (hS_nb _ (List.getElem_mem hj)) (Γw.toΓ_eq_blank.mp hcon)
      )
      (by
        rw [show 1 + (qhaltField (groupPairs α)).length
            = (qhaltField (groupPairs α)).length + 1 by omega]
        exact Tape.HoldsExact.cells_ge hS_hold (Nat.le_refl _))
      (descLayout_sep2 hinv.desc)
      c₁ hst₁
      (by rw [hstS₁]) (by rw [hstS₁, hinv.state_head])
      (by rw [hwtD₁]) (by rw [hwtD₁]; dsimp only; omega)
      (by rw [hin₁]; exact hinv.inp_read) (by rw [hout₁]; exact hinv.out_read)
      (fun i hiS hiD => by rw [hoth₁ i hiD]; exact hoth_d i hiD)
  -- Phase haltRewS: rewind the state head
  obtain ⟨c₃, hr₃, hst₃, hwtS₃, hin₃, hout₃, hoth₃⟩ :=
    rewStep_loop (cur := haltRewS) (next := haltRewD) (t := stT)
      (fun hcon => nomatch hcon) arm_haltRewS
      (c.work stT).cells hS_hold.1 hS_wns
      (1 + (qhaltField (groupPairs α)).length) c₂ hst₂
      (by rw [hwtS₂]) (by rw [hwtS₂])
      (by rw [hin₂, hin₁]; exact hinv.inp_read)
      (by rw [hout₂, hout₁]; exact hinv.out_read)
      (fun i hi => by
        by_cases hiD : i = dsT
        · subst hiD
          rw [hwtD₂]
          exact hW_wns ((takeField (groupPairs α)).1.length + 2
            + (qhaltField (groupPairs α)).length) (by omega)
        · rw [hoth₂ i hi hiD, hoth₁ i hiD]
          exact hoth_d i hiD)
  -- Phase haltRewD: rewind the desc head
  obtain ⟨c₄, hr₄, hst₄, hwtD₄, hin₄, hout₄, hoth₄⟩ :=
    rewStep_loop (cur := haltRewD) (next := bodyDone) (t := dsT)
      (fun hcon => nomatch hcon) arm_haltRewD
      (c.work dsT).cells hinv.desc.1 hW_wns
      ((takeField (groupPairs α)).1.length + 2
        + (qhaltField (groupPairs α)).length) c₃ hst₃
      (by rw [hoth₃ dsT (by decide), hwtD₂])
      (by rw [hoth₃ dsT (by decide), hwtD₂])
      (by rw [hin₃, hin₂, hin₁]; exact hinv.inp_read)
      (by rw [hout₃, hout₂, hout₁]; exact hinv.out_read)
      (fun i hi => by
        by_cases hiS : i = stT
        · subst hiS
          rw [hwtS₃]
          exact hS_wns 1 (by omega)
        · rw [hoth₃ i hiS, hoth₂ i hiS hi, hoth₁ i hi]
          exact hoth_d i hi)
  have hF1 := takeField_fst_length_le (groupPairs α)
  have hqh := qhaltField_length_le (groupPairs α)
  refine ⟨c₄,
    ((takeField (groupPairs α)).1.length + 1)
      + ((qhaltField (groupPairs α)).length + 1)
      + ((1 + (qhaltField (groupPairs α)).length) + 1)
      + (((takeField (groupPairs α)).1.length + 2
          + (qhaltField (groupPairs α)).length) + 1),
    by omega,
    reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _ hr₁ hr₂) hr₃) hr₄,
    hst₄, by rw [hin₄, hin₃, hin₂, hin₁], ?_,
    by rw [hout₄, hout₃, hout₂, hout₁]⟩
  intro i
  by_cases hiS : i = stT
  · subst hiS
    rw [hoth₄ stT (by decide), hwtS₃]
    exact tape_mk_eq hinv.state_head
  · by_cases hiD : i = dsT
    · subst hiD
      rw [hwtD₄]
      exact tape_mk_eq hinv.desc_head
    · rw [hoth₄ i hiD, hoth₃ i hiS, hoth₂ i hiS hiD, hoth₁ i hiD]

/-- **Halt-check phase, running case**: when the interpreted machine is not
    at its halt state, the body's halt check falls through to the peek
    phase with every tape exactly restored, within
    `5·|groupPairs α| + 7` steps. -/
theorem hcPhase_running (c : Cfg 6 bodyTM.Q)
    (hst : c.state = hc0)
    (hinv : SimInv α mc c.input c.work c.output)
    (hrun : mc.state ≠ (decodeDesc α).toTM.qhalt) :
    ∃ c' t, t ≤ 5 * (groupPairs α).length + 7 ∧
      bodyTM.reachesIn t c c' ∧
      c'.state = peek1 ∧
      c'.input = c.input ∧ (∀ i, c'.work i = c.work i) ∧
      c'.output = c.output := by
  -- the state clause must be the running disjunct
  rcases hinv.state with ⟨hlt, hS_hold⟩ | ⟨hq, -⟩
  swap
  · exact absurd hq hrun
  have hS_nb : ∀ s ∈ bitsToSyms (Nat.toBits (decodeDesc α).w mc.state.val),
      s ≠ Γw.blank := fun s hs => bitsToSyms_ne_blank hs
  -- the state encoding differs from the qhalt field
  have hne_list : bitsToSyms (Nat.toBits (decodeDesc α).w mc.state.val)
      ≠ qhaltField (groupPairs α) := by
    intro hcon
    exact hrun (Fin.val_injective ((verdict_running α hlt).mp hcon))
  obtain ⟨n, hnA, hnB, hagree, hmm⟩ :=
    exists_first_mismatch hS_nb
      (fun s hs => takeField_fst_ne_blank _ s hs) hne_list
  have hnB' : n ≤ (qhaltField (groupPairs α)).length := hnB
  have hS_wns : ∀ j, 1 ≤ j → (c.work stT).cells j ≠ Γ.start :=
    (Tape.HoldsExact.startInvariant hS_hold).2
  have hW_wns : ∀ j, 1 ≤ j → (c.work dsT).cells j ≠ Γ.start :=
    (Tape.HoldsExact.startInvariant hinv.desc).2
  have hoth_d : ∀ i, i ≠ dsT → (c.work i).read ≠ Γ.start := by
    intro i hiD
    by_cases hiS : i = stT
    · subst hiS
      exact SimInv.read_ne_start_of_holdsExact hS_hold (by rw [hinv.state_head])
    · exact hinv.others_read i hiS hiD
  -- Phase hc0: scan past field 1
  obtain ⟨c₁, hr₁, hst₁, hwtD₁, hin₁, hout₁, hoth₁⟩ :=
    scanRight_loop (cur := hc0) (next := hc1) (t := dsT)
      (fun hcon => nomatch hcon) arm_hc0
      (c.work dsT).cells hW_wns
      (takeField (groupPairs α)).1.length 1 (by omega)
      (fun j hj => descLayout_field1 hinv.desc j hj)
      (descLayout_sep1 hinv.desc)
      c hst rfl hinv.desc_head hinv.inp_read hinv.out_read
      (fun i hi => hoth_d i hi)
  have hstS₁ : c₁.work stT = c.work stT := hoth₁ stT (by decide)
  -- state and desc cell values in blank-default form
  have hScell : ∀ j, (c.work stT).cells (1 + j)
      = (((bitsToSyms (Nat.toBits (decodeDesc α).w mc.state.val))[j]?).getD
          Γw.blank).toΓ := by
    intro j
    rw [show 1 + j = j + 1 by omega]
    exact holdsExact_cells_getD hS_hold j
  have hWcell : ∀ j, j ≤ (qhaltField (groupPairs α)).length →
      (c.work dsT).cells ((takeField (groupPairs α)).1.length + 2 + j)
        = (((qhaltField (groupPairs α))[j]?).getD Γw.blank).toΓ :=
    fun j hj => descLayout_field2_getD hinv.desc j hj
  -- Phase hc1: lockstep compare, first mismatch at offset n
  obtain ⟨c₂, hr₂, hst₂, hwtS₂, hwtD₂, hin₂, hout₂, hoth₂⟩ :=
    hc1_mismatch_loop (c.work stT).cells (c.work dsT).cells hS_wns hW_wns
      n 1 ((takeField (groupPairs α)).1.length + 2) (by omega) (by omega)
      (fun j hj => by
        obtain ⟨hje, hjb⟩ := hagree j hj
        constructor
        · rw [hScell j, hWcell j (by omega)]
          exact congrArg Γw.toΓ hje
        · rw [hScell j]
          intro hcon
          exact hjb (Γw.toΓ_eq_blank.mp hcon))
      (by
        rw [hScell n, hWcell n hnB']
        rintro ⟨h1, h2⟩
        exact hmm ((Γw.toΓ_eq_blank.mp h1).trans (Γw.toΓ_eq_blank.mp h2).symm))
      (by
        rw [hScell n, hWcell n hnB']
        rintro ⟨-, -, h3⟩
        exact hmm (Γw.toΓ_inj h3))
      c₁ hst₁
      (by rw [hstS₁]) (by rw [hstS₁, hinv.state_head])
      (by rw [hwtD₁]) (by rw [hwtD₁]; dsimp only; omega)
      (by rw [hin₁]; exact hinv.inp_read) (by rw [hout₁]; exact hinv.out_read)
      (fun i hiS hiD => by rw [hoth₁ i hiD]; exact hoth_d i hiD)
  -- Phase preRewS: rewind the state head
  obtain ⟨c₃, hr₃, hst₃, hwtS₃, hin₃, hout₃, hoth₃⟩ :=
    rewStep_loop (cur := preRewS) (next := preRewD) (t := stT)
      (fun hcon => nomatch hcon) arm_preRewS
      (c.work stT).cells hS_hold.1 hS_wns
      (1 + n) c₂ hst₂
      (by rw [hwtS₂]) (by rw [hwtS₂])
      (by rw [hin₂, hin₁]; exact hinv.inp_read)
      (by rw [hout₂, hout₁]; exact hinv.out_read)
      (fun i hi => by
        by_cases hiD : i = dsT
        · subst hiD
          rw [hwtD₂]
          exact hW_wns ((takeField (groupPairs α)).1.length + 2 + n) (by omega)
        · rw [hoth₂ i hi hiD, hoth₁ i hiD]
          exact hoth_d i hiD)
  -- Phase preRewD: rewind the desc head
  obtain ⟨c₄, hr₄, hst₄, hwtD₄, hin₄, hout₄, hoth₄⟩ :=
    rewStep_loop (cur := preRewD) (next := peek1) (t := dsT)
      (fun hcon => nomatch hcon) arm_preRewD
      (c.work dsT).cells hinv.desc.1 hW_wns
      ((takeField (groupPairs α)).1.length + 2 + n) c₃ hst₃
      (by rw [hoth₃ dsT (by decide), hwtD₂])
      (by rw [hoth₃ dsT (by decide), hwtD₂])
      (by rw [hin₃, hin₂, hin₁]; exact hinv.inp_read)
      (by rw [hout₃, hout₂, hout₁]; exact hinv.out_read)
      (fun i hi => by
        by_cases hiS : i = stT
        · subst hiS
          rw [hwtS₃]
          exact hS_wns 1 (by omega)
        · rw [hoth₃ i hiS, hoth₂ i hiS hi, hoth₁ i hi]
          exact hoth_d i hi)
  have hF1 := takeField_fst_length_le (groupPairs α)
  have hqh := qhaltField_length_le (groupPairs α)
  refine ⟨c₄,
    ((takeField (groupPairs α)).1.length + 1) + (n + 1) + ((1 + n) + 1)
      + (((takeField (groupPairs α)).1.length + 2 + n) + 1),
    by omega,
    reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _ hr₁ hr₂) hr₃) hr₄,
    hst₄, by rw [hin₄, hin₃, hin₂, hin₁], ?_,
    by rw [hout₄, hout₃, hout₂, hout₁]⟩
  intro i
  by_cases hiS : i = stT
  · subst hiS
    rw [hoth₄ stT (by decide), hwtS₃]
    exact tape_mk_eq hinv.state_head
  · by_cases hiD : i = dsT
    · subst hiD
      rw [hwtD₄]
      exact tape_mk_eq hinv.desc_head
    · rw [hoth₄ i hiD, hoth₃ i hiS, hoth₂ i hiS hiD, hoth₁ i hiD]

/-- **Peek and seek phases**: from `peek1`, capture the (honest) at-origin
    flags and walk the desc head to the start of the entry region
    (`|F1| + |F2| + 3`), all other tapes exactly restored, within
    `2·|groupPairs α| + 4` steps. -/
theorem peekSeekPhase (c : Cfg 6 bodyTM.Q)
    (hst : c.state = peek1)
    (hinv : SimInv α mc c.input c.work c.output) :
    ∃ c' t, t ≤ 2 * (groupPairs α).length + 4 ∧
      bodyTM.reachesIn t c c' ∧
      c'.state = cmpQ (decide (mc.input.head = 0), decide ((mc.work 0).head = 0),
        decide (mc.output.head = 0)) ∧
      (∀ i, i ≠ dsT → c'.work i = c.work i) ∧
      c'.work dsT = ⟨(takeField (groupPairs α)).1.length
        + (qhaltField (groupPairs α)).length + 3, (c.work dsT).cells⟩ ∧
      c'.input = c.input ∧ c'.output = c.output := by
  obtain ⟨S, hS_hold, hS_nb, hS_which⟩ := hinv.state_syms_ne_blank
  have hst_read : (c.work stT).read ≠ Γ.start :=
    SimInv.read_ne_start_of_holdsExact hS_hold (by rw [hinv.state_head])
  have hds_read : (c.work dsT).read ≠ Γ.start :=
    SimInv.read_ne_start_of_holdsExact hinv.desc (by rw [hinv.desc_head])
  have hsc_read : (c.work scT).read ≠ Γ.start :=
    SimInv.read_ne_start_of_holdsExact hinv.scratch (by rw [hinv.scratch_head])
  have hW_wns : ∀ j, 1 ≤ j → (c.work dsT).cells j ≠ Γ.start :=
    (Tape.HoldsExact.startInvariant hinv.desc).2
  -- peek: two steps, all tapes restored
  obtain ⟨c₁, hr₁, hst₁, hv0₁, hv1₁, hv2₁, hstT₁, hdsT₁, hscT₁, hin₁, hout₁⟩ :=
    peek_correct hinv.vin hinv.vwk hinv.vout hinv.wf_in hinv.wf_wk hinv.wf_out
      hst hst_read hds_read hsc_read hinv.inp_read hinv.out_read
  have hoth_d₁ : ∀ i, i ≠ dsT → c₁.work i = c.work i := by
    intro i hiD
    rcases i with ⟨iv, hv⟩
    rcases iv with _ | _ | _ | _ | _ | _ | m
    · exact hv0₁
    · exact hv1₁
    · exact hv2₁
    · exact hstT₁
    · exact absurd rfl hiD
    · exact hscT₁
    · exact absurd hv (by omega)
  have hoth_read : ∀ i, i ≠ dsT → (c.work i).read ≠ Γ.start := by
    intro i hiD
    by_cases hiS : i = stT
    · subst hiS; exact hst_read
    · exact hinv.others_read i hiS hiD
  -- seek1: past the first separator
  obtain ⟨c₂, hr₂, hst₂, hwtD₂, hin₂, hout₂, hoth₂⟩ :=
    scanRight_loop (cur := seek1 _) (next := seek2 _) (t := dsT)
      (fun hcon => nomatch hcon) (arm_seek1 · · · _)
      (c.work dsT).cells hW_wns
      (takeField (groupPairs α)).1.length 1 (by omega)
      (fun j hj => descLayout_field1 hinv.desc j hj)
      (descLayout_sep1 hinv.desc)
      c₁ hst₁ (by rw [hdsT₁]) (by rw [hdsT₁, hinv.desc_head])
      (by rw [hin₁]; exact hinv.inp_read) (by rw [hout₁]; exact hinv.out_read)
      (fun i hi => by rw [hoth_d₁ i hi]; exact hoth_read i hi)
  -- seek2: past the second separator
  obtain ⟨c₃, hr₃, hst₃, hwtD₃, hin₃, hout₃, hoth₃⟩ :=
    scanRight_loop (cur := seek2 _) (next := cmpQ _) (t := dsT)
      (fun hcon => nomatch hcon) (arm_seek2 · · · _)
      (c.work dsT).cells hW_wns
      (qhaltField (groupPairs α)).length
      ((takeField (groupPairs α)).1.length + 2) (by omega)
      (fun j hj => descLayout_field2 hinv.desc j hj)
      (descLayout_sep2 hinv.desc)
      c₂ hst₂ (by rw [hwtD₂]) (by rw [hwtD₂]; dsimp only; omega)
      (by rw [hin₂, hin₁]; exact hinv.inp_read)
      (by rw [hout₂, hout₁]; exact hinv.out_read)
      (fun i hi => by rw [hoth₂ i hi, hoth_d₁ i hi]; exact hoth_read i hi)
  have hF1 := takeField_fst_length_le (groupPairs α)
  have hqh := qhaltField_length_le (groupPairs α)
  refine ⟨c₃, 2 + ((takeField (groupPairs α)).1.length + 1)
      + ((qhaltField (groupPairs α)).length + 1),
    by omega,
    reachesIn_trans _ (reachesIn_trans _ hr₁ hr₂) hr₃,
    hst₃,
    (fun i hi => by rw [hoth₃ i hi, hoth₂ i hi, hoth_d₁ i hi]),
    (by rw [hwtD₃]
        exact congrArg (fun m => (⟨m, (c.work dsT).cells⟩ : Tape)) (by omega)),
    by rw [hin₃, hin₂, hin₁], by rw [hout₃, hout₂, hout₁]⟩

/-- **Cleanup phase** (after a successful apply): blank-rewind the scratch
    tape, then rewind the state and desc heads; ends at `bodyDone` with the
    scratch cleared and every other tape's cells intact. -/
theorem cleanupPhase (c : Cfg 6 bodyTM.Q) (E S W : ℕ → Γ) (p sp dp : ℕ)
    (hsp : 1 ≤ sp) (hdp : 1 ≤ dp)
    (hst : c.state = clScr)
    (hE0 : E 0 = Γ.start) (hEns : ∀ j, 1 ≤ j → E j ≠ Γ.start)
    (hEbeyond : ∀ j, p < j → E j = Γ.blank)
    (hscC : (c.work scT).cells = E) (hscH : (c.work scT).head = p)
    (hS0 : S 0 = Γ.start) (hSns : ∀ j, 1 ≤ j → S j ≠ Γ.start)
    (hstC : (c.work stT).cells = S) (hstH : (c.work stT).head = sp)
    (hW0 : W 0 = Γ.start) (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start)
    (hdsC : (c.work dsT).cells = W) (hdsH : (c.work dsT).head = dp)
    (hin : c.input.read ≠ Γ.start) (hout : c.output.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ stT → i ≠ dsT → i ≠ scT → (c.work i).read ≠ Γ.start) :
    ∃ c', bodyTM.reachesIn ((p + 1) + (sp + 1) + (dp + 1)) c c' ∧
      c'.state = bodyDone ∧
      (c'.work scT).HoldsExact [] ∧ (c'.work scT).head = 1 ∧
      c'.work stT = ⟨1, S⟩ ∧ c'.work dsT = ⟨1, W⟩ ∧
      (∀ i, i ≠ stT → i ≠ dsT → i ≠ scT → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output := by
  have hst_read : (c.work stT).read ≠ Γ.start := by
    rw [Tape.read, hstC, hstH]; exact hSns sp hsp
  have hds_read : (c.work dsT).read ≠ Γ.start := by
    rw [Tape.read, hdsC, hdsH]; exact hWns dp hdp
  -- the blanked scratch cells
  set E' : ℕ → Γ := fun j => if 1 ≤ j ∧ j ≤ p then Γ.blank else E j with hE'
  have hE'ns : ∀ j, 1 ≤ j → E' j ≠ Γ.start := by
    intro j hj
    rw [hE']
    dsimp only
    split
    · simp
    · exact hEns j hj
  -- clScr: blank-rewind the scratch
  obtain ⟨c₁, hr₁, hst₁, hwtSc₁, hin₁, hout₁, hoth₁⟩ :=
    blankRewStep_loop (cur := clScr) (next := clSt) (t := scT)
      (fun hcon => nomatch hcon) arm_clScr
      p E hE0 hEns c hst hscC hscH hin hout
      (fun i hi => by
        by_cases hiS : i = stT
        · subst hiS; exact hst_read
        · by_cases hiD : i = dsT
          · subst hiD; exact hds_read
          · exact hoth i hiS hiD hi)
  -- clSt: rewind the state head
  obtain ⟨c₂, hr₂, hst₂, hwtS₂, hin₂, hout₂, hoth₂⟩ :=
    rewStep_loop (cur := clSt) (next := clDesc) (t := stT)
      (fun hcon => nomatch hcon) arm_clSt
      S hS0 hSns sp c₁ hst₁
      (by rw [hoth₁ stT (by decide), hstC]) (by rw [hoth₁ stT (by decide), hstH])
      (by rw [hin₁]; exact hin) (by rw [hout₁]; exact hout)
      (fun i hi => by
        by_cases hiD : i = dsT
        · subst hiD
          rw [hoth₁ dsT (by decide)]
          exact hds_read
        · by_cases hiSc : i = scT
          · subst hiSc
            rw [hwtSc₁, Tape.read]
            exact hE'ns 1 (by omega)
          · rw [hoth₁ i hiSc]
            exact hoth i hi hiD hiSc)
  -- clDesc: rewind the desc head
  obtain ⟨c₃, hr₃, hst₃, hwtD₃, hin₃, hout₃, hoth₃⟩ :=
    rewStep_loop (cur := clDesc) (next := bodyDone) (t := dsT)
      (fun hcon => nomatch hcon) arm_clDesc
      W hW0 hWns dp c₂ hst₂
      (by rw [hoth₂ dsT (by decide), hoth₁ dsT (by decide), hdsC])
      (by rw [hoth₂ dsT (by decide), hoth₁ dsT (by decide), hdsH])
      (by rw [hin₂, hin₁]; exact hin) (by rw [hout₂, hout₁]; exact hout)
      (fun i hi => by
        by_cases hiS : i = stT
        · subst hiS
          rw [hwtS₂]
          exact hSns 1 (by omega)
        · by_cases hiSc : i = scT
          · subst hiSc
            rw [hoth₂ scT (by decide), hwtSc₁, Tape.read]
            exact hE'ns 1 (by omega)
          · rw [hoth₂ i hiS, hoth₁ i hiSc]
            exact hoth i hiS hi hiSc)
  have hsc_final : c₃.work scT = ⟨1, E'⟩ := by
    rw [hoth₃ scT (by decide), hoth₂ scT (by decide), hwtSc₁]
  refine ⟨c₃, reachesIn_trans _ (reachesIn_trans _ hr₁ hr₂) hr₃, hst₃, ?_, ?_,
    by rw [hoth₃ stT (by decide), hwtS₂], hwtD₃, ?_, ?_, ?_⟩
  · rw [hsc_final]
    refine Tape.HoldsExact.nil_iff.mpr ⟨?_, ?_⟩
    · show E' 0 = Γ.start
      rw [hE']
      dsimp only
      rw [ite_eq_right (by omega)]
      exact hE0
    · intro i
      show E' (i + 1) = Γ.blank
      rw [hE']
      dsimp only
      split
      · rfl
      · exact hEbeyond (i + 1) (by omega)
  · rw [hsc_final]
  · intro i hiS hiD hiSc
    rw [hoth₃ i hiD, hoth₂ i hiS, hoth₁ i hiSc]
  · rw [hin₃, hin₂, hin₁]
  · rw [hout₃, hout₂, hout₁]

/-- **Default-phase tail** (from `dfScr`, after the sanitized virtual moves
    were applied on the `segCheck` step): clear the scratch, blank the state
    tape, copy the qhalt field onto it, rewind everything; ends at
    `bodyDone` with the state tape holding the qhalt field — the shape of
    the invariant's post-default disjunct. -/
theorem defaultTail (c : Cfg 6 bodyTM.Q) (E : ℕ → Γ) (SL : List Γw)
    (p sp dp : ℕ) (hsp : 1 ≤ sp) (hdp : 1 ≤ dp)
    (hst : c.state = dfScr)
    (hE0 : E 0 = Γ.start) (hEns : ∀ j, 1 ≤ j → E j ≠ Γ.start)
    (hEbeyond : ∀ j, p < j → E j = Γ.blank)
    (hscC : (c.work scT).cells = E) (hscH : (c.work scT).head = p)
    (hSL_hold : (c.work stT).HoldsExact SL) (hSL_nb : ∀ s ∈ SL, s ≠ Γw.blank)
    (hstH : (c.work stT).head = sp)
    (hdesc : (c.work dsT).HoldsExact (groupPairs α)) (hdsH : (c.work dsT).head = dp)
    (hin : c.input.read ≠ Γ.start) (hout : c.output.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ stT → i ≠ dsT → i ≠ scT → (c.work i).read ≠ Γ.start) :
    ∃ c' t, t ≤ p + 2 * sp + 2 * SL.length + 2 * dp
        + 2 * (takeField (groupPairs α)).1.length
        + 3 * (qhaltField (groupPairs α)).length + 12 ∧
      bodyTM.reachesIn t c c' ∧
      c'.state = bodyDone ∧
      (c'.work stT).HoldsExact (qhaltField (groupPairs α)) ∧
      (c'.work stT).head = 1 ∧
      c'.work dsT = ⟨1, (c.work dsT).cells⟩ ∧
      (c'.work scT).HoldsExact [] ∧ (c'.work scT).head = 1 ∧
      (∀ i, i ≠ stT → i ≠ dsT → i ≠ scT → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output := by
  have hS_wns := (Tape.HoldsExact.startInvariant hSL_hold).2
  have hW_wns := (Tape.HoldsExact.startInvariant hdesc).2
  have hst_read : (c.work stT).read ≠ Γ.start := by
    rw [Tape.read, hstH]; exact hS_wns sp hsp
  have hds_read : (c.work dsT).read ≠ Γ.start := by
    rw [Tape.read, hdsH]; exact hW_wns dp hdp
  set E' : ℕ → Γ := fun j => if 1 ≤ j ∧ j ≤ p then Γ.blank else E j with hE'
  have hE'ns : ∀ j, 1 ≤ j → E' j ≠ Γ.start := by
    intro j hj
    rw [hE']; dsimp only
    split
    · simp
    · exact hEns j hj
  have hE'read1 : E' 1 ≠ Γ.start := hE'ns 1 (by omega)
  -- dfScr: blank-rewind scratch
  obtain ⟨c₁, hr₁, hst₁, hwtSc₁, hin₁, hout₁, hoth₁⟩ :=
    blankRewStep_loop (cur := dfScr) (next := dfStRew) (t := scT)
      (fun hcon => nomatch hcon) arm_dfScr
      p E hE0 hEns c hst hscC hscH hin hout
      (fun i hi => by
        by_cases hiS : i = stT
        · subst hiS; exact hst_read
        · by_cases hiD : i = dsT
          · subst hiD; exact hds_read
          · exact hoth i hiS hiD hi)
  have hscRead₁ : (c₁.work scT).read ≠ Γ.start := by
    rw [hwtSc₁, Tape.read]; exact hE'read1
  -- dfStRew: rewind state
  obtain ⟨c₂, hr₂, hst₂, hwtS₂, hin₂, hout₂, hoth₂⟩ :=
    rewStep_loop (cur := dfStRew) (next := dfBlank) (t := stT)
      (fun hcon => nomatch hcon) arm_dfStRew
      (c.work stT).cells hSL_hold.1 hS_wns sp c₁ hst₁
      (by rw [hoth₁ stT (by decide)]) (by rw [hoth₁ stT (by decide), hstH])
      (by rw [hin₁]; exact hin) (by rw [hout₁]; exact hout)
      (fun i hi => by
        by_cases hiD : i = dsT
        · subst hiD; rw [hoth₁ dsT (by decide)]; exact hds_read
        · by_cases hiSc : i = scT
          · subst hiSc; exact hscRead₁
          · rw [hoth₁ i hiSc]; exact hoth i hi hiD hiSc)
  -- dfBlank: blank the state tape rightward from cell 1
  obtain ⟨c₃, hr₃, hst₃, hwtS₃, hin₃, hout₃, hoth₃⟩ :=
    dfBlank_loop SL.length (c.work stT).cells hS_wns 1 (by omega)
      (fun j hj => by
        rw [show 1 + j = j + 1 by omega, Tape.HoldsExact.cells_lt hSL_hold hj]
        intro hcon
        exact hSL_nb _ (List.getElem_mem hj) (Γw.toΓ_eq_blank.mp hcon))
      (by
        rw [show 1 + SL.length = SL.length + 1 by omega]
        exact Tape.HoldsExact.cells_ge hSL_hold (Nat.le_refl _))
      c₂ hst₂ (by rw [hwtS₂]) (by rw [hwtS₂])
      (by rw [hin₂, hin₁]; exact hin) (by rw [hout₂, hout₁]; exact hout)
      (fun i hi => by
        by_cases hiD : i = dsT
        · subst hiD
          rw [hoth₂ dsT (by decide), hoth₁ dsT (by decide)]
          exact hds_read
        · by_cases hiSc : i = scT
          · subst hiSc; rw [hoth₂ scT (by decide)]; exact hscRead₁
          · rw [hoth₂ i hi, hoth₁ i hiSc]; exact hoth i hi hiD hiSc)
  -- the blanked state cells: everything at ≥ 1 is blank
  set B : ℕ → Γ := fun j =>
    if 1 ≤ j ∧ j < 1 + SL.length then Γ.blank else (c.work stT).cells j with hB
  have hB0 : B 0 = Γ.start := by
    rw [hB]; dsimp only
    rw [ite_eq_right (by omega)]
    exact hSL_hold.1
  have hBns : ∀ j, 1 ≤ j → B j ≠ Γ.start := by
    intro j hj
    rw [hB]; dsimp only
    split
    · simp
    · exact hS_wns j hj
  have hBblank : ∀ j, 1 ≤ j → B j = Γ.blank := by
    intro j hj
    rw [hB]; dsimp only
    split
    · rfl
    · next hcon =>
      rw [show j = (j - 1) + 1 by omega]
      exact Tape.HoldsExact.cells_ge hSL_hold (by omega)
  -- dfStRew2: rewind the state head from the blanking frontier
  obtain ⟨c₄, hr₄, hst₄, hwtS₄, hin₄, hout₄, hoth₄⟩ :=
    rewStep_loop (cur := dfStRew2) (next := dfDescRew) (t := stT)
      (fun hcon => nomatch hcon) arm_dfStRew2
      B hB0 hBns (1 + SL.length) c₃ hst₃
      (by rw [hwtS₃]) (by rw [hwtS₃])
      (by rw [hin₃, hin₂, hin₁]; exact hin)
      (by rw [hout₃, hout₂, hout₁]; exact hout)
      (fun i hi => by
        by_cases hiD : i = dsT
        · subst hiD
          rw [hoth₃ dsT (by decide), hoth₂ dsT (by decide), hoth₁ dsT (by decide)]
          exact hds_read
        · by_cases hiSc : i = scT
          · subst hiSc
            rw [hoth₃ scT (by decide), hoth₂ scT (by decide)]
            exact hscRead₁
          · rw [hoth₃ i hi, hoth₂ i hi, hoth₁ i hiSc]
            exact hoth i hi hiD hiSc)
  -- dfDescRew: rewind the desc head
  obtain ⟨c₅, hr₅, hst₅, hwtD₅, hin₅, hout₅, hoth₅⟩ :=
    rewStep_loop (cur := dfDescRew) (next := dfSkip) (t := dsT)
      (fun hcon => nomatch hcon) arm_dfDescRew
      (c.work dsT).cells hdesc.1 hW_wns dp c₄ hst₄
      (by rw [hoth₄ dsT (by decide), hoth₃ dsT (by decide),
        hoth₂ dsT (by decide), hoth₁ dsT (by decide)])
      (by rw [hoth₄ dsT (by decide), hoth₃ dsT (by decide),
        hoth₂ dsT (by decide), hoth₁ dsT (by decide), hdsH])
      (by rw [hin₄, hin₃, hin₂, hin₁]; exact hin)
      (by rw [hout₄, hout₃, hout₂, hout₁]; exact hout)
      (fun i hi => by
        by_cases hiS : i = stT
        · subst hiS
          rw [hwtS₄]
          exact hBns 1 (by omega)
        · by_cases hiSc : i = scT
          · subst hiSc
            rw [hoth₄ scT (by decide), hoth₃ scT (by decide),
              hoth₂ scT (by decide)]
            exact hscRead₁
          · rw [hoth₄ i hiS, hoth₃ i hiS, hoth₂ i hiS, hoth₁ i hiSc]
            exact hoth i hiS hi hiSc)
  -- dfSkip: scan past field 1
  obtain ⟨c₆, hr₆, hst₆, hwtD₆, hin₆, hout₆, hoth₆⟩ :=
    scanRight_loop (cur := dfSkip) (next := dfCopy) (t := dsT)
      (fun hcon => nomatch hcon) arm_dfSkip
      (c.work dsT).cells hW_wns
      (takeField (groupPairs α)).1.length 1 (by omega)
      (fun j hj => descLayout_field1 hdesc j hj)
      (descLayout_sep1 hdesc)
      c₅ hst₅ (by rw [hwtD₅]) (by rw [hwtD₅])
      (by rw [hin₅, hin₄, hin₃, hin₂, hin₁]; exact hin)
      (by rw [hout₅, hout₄, hout₃, hout₂, hout₁]; exact hout)
      (fun i hi => by
        by_cases hiS : i = stT
        · subst hiS
          rw [hoth₅ stT (by decide), hwtS₄]
          exact hBns 1 (by omega)
        · by_cases hiSc : i = scT
          · subst hiSc
            rw [hoth₅ scT (by decide), hoth₄ scT (by decide),
              hoth₃ scT (by decide), hoth₂ scT (by decide)]
            exact hscRead₁
          · rw [hoth₅ i hi, hoth₄ i hiS, hoth₃ i hiS, hoth₂ i hiS,
              hoth₁ i hiSc]
            exact hoth i hiS hi hiSc)
  -- dfCopy: copy the qhalt field onto the (blank) state tape
  obtain ⟨c₇, hr₇, hst₇, hwtS₇, hwtD₇, hin₇, hout₇, hoth₇⟩ :=
    dfCopy_loop (c.work dsT).cells hW_wns
      (qhaltField (groupPairs α)).length B hBns
      1 ((takeField (groupPairs α)).1.length + 2) (by omega) (by omega)
      (fun j hj => descLayout_field2 hdesc j hj)
      (descLayout_sep2 hdesc)
      c₆ hst₆
      (by rw [hoth₆ stT (by decide), hoth₅ stT (by decide), hwtS₄])
      (by rw [hoth₆ stT (by decide), hoth₅ stT (by decide), hwtS₄])
      (by rw [hwtD₆]) (by rw [hwtD₆]; dsimp only; omega)
      (by rw [hin₆, hin₅, hin₄, hin₃, hin₂, hin₁]; exact hin)
      (by rw [hout₆, hout₅, hout₄, hout₃, hout₂, hout₁]; exact hout)
      (fun i hiS hiD => by
        by_cases hiSc : i = scT
        · subst hiSc
          rw [hoth₆ scT (by decide), hoth₅ scT (by decide),
            hoth₄ scT (by decide), hoth₃ scT (by decide), hoth₂ scT (by decide)]
          exact hscRead₁
        · rw [hoth₆ i hiD, hoth₅ i hiD, hoth₄ i hiS, hoth₃ i hiS,
            hoth₂ i hiS, hoth₁ i hiSc]
          exact hoth i hiS hiD hiSc)
  -- the copied state cells hold exactly the qhalt field
  set C : ℕ → Γ := fun j =>
    if 1 ≤ j ∧ j < 1 + (qhaltField (groupPairs α)).length then
      (c.work dsT).cells ((takeField (groupPairs α)).1.length + 2 + (j - 1))
    else B j with hC
  have hCns : ∀ j, 1 ≤ j → C j ≠ Γ.start := by
    intro j hj
    rw [hC]; dsimp only
    split
    · exact hW_wns _ (by omega)
    · exact hBns j hj
  have hC0 : C 0 = Γ.start := by
    rw [hC]; dsimp only
    rw [ite_eq_right (by omega)]
    exact hB0
  -- dfStRew3: rewind the state head
  obtain ⟨c₈, hr₈, hst₈, hwtS₈, hin₈, hout₈, hoth₈⟩ :=
    rewStep_loop (cur := dfStRew3) (next := dfDescRew2) (t := stT)
      (fun hcon => nomatch hcon) arm_dfStRew3
      C hC0 hCns (1 + (qhaltField (groupPairs α)).length) c₇ hst₇
      (by rw [hwtS₇]) (by rw [hwtS₇])
      (by rw [hin₇, hin₆, hin₅, hin₄, hin₃, hin₂, hin₁]; exact hin)
      (by rw [hout₇, hout₆, hout₅, hout₄, hout₃, hout₂, hout₁]; exact hout)
      (fun i hi => by
        by_cases hiD : i = dsT
        · subst hiD
          rw [hwtD₇]
          exact hW_wns ((takeField (groupPairs α)).1.length + 2
            + (qhaltField (groupPairs α)).length) (by omega)
        · by_cases hiSc : i = scT
          · subst hiSc
            rw [hoth₇ scT (by decide) (by decide), hoth₆ scT (by decide),
              hoth₅ scT (by decide), hoth₄ scT (by decide),
              hoth₃ scT (by decide), hoth₂ scT (by decide)]
            exact hscRead₁
          · rw [hoth₇ i hi hiD, hoth₆ i hiD, hoth₅ i hiD, hoth₄ i hi,
              hoth₃ i hi, hoth₂ i hi, hoth₁ i hiSc]
            exact hoth i hi hiD hiSc)
  -- dfDescRew2: rewind the desc head, done
  obtain ⟨c₉, hr₉, hst₉, hwtD₉, hin₉, hout₉, hoth₉⟩ :=
    rewStep_loop (cur := dfDescRew2) (next := bodyDone) (t := dsT)
      (fun hcon => nomatch hcon) arm_dfDescRew2
      (c.work dsT).cells hdesc.1 hW_wns
      ((takeField (groupPairs α)).1.length + 2
        + (qhaltField (groupPairs α)).length) c₈ hst₈
      (by rw [hoth₈ dsT (by decide), hwtD₇])
      (by rw [hoth₈ dsT (by decide), hwtD₇])
      (by rw [hin₈, hin₇, hin₆, hin₅, hin₄, hin₃, hin₂, hin₁]; exact hin)
      (by rw [hout₈, hout₇, hout₆, hout₅, hout₄, hout₃, hout₂, hout₁]
          exact hout)
      (fun i hi => by
        by_cases hiS : i = stT
        · subst hiS
          rw [hwtS₈]
          exact hCns 1 (by omega)
        · by_cases hiSc : i = scT
          · subst hiSc
            rw [hoth₈ scT (by decide), hoth₇ scT (by decide) (by decide),
              hoth₆ scT (by decide), hoth₅ scT (by decide),
              hoth₄ scT (by decide), hoth₃ scT (by decide),
              hoth₂ scT (by decide)]
            exact hscRead₁
          · rw [hoth₈ i hiS, hoth₇ i hiS hi, hoth₆ i hi, hoth₅ i hi,
              hoth₄ i hiS, hoth₃ i hiS, hoth₂ i hiS, hoth₁ i hiSc]
            exact hoth i hiS hi hiSc)
  refine ⟨c₉,
    (p + 1) + (sp + 1) + (SL.length + 1) + ((1 + SL.length) + 1) + (dp + 1)
      + ((takeField (groupPairs α)).1.length + 1)
      + ((qhaltField (groupPairs α)).length + 1)
      + ((1 + (qhaltField (groupPairs α)).length) + 1)
      + (((takeField (groupPairs α)).1.length + 2
          + (qhaltField (groupPairs α)).length) + 1),
    by omega,
    reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _
      (reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _
        (reachesIn_trans _ hr₁ hr₂) hr₃) hr₄) hr₅) hr₆) hr₇) hr₈) hr₉,
    hst₉, ?_, ?_, hwtD₉, ?_, ?_, ?_, ?_, ?_⟩
  · -- the state tape holds exactly the qhalt field
    rw [hoth₉ stT (by decide), hwtS₈]
    refine ⟨hC0, fun i => ?_⟩
    show C (i + 1) = _
    rw [hC]
    dsimp only
    by_cases hi : i < (qhaltField (groupPairs α)).length
    · rw [ite_eq_left (by omega), dite_eq_left hi,
        show (takeField (groupPairs α)).1.length + 2 + (i + 1 - 1)
          = (takeField (groupPairs α)).1.length + 2 + i by omega]
      exact descLayout_field2_val hdesc i hi
    · rw [ite_eq_right (by omega), dite_eq_right hi]
      exact hBblank (i + 1) (by omega)
  · rw [hoth₉ stT (by decide), hwtS₈]
  · -- scratch cleared
    rw [hoth₉ scT (by decide), hoth₈ scT (by decide),
      hoth₇ scT (by decide) (by decide), hoth₆ scT (by decide),
      hoth₅ scT (by decide), hoth₄ scT (by decide), hoth₃ scT (by decide),
      hoth₂ scT (by decide), hwtSc₁]
    refine Tape.HoldsExact.nil_iff.mpr ⟨?_, ?_⟩
    · show E' 0 = Γ.start
      rw [hE']
      dsimp only
      rw [ite_eq_right (by omega)]
      exact hE0
    · intro i
      show E' (i + 1) = Γ.blank
      rw [hE']
      dsimp only
      split
      · rfl
      · exact hEbeyond (i + 1) (by omega)
  · rw [hoth₉ scT (by decide), hoth₈ scT (by decide),
      hoth₇ scT (by decide) (by decide), hoth₆ scT (by decide),
      hoth₅ scT (by decide), hoth₄ scT (by decide), hoth₃ scT (by decide),
      hoth₂ scT (by decide), hwtSc₁]
  · intro i hiS hiD hiSc
    rw [hoth₉ i hiD, hoth₈ i hiS, hoth₇ i hiS hiD, hoth₆ i hiD, hoth₅ i hiD,
      hoth₄ i hiS, hoth₃ i hiS, hoth₂ i hiS, hoth₁ i hiSc]
  · rw [hin₉, hin₈, hin₇, hin₆, hin₅, hin₄, hin₃, hin₂, hin₁]
  · rw [hout₉, hout₈, hout₇, hout₆, hout₅, hout₄, hout₃, hout₂, hout₁]

/-- **Apply phase** (from `appRewScr f`, scratch holding the copied value
    `EL` = new-state field (`|SL|` cells, the old state's width) followed by
    the ten action cells): rewind scratch, overwrite the state tape, decode
    and act on the virtual tapes, clean up. Ends at `bodyDone` with the
    state tape holding the value's first `|SL|` cells and the virtual tapes
    transformed by the sanitized action. -/
theorem applyPhase (c : Cfg 6 bodyTM.Q) {f : VFlags} {sim0 sim1 sim2 : Tape}
    (EL SL : List Γw) (sc_p dp : ℕ)
    (_hscp : 1 ≤ sc_p) (hdp : 1 ≤ dp)
    (hlen : EL.length = SL.length + 10)
    (hSL_nb : ∀ s ∈ SL, s ≠ Γw.blank)
    (hst : c.state = appRewScr f)
    (h0 : VShift sim0 (c.work vIn)) (h1 : VShift sim1 (c.work vWk))
    (h2 : VShift sim2 (c.work vOut))
    (hwf0 : sim0.StartInvariant) (hwf1 : sim1.StartInvariant) (hwf2 : sim2.StartInvariant)
    (hf0 : f.1 = decide (sim0.head = 0)) (hf1 : f.2.1 = decide (sim1.head = 0))
    (hf2 : f.2.2 = decide (sim2.head = 0))
    (hSL_hold : (c.work stT).HoldsExact SL) (hstH : (c.work stT).head = 1)
    (hEL_hold : (c.work scT).HoldsExact EL) (hscH : (c.work scT).head = sc_p)
    (hdesc_wf : (c.work dsT).StartInvariant) (hdsH : (c.work dsT).head = dp)
    (hin : c.input.read ≠ Γ.start) (hout : c.output.read ≠ Γ.start) :
    ∃ c' t, t ≤ sc_p + 3 * SL.length + dp + 28 ∧
      bodyTM.reachesIn t c c' ∧
      c'.state = bodyDone ∧
      (c'.work stT).HoldsExact (EL.take SL.length) ∧ (c'.work stT).head = 1 ∧
      c'.work dsT = ⟨1, (c.work dsT).cells⟩ ∧
      (c'.work scT).HoldsExact [] ∧ (c'.work scT).head = 1 ∧
      VShift (sim0.move
          (if f.1 then Dir3.right
            else grpDir (cellBit ((c.work scT).cells (1 + SL.length + 4)))
              (cellBit ((c.work scT).cells (1 + SL.length + 5)))))
        (c'.work vIn) ∧
      VShift (sim1.writeAndMove
          (grpΓw (cellBit ((c.work scT).cells (1 + SL.length)))
            (cellBit ((c.work scT).cells (1 + SL.length + 1)))).toΓ
          (if f.2.1 then Dir3.right
            else grpDir (cellBit ((c.work scT).cells (1 + SL.length + 6)))
              (cellBit ((c.work scT).cells (1 + SL.length + 7)))))
        (c'.work vWk) ∧
      VShift (sim2.writeAndMove
          (grpΓw (cellBit ((c.work scT).cells (1 + SL.length + 2)))
            (cellBit ((c.work scT).cells (1 + SL.length + 3)))).toΓ
          (if f.2.2 then Dir3.right
            else grpDir (cellBit ((c.work scT).cells (1 + SL.length + 8)))
              (cellBit ((c.work scT).cells (1 + SL.length + 9)))))
        (c'.work vOut) ∧
      c'.input = c.input ∧ c'.output = c.output := by
  have hE_wns := (Tape.HoldsExact.startInvariant hEL_hold).2
  have hS_wns := (Tape.HoldsExact.startInvariant hSL_hold).2
  have hW_wns := hdesc_wf.2
  have hst_read : (c.work stT).read ≠ Γ.start := by
    rw [Tape.read, hstH]; exact hS_wns 1 (by omega)
  have hds_read : (c.work dsT).read ≠ Γ.start := by
    rw [Tape.read, hdsH]; exact hW_wns dp hdp
  have hr0 := h0.read_ne_start hwf0
  have hr1 := h1.read_ne_start hwf1
  have hr2 := h2.read_ne_start hwf2
  -- appRewScr: rewind the scratch
  obtain ⟨c₁, hr₁, hst₁, hwtSc₁, hin₁, hout₁, hoth₁⟩ :=
    rewStep_loop (cur := appRewScr f) (next := appQ' f) (t := scT)
      (fun hcon => nomatch hcon) (arm_appRewScr · · · f)
      (c.work scT).cells hEL_hold.1 hE_wns sc_p c hst rfl hscH hin hout
      (fun i hi => by
        rcases i with ⟨iv, hv⟩
        rcases iv with _ | _ | _ | _ | _ | _ | m
        · exact hr0
        · exact hr1
        · exact hr2
        · exact hst_read
        · exact hds_read
        · exact absurd rfl hi
        · exact absurd hv (by omega))
  -- appQ': overwrite the state tape with the new-state field
  obtain ⟨c₂, hr₂, hst₂, hwtS₂, hwtSc₂, hin₂, hout₂, hoth₂⟩ :=
    appQ'_loop (f := f) (c.work scT).cells hE_wns
      SL.length (c.work stT).cells hS_wns 1 1 (by omega) (by omega)
      (fun j hj => by
        rw [show 1 + j = j + 1 by omega, Tape.HoldsExact.cells_lt hSL_hold hj]
        intro hcon
        exact hSL_nb _ (List.getElem_mem hj) (Γw.toΓ_eq_blank.mp hcon))
      (by
        rw [show 1 + SL.length = SL.length + 1 by omega]
        exact Tape.HoldsExact.cells_ge hSL_hold (Nat.le_refl _))
      c₁ hst₁
      (by rw [hoth₁ stT (by decide)]) (by rw [hoth₁ stT (by decide), hstH])
      (by rw [hwtSc₁]) (by rw [hwtSc₁])
      (by rw [hin₁]; exact hin) (by rw [hout₁]; exact hout)
      (fun i hiS hiSc => by
        rw [hoth₁ i hiSc]
        rcases i with ⟨iv, hv⟩
        rcases iv with _ | _ | _ | _ | _ | _ | m
        · exact hr0
        · exact hr1
        · exact hr2
        · exact absurd rfl hiS
        · exact hds_read
        · exact absurd rfl hiSc
        · exact absurd hv (by omega))
  -- appAct: decode the five groups and act on the virtual tapes
  obtain ⟨c₃, hr₃, hst₃, hv0₃, hv1₃, hv2₃, hstT₃, hdsT₃, hwtSc₃, hin₃, hout₃⟩ :=
    appAct_all (c := c₂) (f := f) (E := (c.work scT).cells) (e := 1 + SL.length)
      (by rw [hoth₂ vIn (by decide) (by decide), hoth₁ vIn (by decide)]; exact h0)
      (by rw [hoth₂ vWk (by decide) (by decide), hoth₁ vWk (by decide)]; exact h1)
      (by rw [hoth₂ vOut (by decide) (by decide), hoth₁ vOut (by decide)]; exact h2)
      hwf0 hwf1 hwf2 hf0 hf1 hf2 hst₂
      (by rw [hwtSc₂]) (by rw [hwtSc₂]) (by omega) hE_wns
      (by rw [hwtS₂]
          dsimp only [Tape.read]
          rw [ite_eq_right (by omega)]
          exact hS_wns (1 + SL.length) (by omega))
      (by rw [hoth₂ dsT (by decide) (by decide), hoth₁ dsT (by decide)]
          exact hds_read)
      (by rw [hin₂, hin₁]; exact hin) (by rw [hout₂, hout₁]; exact hout)
  -- the overwritten state cells
  set U : ℕ → Γ := fun j => if 1 ≤ j ∧ j < 1 + SL.length then
      (c.work scT).cells (1 + (j - 1)) else (c.work stT).cells j with hU
  have hU0 : U 0 = Γ.start := by
    rw [hU]; dsimp only
    rw [ite_eq_right (by omega)]
    exact hSL_hold.1
  have hUns : ∀ j, 1 ≤ j → U j ≠ Γ.start := by
    intro j hj
    rw [hU]; dsimp only
    split
    · exact hE_wns _ (by omega)
    · exact hS_wns j hj
  -- StartInvariant of the transformed simulated tapes
  have hwf0' : (sim0.move
      (if f.1 then Dir3.right
        else grpDir (cellBit ((c.work scT).cells (1 + SL.length + 4)))
          (cellBit ((c.work scT).cells (1 + SL.length + 5))))).StartInvariant :=
    hwf0.move _
  have hwf1' : (sim1.writeAndMove
      (grpΓw (cellBit ((c.work scT).cells (1 + SL.length)))
        (cellBit ((c.work scT).cells (1 + SL.length + 1)))).toΓ
      (if f.2.1 then Dir3.right
        else grpDir (cellBit ((c.work scT).cells (1 + SL.length + 6)))
          (cellBit ((c.work scT).cells (1 + SL.length + 7))))).StartInvariant :=
    hwf1.writeAndMove _ _
  have hwf2' : (sim2.writeAndMove
      (grpΓw (cellBit ((c.work scT).cells (1 + SL.length + 2)))
        (cellBit ((c.work scT).cells (1 + SL.length + 3)))).toΓ
      (if f.2.2 then Dir3.right
        else grpDir (cellBit ((c.work scT).cells (1 + SL.length + 8)))
          (cellBit ((c.work scT).cells (1 + SL.length + 9))))).StartInvariant :=
    hwf2.writeAndMove _ _
  -- cleanup
  obtain ⟨c₄, hr₄, hst₄, hscHold₄, hscHead₄, hwtS₄, hwtD₄, hoth₄, hin₄, hout₄⟩ :=
    cleanupPhase c₃ (c.work scT).cells U (c.work dsT).cells
      (1 + SL.length + 10) (1 + SL.length) dp (by omega) hdp hst₃
      hEL_hold.1 hE_wns
      (fun j hj => by
        rw [show j = (j - 1) + 1 by omega]
        exact Tape.HoldsExact.cells_ge hEL_hold (by omega))
      (by rw [hwtSc₃]) (by rw [hwtSc₃])
      hU0 hUns
      (by rw [hstT₃, hwtS₂]) (by rw [hstT₃, hwtS₂])
      hdesc_wf.1 hW_wns
      (by rw [hdsT₃, hoth₂ dsT (by decide) (by decide), hoth₁ dsT (by decide)])
      (by rw [hdsT₃, hoth₂ dsT (by decide) (by decide), hoth₁ dsT (by decide), hdsH])
      (by rw [hin₃, hin₂, hin₁]; exact hin)
      (by rw [hout₃, hout₂, hout₁]; exact hout)
      (fun i hiS hiD hiSc => by
        rcases i with ⟨iv, hv⟩
        rcases iv with _ | _ | _ | _ | _ | _ | m
        · exact hv0₃.read_ne_start hwf0'
        · exact hv1₃.read_ne_start hwf1'
        · exact hv2₃.read_ne_start hwf2'
        · exact absurd rfl hiS
        · exact absurd rfl hiD
        · exact absurd rfl hiSc
        · exact absurd hv (by omega))
  refine ⟨c₄,
    (sc_p + 1) + (SL.length + 1) + 10
      + ((1 + SL.length + 10 + 1) + (1 + SL.length + 1) + (dp + 1)),
    by omega,
    reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _ hr₁ hr₂) hr₃) hr₄,
    hst₄, ?_, ?_, hwtD₄, hscHold₄, hscHead₄, ?_, ?_, ?_,
    by rw [hin₄, hin₃, hin₂, hin₁], by rw [hout₄, hout₃, hout₂, hout₁]⟩
  · -- state tape holds the value's first |SL| cells
    rw [hwtS₄]
    refine ⟨hU0, fun i => ?_⟩
    show U (i + 1) = _
    rw [hU]
    dsimp only
    by_cases hi : i < SL.length
    · rw [ite_eq_left (by omega), dite_eq_left (by
        rw [List.length_take]
        omega),
        show 1 + (i + 1 - 1) = i + 1 by omega,
        Tape.HoldsExact.cells_lt hEL_hold (by omega)]
      congr 1
      exact (List.getElem_take ..).symm
    · rw [ite_eq_right (by omega), dite_eq_right (by rw [List.length_take]; omega),
        show i + 1 = i + 1 by rfl]
      exact Tape.HoldsExact.cells_ge hSL_hold (by omega)
  · rw [hwtS₄]
  · rw [hoth₄ vIn (by decide) (by decide) (by decide)]
    exact hv0₃
  · rw [hoth₄ vWk (by decide) (by decide) (by decide)]
    exact hv1₃
  · rw [hoth₄ vOut (by decide) (by decide) (by decide)]
    exact hv2₃

end HcPhase

end TM.UTMBody

end Complexity
