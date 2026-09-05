/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.NLSearchAssemble
public import Complexitylib.Classes.P.NormalForm
public import Complexitylib.Classes.P.DecisionFn

/-!
# A language in `P` has a polynomial-time verdict function

⚠️ Unreviewed by Bolton

`Complexity.mem_P_of_decisionFn` puts a language in `P` given a verdict function in `FP`. This
file is the converse: a language in `P` *has* such a function. That is what a development needs
whenever a polynomial-time predicate has to be consulted from inside another polynomial-time
computation — the predicate arrives as a machine, and only a function can be composed.

The function is the machine's own run, carried out inside the algebra: `Cobham.initFn` encodes
the initial configuration, `Cobham.stepFn` advances it, and after the machine's time bound many
steps `Complexity.acceptFlag` reads the verdict cell off the resulting code. Halted
configurations are fixed points of the encoded step, so running for exactly the time bound is
safe however early the machine stops.

## Main definitions

- `Complexity.TM.stepOrStay`, `Complexity.TM.runTo` — the run as a total iteration
- `Complexity.codeStep` — the encoded step with its ruler carried alongside
- `Complexity.pVerdict` — the verdict function

## Main results

- `Complexity.runCode_eq` — the encoded run is the code of the real one
- `Complexity.pVerdict_eq_true_iff` — the verdict function decides the language
- `Complexity.pVerdict_mem_FP` — and it is polynomial-time
- `Complexity.exists_decisionFn_of_mem_P` — hence every language in `P` has one
-/

@[expose] public section

namespace Complexity

open Cobham

variable {k : ℕ}

/-! ## The run as a total iteration -/

namespace TM

/-- One step of a deterministic machine, staying put once it has halted. -/
def stepOrStay (tm : TM k) (c : Cfg k tm.Q) : Cfg k tm.Q := (tm.step c).getD c

theorem stepOrStay_of_halted (tm : TM k) {c : Cfg k tm.Q} (h : c.state = tm.qhalt) :
    tm.stepOrStay c = c := by
  rw [stepOrStay, TM.step, ite_eq_left h]
  rfl

theorem stepOrStay_of_step (tm : TM k) {c c' : Cfg k tm.Q} (h : tm.step c = some c') :
    tm.stepOrStay c = c' := by
  rw [stepOrStay, h]
  rfl

/-- The configuration after `n` steps, halted ones counting as no-ops. -/
def runTo (tm : TM k) (x : List Bool) (n : ℕ) : Cfg k tm.Q :=
  (tm.stepOrStay)^[n] (tm.initCfg x)

@[simp] theorem runTo_zero (tm : TM k) (x : List Bool) : tm.runTo x 0 = tm.initCfg x := rfl

theorem runTo_succ (tm : TM k) (x : List Bool) (n : ℕ) :
    tm.runTo x (n + 1) = tm.stepOrStay (tm.runTo x n) := by
  rw [runTo, runTo, Function.iterate_succ_apply']

/-- A bounded walk is exactly that many total steps. -/
theorem iterate_stepOrStay_of_reachesIn (tm : TM k) :
    ∀ {t : ℕ} {c c' : Cfg k tm.Q}, tm.reachesIn t c c' → (tm.stepOrStay)^[t] c = c' := by
  intro t c c' h
  induction h with
  | zero => rfl
  | step hstep _ ih =>
      rw [Function.iterate_succ_apply, stepOrStay_of_step tm hstep]
      exact ih

/-- A halted configuration is a fixed point of the total step. -/
theorem iterate_stepOrStay_halted (tm : TM k) {c : Cfg k tm.Q} (h : c.state = tm.qhalt) :
    ∀ n, (tm.stepOrStay)^[n] c = c := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, stepOrStay_of_halted tm h, ih]

/-- Once the machine has halted, the run stays where it stopped. -/
theorem runTo_of_halted (tm : TM k) (x : List Bool) {t : ℕ} {c : Cfg k tm.Q}
    (h : tm.reachesIn t (tm.initCfg x) c) (hh : c.state = tm.qhalt) {n : ℕ} (hn : t ≤ n) :
    tm.runTo x n = c := by
  have ht : (tm.stepOrStay)^[t] (tm.initCfg x) = c := iterate_stepOrStay_of_reachesIn tm h
  rw [runTo, show n = n - t + t from by omega, Function.iterate_add_apply, ht,
    iterate_stepOrStay_halted tm hh]

/-- Every point of the run is reached by a walk no longer than the index. -/
theorem exists_reachesIn_runTo (tm : TM k) (x : List Bool) :
    ∀ n, ∃ t ≤ n, tm.reachesIn t (tm.initCfg x) (tm.runTo x n) := by
  intro n
  induction n with
  | zero => exact ⟨0, le_rfl, TM.reachesIn.zero⟩
  | succ n ih =>
      obtain ⟨t, ht, hr⟩ := ih
      rw [runTo_succ]
      rcases hs : tm.step (tm.runTo x n) with _ | c'
      · refine ⟨t, by omega, ?_⟩
        rw [stepOrStay, hs]
        exact hr
      · refine ⟨t + 1, by omega, ?_⟩
        rw [stepOrStay_of_step tm hs]
        exact tm.reachesIn_trans hr (TM.reachesIn.step hs TM.reachesIn.zero)

/-- The left-end markers survive any walk. -/
theorem startInvariant_of_reachesIn (tm : TM k) :
    ∀ {t : ℕ} {c c' : Cfg k tm.Q}, tm.reachesIn t c c' →
      c.input.StartInvariant → (∀ i, (c.work i).StartInvariant) → c.output.StartInvariant →
      c'.input.StartInvariant ∧ (∀ i, (c'.work i).StartInvariant) ∧
        c'.output.StartInvariant := by
  intro t c c' h
  induction h with
  | zero => exact fun a b c => ⟨a, b, c⟩
  | step hstep _ ih =>
      intro hi hw ho
      obtain ⟨hi', hw', ho'⟩ := Tape.StartInvariant.step _ hstep hi hw ho
      exact ih hi' hw' ho'

/-- Every point of the run is inside the window a time bound gives. -/
theorem codeInv_runTo (tm : TM k) (x : List Bool) {W n : ℕ} (hn : n ≤ W) :
    CodeInv W (tm.runTo x n) := by
  obtain ⟨t, ht, hr⟩ := exists_reachesIn_runTo tm x n
  obtain ⟨hi, hw, ho⟩ := startInvariant_of_reachesIn tm hr
    (Tape.StartInvariant.init_ofBool x) (fun _ => Tape.StartInvariant.init_nil)
    Tape.StartInvariant.init_nil
  obtain ⟨hin, hout, hwork⟩ := TM.head_le_of_reachesIn tm hr
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩ <;>
    · rw [cfgTapes, List.mem_cons, List.mem_cons, List.mem_ofFn] at hs
      rcases hs with rfl | rfl | ⟨i, rfl⟩
      · first | exact hi | omega
      · first | exact ho | omega
      · first | exact hw i | (have := hwork i; omega)

end TM

/-! ## The encoded run -/

/-- The encoded step, carrying its ruler alongside the code. -/
noncomputable def codeStep (tm : TM k) (w : List Bool) : List Bool :=
  pair (pairFst w) (stepFn tm (pairFst w) (pairSnd w))

theorem codeStep_pair (tm : TM k) (R z : List Bool) :
    codeStep tm (pair R z) = pair R (stepFn tm R z) := by
  rw [codeStep, pairFst_pair, pairSnd_pair]

theorem codeStep_iterate (tm : TM k) (R z : List Bool) :
    ∀ n, (codeStep tm)^[n] (pair R z) = pair R ((stepFn tm R)^[n] z) := by
  intro n
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, codeStep_pair, ih, Function.iterate_succ_apply]

theorem codeStep_mem_FP (tm : TM k) : codeStep tm ∈ FP := by
  have hfst : (fun z : List Bool => pairFst z) ∈ FP := Cobham.fstBlock_mem_FP
  have hsnd : (fun z : List Bool => pairSnd z) ∈ FP := Cobham.sndBlock_mem_FP
  have hstep : (fun w => stepFn tm (pairFst w) (pairSnd w)) ∈ FP :=
    binFn_mem_FP (g := stepFn tm)
      (Cobham.stepFn_mem tm (Cobham.proj 0) (Cobham.proj 1)) hfst hsnd
  exact Cobham.pairFn_mem_FP hfst hstep

/-- **The encoded run is the code of the real one.** -/
theorem runCode_eq (tm : TM k) (W : ℕ) (hq : Fintype.card tm.Q ≤ blockWidth W)
    (x : List Bool) (hx : x.length ≤ W) :
    ∀ n ≤ W, (stepFn tm (blockRuler W))^[n] (Cobham.initFn tm (blockRuler W) x)
      = Cobham.cfgCode W (tm.runTo x n) := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [Function.iterate_zero_apply, Cobham.initFn_eq tm W x hx, TM.runTo_zero]
  | succ n ih =>
      intro hn
      have hinv : CodeInv W (tm.runTo x n) := TM.codeInv_runTo tm x (by omega)
      have hheads : ∀ t ∈ cfgTapes (tm.runTo x n), t.head ≤ W := hinv.head
      rw [Function.iterate_succ_apply', ih (by omega), TM.runTo_succ]
      rcases hs : tm.step (tm.runTo x n) with _ | c'
      · have hhalt : (tm.runTo x n).state = tm.qhalt := by
          by_contra hc
          simp [TM.step, hc] at hs
        rw [TM.stepOrStay, hs]
        exact stepFn_halted tm hhalt hq hheads
      · rw [TM.stepOrStay_of_step tm hs]
        exact stepFn_eq tm hs hq hheads (hinv.start _ (by simp [cfgTapes]))
          (fun i => hinv.start _ (by
            rw [cfgTapes]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩))))
          (stepActs_forall₂ tm _ hinv.start hheads)

/-! ## Reading the verdict off a code -/

/-- **The test decides acceptance**, for a deterministic machine. -/
theorem acceptFlag_cfgCode_tm (tm : TM k) (W : ℕ) (c : Cfg k tm.Q)
    (hq : Fintype.card tm.Q ≤ blockWidth W) (hinv : CodeInv W c) (hW : 1 ≤ W)
    (ruler : List Bool) (hruler : W ≤ ruler.length) :
    acceptFlag (stateCode tm.qhalt) (blockRuler W) ruler (Cobham.cfgCode W c) = [true] ↔
      c.state = tm.qhalt ∧ c.output.cells 1 = Γ.one := by
  have hout : c.output.StartInvariant := hinv.start _ (by simp [cfgTapes])
  have houth : c.output.head ≤ W := hinv.head _ (by simp [cfgTapes])
  have hstate : (blockAt (blockRuler W) (Cobham.cfgCode W c) 0).take
      (stateCode tm.qhalt).length = stateCode c.state := by
    rw [stateCode_length]
    exact state_of_cfgCode W c hq
  have hverdict : verdictSym (blockRuler W)
      (rewindCode (blockRuler W) ruler (outPair (blockRuler W) (Cobham.cfgCode W c)))
      = symCode (c.output.cells 1) := by
    rw [outPair_cfgCode, rewindCode_pairCode W c.output hout houth ruler hruler,
      verdictSym_rewound W c.output hW]
  rw [acceptFlag, andBit_eq_true_iff (eqFlag_flag _ _) (eqFlag_flag _ _),
    eqFlag_eq_true_iff, eqFlag_eq_true_iff, hstate, hverdict]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨stateCode_injective h1, symCode_injective h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1], by rw [h2]⟩

/-! ## The verdict function -/

/-- The verdict a deterministic machine reaches, computed inside the algebra. -/
noncomputable def pVerdict (tm : TM k) (wp tp : Polynomial ℕ) (x : List Bool) : List Bool :=
  acceptFlag (stateCode tm.qhalt) (polyRuler (2 * wp + 2) x)
    (wideRuler (codeBlocks k) (polyRuler (2 * wp + 2) x))
    (pairSnd ((codeStep tm)^[(polyRuler tp x).length]
      (pair (polyRuler (2 * wp + 2) x)
        (Cobham.initFn tm (polyRuler (2 * wp + 2) x) x))))

theorem pVerdict_flag (tm : TM k) (wp tp : Polynomial ℕ) (x : List Bool) :
    pVerdict tm wp tp x = [true] ∨ pVerdict tm wp tp x = [false] :=
  acceptFlag_flag _ _ _ _

/-- **The verdict function decides the language.** -/
theorem pVerdict_eq_true_iff (tm : TM k) {L : Language} (wp tp : Polynomial ℕ)
    (hdec : tm.DecidesInTime L fun n => tp.eval n)
    (hwp : ∀ n, n + tp.eval n + 1 ≤ wp.eval n)
    (hq : ∀ n, Fintype.card tm.Q ≤ blockWidth (wp.eval n)) (x : List Bool) :
    pVerdict tm wp tp x = [true] ↔ x ∈ L := by
  set W := wp.eval x.length with hW
  have hbound := hwp x.length
  have hxW : x.length ≤ W := by omega
  have hW1 : 1 ≤ W := by omega
  have hR : polyRuler (2 * wp + 2) x = blockRuler W := (blockRuler_eq_polyRuler wp x).symm
  have hruler : W ≤ (wideRuler (codeBlocks k) (blockRuler W)).length := by
    rw [wideRuler_length, blockRuler_length, blockWidth]
    have hcb : 1 ≤ codeBlocks k := by rw [codeBlocks]; omega
    calc W ≤ 1 * (2 * (W + 1)) := by omega
      _ ≤ codeBlocks k * (2 * (W + 1)) := Nat.mul_le_mul_right _ hcb
  obtain ⟨c, t, htT, hreach, hhalt, hone, hzero⟩ := hdec x
  have hrun : tm.runTo x (tp.eval x.length) = c :=
    TM.runTo_of_halted tm x hreach hhalt (by simpa using htT)
  have hcode : pairSnd ((codeStep tm)^[(polyRuler tp x).length]
      (pair (polyRuler (2 * wp + 2) x) (Cobham.initFn tm (polyRuler (2 * wp + 2) x) x)))
      = Cobham.cfgCode W c := by
    rw [codeStep_iterate, pairSnd_pair, polyRuler_length, hR,
      runCode_eq tm W (hq x.length) x hxW _ (by omega), hrun]
  rw [pVerdict, hcode, hR,
    acceptFlag_cfgCode_tm tm W c (hq x.length)
      (hrun ▸ TM.codeInv_runTo tm x (n := tp.eval x.length) (by omega)) hW1 _ hruler]
  constructor
  · rintro ⟨_, hv⟩
    by_contra hx
    rw [hzero hx] at hv
    exact absurd hv (by decide)
  · intro hx
    exact ⟨hhalt, hone hx⟩

/-! ## The verdict function is polynomial-time -/

/-- The encoded run never grows past the code width. -/
theorem stepFn_iterate_length_le (tm : TM k) (R z : List Bool)
    (hz : z.length ≤ codeBlocks k * R.length) :
    ∀ n, ((stepFn tm R)^[n] z).length ≤ codeBlocks k * R.length := by
  intro n
  induction n generalizing z with
  | zero => simpa using hz
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih _ (by rw [codeBlocks] at hz ⊢; exact stepFn_length_le tm R z hz)

/-- The width the whole packed state stays inside. -/
noncomputable def pStateBound (k : ℕ) (wp : Polynomial ℕ) : Polynomial ℕ :=
  2 * (2 * wp + 2) + 2 + Polynomial.C (codeBlocks k) * (2 * wp + 2)

theorem pStateBound_eval (k : ℕ) (wp : Polynomial ℕ) (n : ℕ) :
    (pStateBound k wp).eval n
      = 2 * (2 * wp.eval n + 2) + 2 + codeBlocks k * (2 * wp.eval n + 2) := by
  simp [pStateBound]

/-- **The verdict function is polynomial-time.** -/
theorem pVerdict_mem_FP (tm : TM k) (wp tp : Polynomial ℕ)
    (hwp : ∀ n, n ≤ wp.eval n) : pVerdict tm wp tp ∈ FP := by
  have hx : (fun x : List Bool => x) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hRf : (fun x => polyRuler (2 * wp + 2) x) ∈ FP := polyRulerFn_mem_FP _ hx
  have hRlen : ∀ x : List Bool,
      (polyRuler (2 * wp + 2) x).length = 2 * wp.eval x.length + 2 := by
    intro x
    rw [polyRuler_length]
    simp
  have hinit : (fun x => pair (polyRuler (2 * wp + 2) x)
      (Cobham.initFn tm (polyRuler (2 * wp + 2) x) x)) ∈ FP :=
    Cobham.pairFn_mem_FP hRf
      (binFn_mem_FP (g := Cobham.initFn tm)
        (Cobham.initFn_mem tm (Cobham.proj 0) (Cobham.proj 1)) hRf hx)
  have hruler : (fun x => polyRuler tp x) ∈ FP := polyRulerFn_mem_FP _ hx
  have hwidth : (fun x => polyRuler (pStateBound k wp) x) ∈ FP := polyRulerFn_mem_FP _ hx
  have hbound : ∀ x : List Bool, ∀ n ≤ (polyRuler tp x).length,
      ((codeStep tm)^[n] (pair (polyRuler (2 * wp + 2) x)
        (Cobham.initFn tm (polyRuler (2 * wp + 2) x) x))).length
        ≤ (polyRuler (pStateBound k wp) x).length := by
    intro x n _
    have hR : polyRuler (2 * wp + 2) x = blockRuler (wp.eval x.length) :=
      (blockRuler_eq_polyRuler wp x).symm
    have hinitlen : (Cobham.initFn tm (polyRuler (2 * wp + 2) x) x).length
        ≤ codeBlocks k * (polyRuler (2 * wp + 2) x).length := by
      rw [hR, Cobham.initFn_eq tm _ x (hwp x.length), cfgCode_length]
    have := stepFn_iterate_length_le tm (polyRuler (2 * wp + 2) x) _ hinitlen n
    rw [codeStep_iterate, pair_length, hRlen x, polyRuler_length, pStateBound_eval]
    rw [hRlen x] at this
    omega
  have hiter := Cobham.iterate_mem_FP (codeStep_mem_FP tm) hinit hruler hwidth hbound
  have hcode : (fun x => pairSnd ((codeStep tm)^[(polyRuler tp x).length]
      (pair (polyRuler (2 * wp + 2) x)
        (Cobham.initFn tm (polyRuler (2 * wp + 2) x) x)))) ∈ FP := by
    have := mem_FP_comp hiter Cobham.sndBlock_mem_FP
    exact this
  exact acceptFlagFn_mem_FP _ hRf (wideRulerFn_mem_FP hRf (codeBlocks k)) hcode

/-! ## The bridge -/

/-- **Every language in `P` has a polynomial-time verdict function.** This is the converse of
`Complexity.mem_P_of_decisionFn_bool`: a polynomial-time predicate can always be consulted from
inside another polynomial-time computation. -/
theorem exists_decisionFn_of_mem_P {L : Language} (hL : L ∈ P) :
    ∃ g : List Bool → Bool, (fun x => [g x]) ∈ FP ∧ ∀ x, x ∈ L ↔ g x = true := by
  obtain ⟨k, tm, tp, hdec⟩ := mem_P_iff_decidesInTime_polynomial.mp hL
  set wp : Polynomial ℕ :=
    Polynomial.X + tp + Polynomial.C 1 + Polynomial.C (Fintype.card tm.Q) with hwpdef
  have hwe : ∀ n, wp.eval n = n + tp.eval n + 1 + Fintype.card tm.Q := by
    intro n
    rw [hwpdef]
    simp
  have hwp : ∀ n, n + tp.eval n + 1 ≤ wp.eval n := by
    intro n
    rw [hwe]
    omega
  have hq : ∀ n, Fintype.card tm.Q ≤ blockWidth (wp.eval n) := by
    intro n
    rw [blockWidth, hwe]
    omega
  refine ⟨fun x => (pVerdict tm wp tp x).headD false, ?_, fun x => ?_⟩
  · have heq : (fun x => [(pVerdict tm wp tp x).headD false]) = pVerdict tm wp tp := by
      funext x
      rcases pVerdict_flag tm wp tp x with h | h <;> rw [h] <;> rfl
    rw [heq]
    exact pVerdict_mem_FP tm wp tp fun n => by rw [hwe]; omega
  · rw [← pVerdict_eq_true_iff tm wp tp hdec hwp hq x]
    rcases pVerdict_flag tm wp tp x with h | h <;> simp [h]

end Complexity
