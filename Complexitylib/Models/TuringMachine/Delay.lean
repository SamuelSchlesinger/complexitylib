/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Mathlib.Data.Fintype.Prod
public import Complexitylib.Models.TuringMachine.Combinators
public import Complexitylib.Models.TuringMachine.Internal
public import Complexitylib.Models.TuringMachine.Combinators.Internal.SentinelStep

/-!
# Delaying a nondeterministic machine's first choice

A machine begins with every head on `▷`, and `NTM.δ_right_of_start` forces that first transition
to move them all right. The transition may nevertheless *branch*: `δ false` and `δ true` can send
the machine to different states. That is a nuisance for any construction that has to enter a
simulated machine after the compulsory `▷`-step — a composed machine can never hand a stage a
head at cell zero — because the entry state would then fix the first choice.

`NTM.delayNTM` removes the branch. It spends one extra step doing nothing but the compulsory
move, and only *then* consults the choice bit, jumping to whichever state the source machine's
first transition would have produced. Its first step is therefore choice-independent, while its
subsequent behaviour is the source machine's, one step later.

## Main results

- `NTM.delayNTM` — the source machine with its first choice deferred by one step
- `NTM.delayNTM_trace_embed` — after the delay, the two machines run in lockstep
- `NTM.delayNTM_trace_two_initCfg` — two steps of the delayed machine reproduce one of the source
- `NTM.delayNTM_allPathsHaltIn` — the delay costs two steps
- `NTM.delayNTM_acceptCount` — the delay doubles the count of accepting paths
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {n : ℕ}

/-- **The source machine with its first choice deferred.** The extra state `Sum.inl ()` is both
the start state and the state the machine sits in after the compulsory `▷`-step; the two are
distinguished by the input head's symbol, which is `▷` exactly on the first step. -/
def delayNTM (tm : NTM n) : NTM n :=
  letI : Fintype tm.Q := tm.finQ
  letI : DecidableEq tm.Q := tm.decEq
  { Q := Unit ⊕ tm.Q,
    decEq := inferInstance,
    finQ := inferInstance,
    qstart := Sum.inl (),
    qhalt := Sum.inr tm.qhalt,
    δ := fun b q iHead wHeads oHead =>
      match q with
      | Sum.inl () =>
        ( if iHead = Γ.start then Sum.inl ()
          else Sum.inr (tm.δ b tm.qstart Γ.start (fun _ => Γ.start) Γ.start).1,
          fun i => TM.readBackWrite (wHeads i),
          TM.readBackWrite oHead,
          TM.idleDir iHead,
          fun i => TM.idleDir (wHeads i),
          TM.idleDir oHead )
      | Sum.inr q' =>
        let r := tm.δ b q' iHead wHeads oHead
        (Sum.inr r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2),
    δ_right_of_start := by
      intro b q iHead wHeads oHead
      match q with
      | Sum.inl () =>
        exact ⟨fun h => by simp [TM.idleDir, h], fun i h => by simp [TM.idleDir, h],
          fun h => by simp [TM.idleDir, h]⟩
      | Sum.inr q' =>
        exact tm.δ_right_of_start b q' iHead wHeads oHead }

@[simp] theorem delayNTM_qhalt (tm : NTM n) : (delayNTM tm).qhalt = Sum.inr tm.qhalt := rfl

@[simp] theorem delayNTM_qstart (tm : NTM n) : (delayNTM tm).qstart = Sum.inl () := rfl

/-- A source configuration, viewed as one of the delayed machine's. -/
def delayEmbed (tm : NTM n) (c : Cfg n tm.Q) : Cfg n (delayNTM tm).Q where
  state := Sum.inr c.state
  input := c.input
  work := c.work
  output := c.output

theorem delayEmbed_halted_iff (tm : NTM n) (c : Cfg n tm.Q) :
    (delayEmbed tm c).state = (delayNTM tm).qhalt ↔ c.state = tm.qhalt := by
  exact ⟨fun h => by injection h, fun h => by rw [delayEmbed, delayNTM_qhalt, h]⟩

/-- **One step, transported.** On an embedded configuration the delayed machine's transition is
literally the source's, wrapped. -/
theorem delayNTM_trace_one_embed (tm : NTM n) (b : Bool) (c : Cfg n tm.Q) :
    (delayNTM tm).trace 1 (fun _ => b) (delayEmbed tm c)
      = delayEmbed tm (tm.trace 1 (fun _ => b) c) := by
  by_cases hc : c.state = tm.qhalt
  · rw [NTM.trace, NTM.trace, ite_eq_left ((delayEmbed_halted_iff tm c).mpr hc), ite_eq_left hc]
  · rw [NTM.trace, NTM.trace, ite_eq_right (fun h => hc ((delayEmbed_halted_iff tm c).mp h)),
      ite_eq_right hc]
    rcases hr : tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read with
      ⟨q', ww, ow, iD, wD, oD⟩
    have hd : (delayNTM tm).δ b (delayEmbed tm c).state (delayEmbed tm c).input.read
        (fun i => ((delayEmbed tm c).work i).read) (delayEmbed tm c).output.read
        = (Sum.inr q', ww, ow, iD, wD, oD) := by
      show (delayNTM tm).δ b (Sum.inr c.state) c.input.read
        (fun i => (c.work i).read) c.output.read = _
      rw [show (delayNTM tm).δ b (Sum.inr c.state) c.input.read
          (fun i => (c.work i).read) c.output.read
          = (fun r => (Sum.inr r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2))
            (tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read) from rfl,
        hr]
    simp only [hd, hr]
    rfl

/-- **After the delay, the two machines run in lockstep.** Every trace from an embedded
configuration transports to the source machine's. -/
theorem delayNTM_trace_embed (tm : NTM n) :
    ∀ (T : ℕ) (choices : Fin T → Bool) (c : Cfg n tm.Q),
      (delayNTM tm).trace T choices (delayEmbed tm c)
        = delayEmbed tm (tm.trace T choices c) := by
  intro T
  induction T with
  | zero => intro _ _; rfl
  | succ T ih =>
      intro choices c
      rw [NTM.trace_succ (delayNTM tm) T choices (delayEmbed tm c),
        NTM.trace_succ tm T choices c, delayNTM_trace_one_embed, ih]


/-- **The sentinel step of a nondeterministic machine.** From any configuration whose heads are
at cell zero the reads are all `▷`, so the writes are no-ops and every head moves right; only the
state depends on the choice bit. -/
theorem trace_one_of_heads_zero (tm : NTM n) (b : Bool) (c : Cfg n tm.Q)
    (hne : c.state ≠ tm.qhalt)
    (hin : c.input.head = 0) (hwork : ∀ i, (c.work i).head = 0) (hout : c.output.head = 0)
    (hin0 : c.input.cells 0 = Γ.start) (hwork0 : ∀ i, (c.work i).cells 0 = Γ.start)
    (hout0 : c.output.cells 0 = Γ.start) :
    tm.trace 1 (fun _ => b) c =
      ⟨(tm.δ b c.state Γ.start (fun _ => Γ.start) Γ.start).1,
        c.input.move Dir3.right, fun i => (c.work i).move Dir3.right,
        c.output.move Dir3.right⟩ := by
  have hri : c.input.read = Γ.start := by rw [Tape.read, hin]; exact hin0
  have hrw : ∀ i, (c.work i).read = Γ.start := by
    intro i; rw [Tape.read, hwork i]; exact hwork0 i
  have hro : c.output.read = Γ.start := by rw [Tape.read, hout]; exact hout0
  have hdirs := tm.δ_right_of_start b c.state Γ.start (fun _ => Γ.start) Γ.start
  rw [NTM.trace, ite_eq_right hne]
  simp only [hri, hro, funext hrw]
  rcases hr : tm.δ b c.state Γ.start (fun _ => Γ.start) Γ.start with ⟨q', ww, ow, iD, wD, oD⟩
  rw [hr] at hdirs
  simp only [hr, NTM.trace]
  refine Cfg.ext rfl ?_ ?_ ?_
  · rw [hdirs.1 rfl]
  · funext i
    show (c.work i).writeAndMove (ww i).toΓ (wD i) = (c.work i).move Dir3.right
    rw [TM.writeAndMove_of_head_zero _ _ _ (hwork i), hdirs.2.1 i rfl]
  · show c.output.writeAndMove ow.toΓ oD = c.output.move Dir3.right
    rw [TM.writeAndMove_of_head_zero _ _ _ hout, hdirs.2.2 rfl]

/-- **The delayed machine's second step.** Sitting in the extra state with every head off the
marker, it consults the choice bit, jumps to the state the source machine's first transition would
have produced, and leaves every tape exactly as it is. -/
theorem delayNTM_trace_one_pending (tm : NTM n) (b : Bool) (c : Cfg n (delayNTM tm).Q)
    (hstate : c.state = Sum.inl ())
    (hin : c.input.read ≠ Γ.start) (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    (delayNTM tm).trace 1 (fun _ => b) c =
      ⟨Sum.inr (tm.δ b tm.qstart Γ.start (fun _ => Γ.start) Γ.start).1,
        c.input, c.work, c.output⟩ := by
  have hnh : c.state ≠ (delayNTM tm).qhalt := by rw [hstate]; nofun
  rw [NTM.trace, ite_eq_right hnh]
  have hd : (delayNTM tm).δ b c.state c.input.read (fun i => (c.work i).read) c.output.read
      = (Sum.inr (tm.δ b tm.qstart Γ.start (fun _ => Γ.start) Γ.start).1,
        fun i => TM.readBackWrite ((c.work i).read), TM.readBackWrite c.output.read,
        TM.idleDir c.input.read, fun i => TM.idleDir ((c.work i).read),
        TM.idleDir c.output.read) := by
    rw [hstate]
    show (if c.input.read = Γ.start then (Sum.inl () : Unit ⊕ tm.Q)
      else Sum.inr (tm.δ b tm.qstart Γ.start (fun _ => Γ.start) Γ.start).1, _, _, _, _, _) = _
    rw [ite_eq_right hin]
  simp only [hd, NTM.trace]
  refine Cfg.ext rfl ?_ ?_ ?_
  · exact TM.transitionInput_eq_self hin
  · funext i
    exact TM.transitionTape_eq_self (hwork i)
  · exact TM.transitionTape_eq_self hout

/-- **Two steps of the delayed machine reproduce one step of the source.** The first step is the
compulsory move off the marker and ignores its choice bit; the second consumes the choice the
source machine would have made first. -/
theorem delayNTM_trace_two_initCfg (tm : NTM n) (x : List Bool)
    (hne : tm.qstart ≠ tm.qhalt) (choices : Fin 2 → Bool) :
    (delayNTM tm).trace 2 choices ((delayNTM tm).initCfg x)
      = delayEmbed tm (tm.trace 1 (fun _ => choices ⟨1, by omega⟩) (tm.initCfg x)) := by
  have hne2 : ((delayNTM tm).initCfg x).state ≠ (delayNTM tm).qhalt := nofun
  have hstep1 := trace_one_of_heads_zero (delayNTM tm) (choices ⟨0, by omega⟩)
    ((delayNTM tm).initCfg x) hne2 rfl (fun _ => rfl) rfl (Tape.init_cells_zero _)
    (fun _ => Tape.init_cells_zero _) (Tape.init_cells_zero _)
  have hδ1 : ((delayNTM tm).δ (choices ⟨0, by omega⟩) ((delayNTM tm).initCfg x).state
      Γ.start (fun _ => Γ.start) Γ.start).1 = Sum.inl () := by
    show (if (Γ.start : Γ) = Γ.start then (Sum.inl () : Unit ⊕ tm.Q)
      else Sum.inr (tm.δ (choices ⟨0, by omega⟩) tm.qstart Γ.start
        (fun _ => Γ.start) Γ.start).1) = Sum.inl ()
    rw [ite_eq_left rfl]
  rw [NTM.trace_two, hstep1, hδ1]
  have hinr : ((Tape.init (x.map Γ.ofBool)).move Dir3.right).read ≠ Γ.start :=
    Tape.init_ofBool_move_right_read_ne_start x
  have hblank : ((Tape.init ([] : List Γ)).move Dir3.right).read ≠ Γ.start := by
    rw [Tape.init_nil_move_right_read]
    nofun
  rw [delayNTM_trace_one_pending tm _ _ rfl hinr (fun _ => hblank) hblank]
  rw [trace_one_of_heads_zero tm (choices ⟨1, by omega⟩) (tm.initCfg x) hne rfl (fun _ => rfl) rfl
    (Tape.init_cells_zero _) (fun _ => Tape.init_cells_zero _) (Tape.init_cells_zero _)]
  rfl


/-- **A whole run of the delayed machine, from its initial configuration.** Two extra steps buy
one step of the source machine, and thereafter the two run in lockstep. -/
theorem delayNTM_trace_initCfg (tm : NTM n) (x : List Bool)
    (hne : tm.qstart ≠ tm.qhalt) (T : ℕ) (ch : Fin (T + 2) → Bool) :
    (delayNTM tm).trace (T + 2) ch ((delayNTM tm).initCfg x)
      = delayEmbed tm (tm.trace (T + 1) (Fin.tail ch) (tm.initCfg x)) := by
  rw [NTM.trace_add_two, delayNTM_trace_two_initCfg tm x hne, delayNTM_trace_embed,
    NTM.trace_succ tm T (Fin.tail ch) (tm.initCfg x)]
  rfl

/-- **The delay costs two steps.** Every path of the source machine that halts within `f |x|`
steps has its delayed counterpart halted within `f |x| + 2`. -/
theorem delayNTM_allPathsHaltIn (tm : NTM n) {f : ℕ → ℕ}
    (hall : tm.AllPathsHaltIn f) (hne : tm.qstart ≠ tm.qhalt) :
    (delayNTM tm).AllPathsHaltIn (fun m => f m + 2) := by
  intro x ch
  show ((delayNTM tm).trace (f x.length + 2) ch ((delayNTM tm).initCfg x)).state
    = (delayNTM tm).qhalt
  rw [delayNTM_trace_initCfg tm x hne (f x.length) ch]
  refine (delayEmbed_halted_iff tm _).mpr ?_
  have heq := tm.trace_mono (T := f x.length) (T' := f x.length + 1) (by omega)
    (choices := fun i => Fin.tail ch ⟨i.val, by omega⟩) (choices' := Fin.tail ch)
    (fun _ => rfl) (hall x _)
  rw [heq]
  exact hall x _

/-- **The delayed machine's accepting paths, counted.** Its first choice bit does nothing, so each
accepting path of the source machine lifts to exactly two of the delayed machine's. -/
theorem delayNTM_acceptCount (tm : NTM n) (x : List Bool)
    (hne : tm.qstart ≠ tm.qhalt) (T : ℕ) :
    (delayNTM tm).acceptCount x (T + 2) = 2 * tm.acceptCount x (T + 1) := by
  classical
  set P : (Fin (T + 1) → Bool) → Prop := fun g =>
    (tm.trace (T + 1) g (tm.initCfg x)).state = tm.qhalt ∧
    (tm.trace (T + 1) g (tm.initCfg x)).output.cells 1 = Γ.one with hP
  let : DecidableEq tm.Q := tm.decEq
  let : DecidablePred P := fun _ => inferInstanceAs (Decidable (_ ∧ _))
  have hkey := delayNTM_trace_initCfg tm x hne T
  have hfilter : ∀ ch : Fin (T + 2) → Bool,
      (((delayNTM tm).trace (T + 2) ch ((delayNTM tm).initCfg x)).state
          = (delayNTM tm).qhalt ∧
        ((delayNTM tm).trace (T + 2) ch ((delayNTM tm).initCfg x)).output.cells 1 = Γ.one)
      ↔ P (Fin.tail ch) := by
    intro ch
    rw [hkey ch, hP]
    exact and_congr (delayEmbed_halted_iff tm _) Iff.rfl
  have hcard : ∀ (Q : (Fin (T + 1) → Bool) → Prop) [DecidablePred Q],
      (Finset.univ.filter fun ch : Fin (T + 2) → Bool => Q (Fin.tail ch)).card
        = 2 * (Finset.univ.filter Q).card := by
    intro Q hQ
    have : DecidablePred Q := hQ
    have hf1 : Fintype {g : Fin (T + 1) → Bool // Q g} := Subtype.fintype _
    have hf2 : Fintype {ch : Fin (T + 2) → Bool // Q (Fin.tail ch)} := Subtype.fintype _
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    rw [Fintype.card_congr (Equiv.mk
      (fun ch : {ch : Fin (T + 2) → Bool // Q (Fin.tail ch)} =>
        (ch.1 0, (⟨Fin.tail ch.1, ch.2⟩ : {g : Fin (T + 1) → Bool // Q g})))
      (fun p : Bool × {g : Fin (T + 1) → Bool // Q g} =>
        (⟨Fin.cons p.1 p.2.1, by rw [Fin.tail_cons]; exact p.2.2⟩ :
          {ch : Fin (T + 2) → Bool // Q (Fin.tail ch)}))
      (fun ch => by
        refine Subtype.ext ?_
        simp)
      (fun p => by
        refine Prod.ext ?_ ?_
        · simp
        · exact Subtype.ext (by simp)))]
    rw [Fintype.card_prod, Fintype.card_bool]
  calc (delayNTM tm).acceptCount x (T + 2)
      = (Finset.univ.filter fun ch : Fin (T + 2) → Bool => P (Fin.tail ch)).card := by
        rw [NTM.acceptCount]
        congr 1
        exact Finset.filter_congr (fun a _ => hfilter a)
    _ = 2 * (Finset.univ.filter fun g : Fin (T + 1) → Bool => P g).card := hcard P
    _ = 2 * tm.acceptCount x (T + 1) := by rw [NTM.acceptCount]

end NTM

end Complexity
