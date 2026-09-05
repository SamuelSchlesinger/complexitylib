/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget
public import Complexitylib.Models.TuringMachine.Combinators.RetargetCompute
public import Complexitylib.Models.TuringMachine.Lift
public import Complexitylib.Models.TuringMachine.Combinators.Apply
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Window

/-!
# Space accounting for a machine reading its input off a work tape

`TM.retargetInput` runs a machine `M` with its input tape relocated to work tape `k`. That
relocation is exactly what a space bound has to be re-read through: what was `M`'s *free* input
tape becomes a *charged* work tape, so the window the retargeted machine needs is `M`'s own space
budget plus the length of the virtual input.

The correspondence is step-by-step (`TM.retargetInput_step_commute`), so every configuration the
retargeted machine reaches is a wrapped configuration of `M` — with the real input tape, which it
never consults, drifting only by an idle move. `M`'s bound on its own run therefore transfers.

## Main results

- `TM.retargetInput_within` — a wrapped configuration is inside the window when `M`'s is
- `TM.retargetInput_keepsWindow_of_reaches` — the whole retargeted run stays inside it
- `TM.retargetInputStarted_reaches_iff`, `TM.retargetInputStarted_keepsWindow_of_reaches` — the
  started wrapper runs the same steps, so the accounting carries over
- `TM.retargetOutput_keepsWindow_of_reaches` — redirecting the output onto a work tape costs one
  cell of window
- `TM.applyTM_keepsWindow_of_reaches` — **the two composed**: the window of the work-to-work
  evaluator
- `TM.applyTM_keepsWindow_of_decidesInSpace` — the same from a `TM.DecidesInSpace` hypothesis
- `TM.liftTM_keepsWindow_of_reaches` — adding spare work tapes costs no window
-/

@[expose] public section

namespace Complexity

namespace TM

variable {k : ℕ}

/-- A wrapped configuration sits inside a window as soon as the wrapped `M`-configuration does:
`M`'s work heads and its relocated input head are all charged against the new budget. -/
theorem retargetInput_within (M : TM k) (r : Tape) (c : Cfg k M.Q)
    {m s inputLength space : ℕ} (hc : c.WithinDecisionSpace m s)
    (hspace : m + s + 1 ≤ space) (hr : r.head ≤ inputLength + space + 1) :
    (retargetWrap M r c).WithinDecisionSpace inputLength space := by
  refine ⟨⟨fun i => ?_, hr⟩, ?_⟩
  · by_cases h : i.val < k
    · rw [retargetWrap_work_lt M r c i h]
      have := hc.1.1 ⟨i.val, h⟩
      omega
    · have hlt := i.isLt
      have hik : i = ⟨k, by omega⟩ := by
        apply Fin.ext
        show i.val = k
        omega
      rw [hik, retargetWrap_work_last M r c]
      have := hc.1.2
      omega
  · have := hc.2
    show c.output.head ≤ space + 1
    omega

/-- **The retargeted run stays inside the window.** Every configuration reachable from a wrapped
start is itself wrapped — the step correspondence is exact — so `M`'s bound on its own run is the
only thing needed. -/
theorem retargetInput_keepsWindow_of_reaches (M : TM k) (r₀ : Tape) (c₀ : Cfg k M.Q)
    {m s inputLength space : ℕ}
    (hM : ∀ c, M.reaches c₀ c → c.WithinDecisionSpace m s)
    (hc₀inp : Tape.StartInvariant c₀.input)
    (hc₀work : ∀ i, Tape.StartInvariant (c₀.work i))
    (hc₀out : Tape.StartInvariant c₀.output)
    (hr₀ : Tape.StartInvariant r₀)
    (hspace : m + s + 1 ≤ space)
    (hr : max r₀.head 1 ≤ inputLength + space + 1) :
    ∀ d, (retargetInput M).reaches (retargetWrap M r₀ c₀) d →
      d.WithinDecisionSpace inputLength space := by
  have key : ∀ d, (retargetInput M).reaches (retargetWrap M r₀ c₀) d →
      ∃ r c, M.reaches c₀ c ∧ Tape.StartInvariant c.input ∧
        (∀ i, Tape.StartInvariant (c.work i)) ∧ Tape.StartInvariant c.output ∧
        Tape.StartInvariant r ∧ r.head ≤ max r₀.head 1 ∧ d = retargetWrap M r c := by
    intro d hd
    induction hd with
    | refl =>
        exact ⟨r₀, c₀, Relation.ReflTransGen.refl, hc₀inp, hc₀work, hc₀out, hr₀,
          le_max_left _ _, rfl⟩
    | @tail dmid dnext _ hstep ih =>
        obtain ⟨r, cM, hreach, hinp, hwork, hout, hrsi, hrhead, rfl⟩ := ih
        have hstep' : (retargetInput M).step (retargetWrap M r cM) = some dnext := hstep
        have hne0 : (retargetWrap M r cM).state ≠ (retargetInput M).qhalt :=
          state_ne_qhalt_of_step hstep'
        have hne : cM.state ≠ M.qhalt := hne0
        obtain ⟨cM', hstep0⟩ : ∃ cM', M.step cM = some cM' := by
          rw [TM.step, ite_eq_right hne]
          exact ⟨_, rfl⟩
        have hcomm := retargetInput_step_commute M hstep0 r hinp
        have hd'eq := Option.some_inj.mp (hstep'.symm.trans hcomm)
        obtain ⟨hinp', hwork', hout'⟩ := Tape.StartInvariant.step M hstep0 hinp hwork hout
        refine ⟨r.move (idleDir r.read), cM', Relation.ReflTransGen.tail hreach hstep0,
          hinp', hwork', hout', ?_, ?_, hd'eq⟩
        · rw [move_idleDir_eq_of_startInvariant hrsi]
          exact ⟨hrsi.1, hrsi.2⟩
        · rw [move_idleDir_eq_of_startInvariant hrsi]
          show max r.head 1 ≤ max r₀.head 1
          omega
  intro d hd
  obtain ⟨r, cM, hreach, -, -, -, -, hrhead, rfl⟩ := key d hd
  exact retargetInput_within M r cM (hM cM hreach) hspace (by omega)

/-! ## The started wrapper -/

/-- The started wrapper and the plain retargeted machine have the same step relation, so they
reach exactly the same configurations. Only their start states differ. -/
theorem retargetInputStarted_reaches_iff (M : TM k) (c d : Cfg (k + 1) M.Q) :
    (retargetInputStarted M).reaches c d ↔ (retargetInput M).reaches c d := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih =>
        exact Relation.ReflTransGen.tail ih
          ((retargetInputStarted_step_eq M _).symm.trans hs)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih =>
        exact Relation.ReflTransGen.tail ih
          ((retargetInputStarted_step_eq M _).trans hs)

/-- **The started wrapper keeps the window too.** It runs the same steps as `TM.retargetInput`,
so the accounting of `TM.retargetInput_keepsWindow_of_reaches` applies verbatim. -/
theorem retargetInputStarted_keepsWindow_of_reaches (M : TM k) (r₀ : Tape) (c₀ : Cfg k M.Q)
    {m s inputLength space : ℕ}
    (hM : ∀ c, M.reaches c₀ c → c.WithinDecisionSpace m s)
    (hc₀inp : Tape.StartInvariant c₀.input)
    (hc₀work : ∀ i, Tape.StartInvariant (c₀.work i))
    (hc₀out : Tape.StartInvariant c₀.output)
    (hr₀ : Tape.StartInvariant r₀)
    (hspace : m + s + 1 ≤ space)
    (hr : max r₀.head 1 ≤ inputLength + space + 1) :
    ∀ d, (retargetInputStarted M).reaches (retargetWrap M r₀ c₀) d →
      d.WithinDecisionSpace inputLength space := fun d hd =>
  retargetInput_keepsWindow_of_reaches M r₀ c₀ hM hc₀inp hc₀work hc₀out hr₀ hspace hr d
    ((retargetInputStarted_reaches_iff M _ d).mp hd)

/-! ## Redirecting the output to a work tape -/

/-- **Redirecting the output onto a work tape costs one cell.** The old output tape becomes work
tape `n`, and the decision convention allows the output head one cell more than the work heads, so
the window grows by exactly that. The real output tape is left parked as a dummy. -/
theorem retargetOutput_keepsWindow_of_reaches {m : ℕ} (tm : TM m) (c₀ : Cfg m tm.Q)
    {inputLength space : ℕ}
    (htm : ∀ c, tm.reaches c₀ c → c.WithinDecisionSpace inputLength space) :
    ∀ D, tm.retargetOutput.reaches (tm.retargetCfg c₀) D →
      D.WithinDecisionSpace inputLength (space + 1) := by
  have key : ∀ D, tm.retargetOutput.reaches (tm.retargetCfg c₀) D →
      ∃ c, tm.reaches c₀ c ∧ D = tm.retargetCfg c := by
    intro D hD
    induction hD with
    | refl => exact ⟨c₀, Relation.ReflTransGen.refl, rfl⟩
    | @tail dmid dnext _ hs ih =>
        obtain ⟨c, hreach, rfl⟩ := ih
        have hs' : tm.retargetOutput.step (tm.retargetCfg c) = some dnext := hs
        rw [retargetOutput_step_retargetCfg] at hs'
        cases hstep : tm.step c with
        | none =>
            rw [hstep] at hs'
            exact absurd hs' (by nofun)
        | some c' =>
            rw [hstep] at hs'
            exact ⟨c', Relation.ReflTransGen.tail hreach hstep,
              (Option.some_inj.mp hs').symm⟩
  intro D hD
  obtain ⟨c, hreach, rfl⟩ := key D hD
  have hc := htm c hreach
  refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
  · by_cases h : i.val < m
    · rw [retargetCfg_work_lt tm c i h]
      have := hc.1.1 ⟨i.val, h⟩
      omega
    · have hlt := i.isLt
      have hil : i = Fin.last m := by
        apply Fin.ext
        show i.val = m
        omega
      rw [hil, retargetCfg_work_last tm c]
      have := hc.2
      omega
  · show c.input.head ≤ _
    have := hc.1.2
    omega
  · show ((Tape.init ([] : List Γ)).move Dir3.right).head ≤ space + 1 + 1
    show 0 + 1 ≤ space + 1 + 1
    omega

/-! ## The work-to-work evaluator -/

/-- **The work-to-work evaluator keeps a window.** `TM.applyTM M` is
`M` retargeted twice — its input read off a work tape, its output written to another — so its
window is `M`'s own decision-space budget, plus the virtual input's length for the relocated
input tape, plus one cell for the relocated output tape. Every quantity is explicit, so a caller
that knows `M`'s polynomial space bound knows this one. -/
theorem applyTM_keepsWindow_of_reaches (M : TM k) (r₀ : Tape) (c₀ : Cfg k M.Q)
    {m s inputLength space : ℕ}
    (hM : ∀ c, M.reaches c₀ c → c.WithinDecisionSpace m s)
    (hc₀inp : Tape.StartInvariant c₀.input)
    (hc₀work : ∀ i, Tape.StartInvariant (c₀.work i))
    (hc₀out : Tape.StartInvariant c₀.output)
    (hr₀ : Tape.StartInvariant r₀)
    (hspace : m + s + 1 ≤ space)
    (hr : max r₀.head 1 ≤ inputLength + space + 1) :
    ∀ D, (applyTM M).reaches
        ((retargetInputStarted M).retargetCfg (retargetWrap M r₀ c₀)) D →
      D.WithinDecisionSpace inputLength (space + 1) :=
  retargetOutput_keepsWindow_of_reaches (retargetInputStarted M) (retargetWrap M r₀ c₀)
    (retargetInputStarted_keepsWindow_of_reaches M r₀ c₀ hM hc₀inp hc₀work hc₀out hr₀ hspace hr)

/-- **The evaluator's window, from the source machine's space bound alone.** Started on the
canonical entry configuration with virtual input `y`, `TM.applyTM M` stays inside a window of
`|y| + S |y| + 2` — the source's own budget, the relocated input tape, and one cell for the
relocated output. This is the form a caller with a `TM.DecidesInSpace` hypothesis can use. -/
theorem applyTM_keepsWindow_of_decidesInSpace (M : TM k) {L : Language} {S : ℕ → ℕ}
    (hdec : M.DecidesInSpace L S) (hne : M.qstart ≠ M.qhalt)
    (y : List Bool) (realInput : Tape) (hrsi : Tape.StartInvariant realInput)
    {inputLength space : ℕ}
    (hspace : y.length + S y.length + 1 ≤ space)
    (hr : max realInput.head 1 ≤ inputLength + space + 1) :
    ∀ D, (applyTM M).reaches
        ((retargetInputStarted M).retargetCfg (retargetInputStartedCfg M y realInput)) D →
      D.WithinDecisionSpace inputLength (space + 1) := by
  rw [retargetInputStartedCfg_eq_retargetWrap M y realInput hne]
  refine applyTM_keepsWindow_of_reaches M realInput (startedCfg M y hne) ?_ ?_ ?_ ?_ hrsi
    hspace hr
  · intro c hreach
    exact hdec.1 y c (Relation.ReflTransGen.head (step_initCfg_startedCfg M y hne) hreach)
  · rw [startedCfg_input_eq M y hne]
    exact (startInvariant_initOfBool y).move Dir3.right
  · intro i
    rw [startedCfg_work_eq_init_move_right M y hne i]
    exact startInvariant_initNil.move Dir3.right
  · rw [startedCfg_output_eq_init_move_right M y hne]
    exact startInvariant_initNil.move Dir3.right


/-! ## Embedding a machine in a larger tape space -/

/-- **Adding spare work tapes costs no window.** `TM.liftTM` runs a machine unchanged alongside
`m` extra tapes, which stay parked at cell one throughout, so a configuration of the lifted
machine sits in exactly the window its underlying configuration does. This is how a subroutine is
placed inside a machine with more tapes than it needs. -/
theorem liftTM_keepsWindow_of_reaches {m' : ℕ} (tm : TM m') (m : ℕ) (c₀ : Cfg m' tm.Q)
    {inputLength space : ℕ} (hs : 1 ≤ space)
    (htm : ∀ c, tm.reaches c₀ c → c.WithinDecisionSpace inputLength space) :
    ∀ D, (tm.liftTM m).reaches (tm.liftCfg m c₀) D →
      D.WithinDecisionSpace inputLength space := by
  have key : ∀ D, (tm.liftTM m).reaches (tm.liftCfg m c₀) D →
      ∃ c, tm.reaches c₀ c ∧ D = tm.liftCfg m c := by
    intro D hD
    induction hD with
    | refl => exact ⟨c₀, Relation.ReflTransGen.refl, rfl⟩
    | @tail dmid dnext _ hstp ih =>
        obtain ⟨c, hreach, rfl⟩ := ih
        have hs' : (tm.liftTM m).step (tm.liftCfg m c) = some dnext := hstp
        rw [liftTM_step_liftCfg] at hs'
        cases hstep : tm.step c with
        | none =>
            rw [hstep] at hs'
            exact absurd hs' (by nofun)
        | some c' =>
            rw [hstep] at hs'
            exact ⟨c', Relation.ReflTransGen.tail hreach hstep,
              (Option.some_inj.mp hs').symm⟩
  intro D hD
  obtain ⟨c, hreach, rfl⟩ := key D hD
  have hc := htm c hreach
  refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
  · by_cases hi : i.val < m'
    · rw [liftCfg_work_lt tm m c i hi]
      exact hc.1.1 ⟨i.val, hi⟩
    · rw [liftCfg_work_ge tm m c i (by omega)]
      show ((Tape.init ([] : List Γ)).move Dir3.right).head ≤ space
      show 0 + 1 ≤ space
      omega
  · show c.input.head ≤ _
    exact hc.1.2
  · show c.output.head ≤ _
    exact hc.2

end TM

end Complexity
