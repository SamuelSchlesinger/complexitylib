/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Registers.Emit
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

/-!
# decRegTM: decrement a register

`decRegTM q` erases the last mark of the unary register `q`: scan right
over the marks, erase the final one, rewind. From `regTape d` to
`regTape (d - 1)` (truncated: the zero register is left unchanged) in
`2d + 4` steps. The missing primitive for descending loop fuels — the
pairwise at-most-one families iterate over shrinking suffixes.

Mirror of `incRegTM` (`RegisterOps.lean`) with an erase phase.
-/


public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Control states of `decRegTM`: `scan` right over the marks, `erase` the
    last one, move `back` to the sentinel, `park` on cell 1, then `done`. -/
inductive DecPhase where
  | scan | erase | back | park | done
  deriving DecidableEq

/-- `DecPhase` is a finite type, as required by the `TM` structure. -/
instance : Fintype DecPhase where
  elems := {.scan, .erase, .back, .park, .done}
  complete := fun x => by cases x <;> simp

/-- **Decrement register `q`**: scan right over the marks, erase the last
    one, rewind to cell 1. From `regTape d` to `regTape (d - 1)` in `2d + 4`
    steps; every other tape untouched. The zero register is unchanged. -/
def decRegTM (q : Fin n) : TM n where
  Q := DecPhase
  qstart := .scan
  qhalt := .done
  δ := fun s iHead wHeads oHead =>
    match s with
    | .scan =>
      if wHeads q = Γ.one then
        (.scan, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => if i = q then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.erase, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = q then (if wHeads q = Γ.start then Dir3.right else Dir3.left)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .erase =>
      if wHeads q = Γ.one then
        (.back, fun i => if i = q then Γw.blank else readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = q then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
      else
        (.park, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = q then (if wHeads q = Γ.start then Dir3.right
                                 else Dir3.stay)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .back =>
      if wHeads q = Γ.start then
        (.park, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => if i = q then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.back, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => if i = q then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
    | .park =>
      (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle s iHead wHeads oHead
  δ_right_of_start := by
    intro s iHead wHeads oHead
    match s with
    | .scan =>
      dsimp only []
      split
      · next hone =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = q
        · subst hir; rw [hone] at hi; exact absurd hi (by decide)
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = q
        · subst hir; rw [ite_eq_left rfl, ite_eq_left hi]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .erase =>
      dsimp only []
      split
      · next hone =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = q
        · subst hir; rw [hone] at hi; exact absurd hi (by decide)
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = q
        · subst hir; rw [ite_eq_left rfl, ite_eq_left hi]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .back =>
      dsimp only []
      split
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = q
        · rw [ite_eq_left hir]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · next hns =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = q
        · subst hir; exact absurd hi hns
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .park =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

section DecReg

variable {q : Fin n}

private theorem decRegTM_ne_halt {s : DecPhase} (h : s ≠ .done)
    {c : Cfg n (decRegTM (n := n) q).Q} (hst : c.state = s) :
    ¬ c.state = (decRegTM (n := n) q).qhalt := by
  rw [hst]
  show ¬ s = DecPhase.done
  exact h

/-- `scan` over a mark: the register head advances; nothing else changes. -/
private theorem decRegTM_step_scan_one (c : Cfg n (decRegTM (n := n) q).Q)
    (hst : c.state = .scan) (hone : (c.work q).read = Γ.one)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ q → Parked (c.work i))
    (hout : Parked c.output) :
    (decRegTM (n := n) q).step c = some
      { state := .scan, input := c.input,
        work := Function.update c.work q ((c.work q).move .right),
        output := c.output } := by
  rw [TM.step, ite_eq_right (decRegTM_ne_halt (by decide) hst)]
  simp only [decRegTM, hst, hone, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = q
    · subst hir
      rw [ite_eq_left rfl, Function.update_self,
        writeAndMove_readBack _ (by rw [hone]; decide)]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `scan` at the first blank: turn around onto the last mark. -/
private theorem decRegTM_step_scan_blank (c : Cfg n (decRegTM (n := n) q).Q)
    (hst : c.state = .scan) (hblank : (c.work q).read = Γ.blank)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ q → Parked (c.work i))
    (hout : Parked c.output) :
    (decRegTM (n := n) q).step c = some
      { state := .erase, input := c.input,
        work := Function.update c.work q ((c.work q).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (decRegTM_ne_halt (by decide) hst)]
  simp only [decRegTM, hst, hblank, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = q
    · subst hir
      rw [ite_eq_left rfl, Function.update_self,
        writeAndMove_readBack _ (by rw [hblank]; decide)]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `erase` on the last mark: blank it and start rewinding. -/
private theorem decRegTM_step_erase_one (c : Cfg n (decRegTM (n := n) q).Q)
    (hst : c.state = .erase) (hone : (c.work q).read = Γ.one)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ q → Parked (c.work i))
    (hout : Parked c.output) :
    (decRegTM (n := n) q).step c = some
      { state := .back, input := c.input,
        work := Function.update c.work q
          (((c.work q).write Γw.blank).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (decRegTM_ne_halt (by decide) hst)]
  simp only [decRegTM, hst, hone, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = q
    · subst hir
      simp only [↓reduceIte, Function.update_self]
    · rw [ite_eq_right hir, ite_eq_right hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `erase` on the sentinel (zero register): step right and park. -/
private theorem decRegTM_step_erase_start (c : Cfg n (decRegTM (n := n) q).Q)
    (hst : c.state = .erase) (hs : (c.work q).read = Γ.start)
    (hcr : ∀ j, 1 ≤ j → (c.work q).cells j ≠ Γ.start)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ q → Parked (c.work i))
    (hout : Parked c.output) :
    (decRegTM (n := n) q).step c = some
      { state := .park, input := c.input,
        work := Function.update c.work q ((c.work q).move .right),
        output := c.output } := by
  have h0 : (c.work q).head = 0 := by
    by_contra hc
    exact hcr _ (by omega) hs
  rw [TM.step, ite_eq_right (decRegTM_ne_halt (by decide) hst)]
  simp only [decRegTM, hst, hs, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = q
    · subst hir
      rw [ite_eq_left rfl, Function.update_self]
      show ((c.work i).write _).move Dir3.right = (c.work i).move .right
      congr 1
      rw [Tape.write, ite_eq_left h0]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `back` off the sentinel: keep rewinding. -/
private theorem decRegTM_step_back_left (c : Cfg n (decRegTM (n := n) q).Q)
    (hst : c.state = .back) (hns : (c.work q).read ≠ Γ.start)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ q → Parked (c.work i))
    (hout : Parked c.output) :
    (decRegTM (n := n) q).step c = some
      { state := .back, input := c.input,
        work := Function.update c.work q ((c.work q).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (decRegTM_ne_halt (by decide) hst)]
  simp only [decRegTM, hst, hns, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = q
    · subst hir
      rw [ite_eq_left rfl, Function.update_self, writeAndMove_readBack _ hns]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `back` on the sentinel: step right to cell 1 and park. -/
private theorem decRegTM_step_back_start (c : Cfg n (decRegTM (n := n) q).Q)
    (hst : c.state = .back) (hs : (c.work q).read = Γ.start)
    (hcr : ∀ j, 1 ≤ j → (c.work q).cells j ≠ Γ.start)
    (hinp : Parked c.input) (hwork : ∀ i, i ≠ q → Parked (c.work i))
    (hout : Parked c.output) :
    (decRegTM (n := n) q).step c = some
      { state := .park, input := c.input,
        work := Function.update c.work q ((c.work q).move .right),
        output := c.output } := by
  have h0 : (c.work q).head = 0 := by
    by_contra hc
    exact hcr _ (by omega) hs
  rw [TM.step, ite_eq_right (decRegTM_ne_halt (by decide) hst)]
  simp only [decRegTM, hst, hs, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = q
    · subst hir
      rw [ite_eq_left rfl, Function.update_self]
      show ((c.work i).write _).move Dir3.right = (c.work i).move .right
      congr 1
      rw [Tape.write, ite_eq_left h0]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `park`: one idle step into `done`. -/
private theorem decRegTM_step_park (c : Cfg n (decRegTM (n := n) q).Q)
    (hst : c.state = .park) (hinp : Parked c.input)
    (hwork : ∀ i, Parked (c.work i)) (hout : Parked c.output) :
    (decRegTM (n := n) q).step c = some
      { state := .done, input := c.input, work := c.work,
        output := c.output } := by
  rw [TM.step, ite_eq_right (decRegTM_ne_halt (by decide) hst)]
  simp only [decRegTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- The scan loop: from `scan` with the register head at `k + 1` over
    `regCells d` cells (`k ≤ d`), reach the first blank in `d - k` steps. -/
private theorem decRegTM_scan_run (d m : ℕ) :
    ∀ (k : ℕ), d = k + m →
      ∀ (c : Cfg n (decRegTM (n := n) q).Q),
      c.state = .scan → Parked c.input → (∀ i, i ≠ q → Parked (c.work i)) →
      Parked c.output →
      (c.work q).cells = regCells d → (c.work q).head = k + 1 →
      ∃ c', (decRegTM (n := n) q).reachesIn m c c' ∧
        c'.state = .scan ∧ c'.input = c.input ∧
        (∀ i, i ≠ q → c'.work i = c.work i) ∧
        (c'.work q).cells = regCells d ∧ (c'.work q).head = d + 1 ∧
        c'.output = c.output := by
  induction m with
  | zero =>
    intro k hk c hst hinp hwork hout hcells hhead
    exact ⟨c, .zero, hst, rfl, fun _ _ => rfl, hcells, by rw [hhead, hk], rfl⟩
  | succ m ih =>
    intro k hk c hst hinp hwork hout hcells hhead
    have hone : (c.work q).read = Γ.one := by
      rw [Tape.read, hhead, hcells]
      exact regCells_one (by omega) (by omega)
    have hstep := decRegTM_step_scan_one c hst hone hinp hwork hout
    obtain ⟨c', hreach, hst', hinp', hwork', hcells', hhead', hout'⟩ :=
      ih (k + 1) (by omega)
        { state := .scan, input := c.input,
          work := Function.update c.work q ((c.work q).move .right),
          output := c.output } rfl hinp
        (fun i hi => by
          show Parked (Function.update c.work q ((c.work q).move .right) i)
          rw [Function.update_of_ne hi]
          exact hwork i hi)
        hout
        (by
          show (Function.update c.work q ((c.work q).move .right) q).cells = _
          rw [Function.update_self]
          show (c.work q).cells = _
          exact hcells)
        (by
          show (Function.update c.work q ((c.work q).move .right) q).head = _
          rw [Function.update_self]
          show (c.work q).head + 1 = _
          rw [hhead])
    refine ⟨c', .step hstep hreach, hst', hinp', ?_, hcells', hhead', hout'⟩
    intro i hi
    rw [hwork' i hi]
    show Function.update c.work q ((c.work q).move .right) i = c.work i
    rw [Function.update_of_ne hi]

/-- The rewind loop: from `back` at head `h` over `▷`-clean cells, reach
    `done` parked at cell 1 in `h + 2` steps. -/
private theorem decRegTM_back_run (h : ℕ) :
    ∀ (c : Cfg n (decRegTM (n := n) q).Q),
      c.state = .back → Parked c.input → (∀ i, i ≠ q → Parked (c.work i)) →
      Parked c.output →
      (c.work q).cells 0 = Γ.start →
      (∀ j, 1 ≤ j → (c.work q).cells j ≠ Γ.start) →
      (c.work q).head = h →
      ∃ c', (decRegTM (n := n) q).reachesIn (h + 2) c c' ∧
        c'.state = .done ∧ c'.input = c.input ∧
        (∀ i, i ≠ q → c'.work i = c.work i) ∧
        (c'.work q).cells = (c.work q).cells ∧ (c'.work q).head = 1 ∧
        c'.output = c.output := by
  induction h with
  | zero =>
    intro c hst hinp hwork hout hc0 hcr hhead
    have hs : (c.work q).read = Γ.start := by rw [Tape.read, hhead]; exact hc0
    have hstep₁ := decRegTM_step_back_start c hst hs hcr hinp hwork hout
    have hworkP : ∀ i,
        Parked (Function.update c.work q ((c.work q).move .right) i) := by
      intro i
      by_cases hir : i = q
      · subst hir
        rw [Function.update_self]
        exact ⟨by show (c.work i).head + 1 ≥ 1; omega, fun j hj => hcr j hj⟩
      · rw [Function.update_of_ne hir]
        exact hwork i hir
    have hstep₂ := decRegTM_step_park (q := q)
      { state := .park, input := c.input,
        work := Function.update c.work q ((c.work q).move .right),
        output := c.output } rfl hinp hworkP hout
    refine ⟨_, .step hstep₁ (.step hstep₂ .zero), rfl, rfl, ?_, ?_, ?_, rfl⟩
    · intro i hi
      show Function.update c.work q ((c.work q).move .right) i = c.work i
      rw [Function.update_of_ne hi]
    · show (Function.update c.work q ((c.work q).move .right) q).cells = _
      rw [Function.update_self]
      rfl
    · show (Function.update c.work q ((c.work q).move .right) q).head = 1
      rw [Function.update_self]
      show (c.work q).head + 1 = 1
      rw [hhead]
  | succ h ih =>
    intro c hst hinp hwork hout hc0 hcr hhead
    have hns : (c.work q).read ≠ Γ.start := by
      rw [Tape.read, hhead]; exact hcr (h + 1) (by omega)
    have hstep₁ := decRegTM_step_back_left c hst hns hinp hwork hout
    have hupd : (Function.update c.work q ((c.work q).move .left) q).cells
        = (c.work q).cells := by
      rw [Function.update_self]
      rfl
    obtain ⟨c', hreach, hst', hinp', hwork', hcells', hhead', hout'⟩ :=
      ih { state := .back, input := c.input,
           work := Function.update c.work q ((c.work q).move .left),
           output := c.output } rfl hinp
        (fun i hi => by
          show Parked (Function.update c.work q ((c.work q).move .left) i)
          rw [Function.update_of_ne hi]
          exact hwork i hi)
        hout
        (by rw [hupd]; exact hc0)
        (fun j hj => by rw [hupd]; exact hcr j hj)
        (by
          show (Function.update c.work q ((c.work q).move .left) q).head = h
          rw [Function.update_self]
          show (c.work q).head - 1 = h
          rw [hhead]
          omega)
    refine ⟨c', .step hstep₁ hreach, hst', hinp', ?_, ?_, hhead', hout'⟩
    · intro i hi
      rw [hwork' i hi]
      show Function.update c.work q ((c.work q).move .left) i = c.work i
      rw [Function.update_of_ne hi]
    · rw [hcells', hupd]

/-- **`decRegTM` Hoare specification.** From `regTape d` in register `q`, reach
    `regTape (d - 1)` in `2d + 4` steps (`regTape 0` is left unchanged); the input,
    output, and every other work tape are untouched. -/
theorem decRegTM_hoareTime (q : Fin n) (d : ℕ) (inp₀ : Tape)
    (work₀ : Fin n → Tape) (ys : List Bool) (hinp₀ : Parked inp₀)
    (hwork₀ : ∀ i, i ≠ q → Parked (work₀ i)) (hq : work₀ q = regTape d) :
    (decRegTM (n := n) q).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ (Function.update work₀ q (regTape (d - 1))) ys)
      (2 * d + 4) := by
  rintro inp work out ⟨rfl, rfl, hout⟩
  obtain ⟨c₁, hreach₁, hst₁, hinp₁, hwork₁, hcells₁, hhead₁, hout₁⟩ :=
    decRegTM_scan_run d d 0 (by omega)
      { state := .scan, input := inp, work := work, output := out } rfl
      hinp₀ hwork₀ hout.parked
      (by show (work q).cells = regCells d; rw [hq, regT_cells])
      (by show (work q).head = 0 + 1; rw [hq, regT_head])
  have hinpP₁ : Parked c₁.input := by rw [hinp₁]; exact hinp₀
  have hworkP₁ : ∀ i, i ≠ q → Parked (c₁.work i) := fun i hi => by
    rw [hwork₁ i hi]
    exact hwork₀ i hi
  have houtP₁ : Parked c₁.output := by rw [hout₁]; exact hout.parked
  have hblank₁ : (c₁.work q).read = Γ.blank := by
    rw [Tape.read, hhead₁, hcells₁]
    exact regCells_blank (by omega)
  have hstep₂ := decRegTM_step_scan_blank c₁ hst₁ hblank₁ hinpP₁ hworkP₁ houtP₁
  set c₂ : Cfg n (decRegTM (n := n) q).Q :=
    { state := .erase, input := c₁.input,
      work := Function.update c₁.work q ((c₁.work q).move .left),
      output := c₁.output } with hc₂
  have hc₂cells : (c₂.work q).cells = regCells d := by
    show (Function.update c₁.work q ((c₁.work q).move .left) q).cells = _
    rw [Function.update_self]
    show (c₁.work q).cells = _
    exact hcells₁
  have hc₂head : (c₂.work q).head = d := by
    show (Function.update c₁.work q ((c₁.work q).move .left) q).head = d
    rw [Function.update_self]
    show (c₁.work q).head - 1 = d
    rw [hhead₁]
    omega
  have hc₂workP : ∀ i, i ≠ q → Parked (c₂.work i) := fun i hi => by
    show Parked (Function.update c₁.work q ((c₁.work q).move .left) i)
    rw [Function.update_of_ne hi]
    exact hworkP₁ i hi
  have hc₂work : ∀ i, i ≠ q → c₂.work i = work i := fun i hi => by
    show Function.update c₁.work q ((c₁.work q).move .left) i = work i
    rw [Function.update_of_ne hi]
    exact hwork₁ i hi
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- Zero register: erase sees the sentinel; nothing changes.
    have hs₂ : (c₂.work q).read = Γ.start := by
      rw [Tape.read, hc₂head, hc₂cells]
      rfl
    have hstep₃ := decRegTM_step_erase_start c₂ rfl hs₂
      (fun j hj => by
        rw [hc₂cells]
        rw [regCells, ite_eq_right (by omega)]
        split <;> decide)
      hinpP₁ hc₂workP houtP₁
    set c₃ : Cfg n (decRegTM (n := n) q).Q :=
      { state := .park, input := c₂.input,
        work := Function.update c₂.work q ((c₂.work q).move .right),
        output := c₂.output } with hc₃
    have hc₃workP : ∀ i, Parked (c₃.work i) := by
      intro i
      by_cases hir : i = q
      · subst hir
        show Parked (Function.update c₂.work i ((c₂.work i).move .right) i)
        rw [Function.update_self]
        refine ⟨?_, ?_⟩
        · show (c₂.work i).head + 1 ≥ 1
          omega
        · intro j hj
          show (c₂.work i).cells j ≠ Γ.start
          rw [hc₂cells, regCells, ite_eq_right (by omega)]
          split <;> decide
      · show Parked (Function.update c₂.work q ((c₂.work q).move .right) i)
        rw [Function.update_of_ne hir]
        exact hc₂workP i hir
    have hstep₄ := decRegTM_step_park c₃ rfl hinpP₁ hc₃workP houtP₁
    refine ⟨_, _, ?_,
      reachesIn_trans _ hreach₁
        (.step hstep₂ (.step hstep₃ (.step hstep₄ .zero))), rfl, ?_, ?_, ?_⟩
    · omega
    · show c₁.input = inp
      exact hinp₁
    · funext i
      by_cases hir : i = q
      · subst hir
        show Function.update c₂.work i ((c₂.work i).move .right) i
          = Function.update work i (regTape (0 - 1)) i
        rw [Function.update_self, Function.update_self]
        refine Tape.ext ?_ ?_
        · show (c₂.work i).head + 1 = 1
          rw [hc₂head]
        · show (c₂.work i).cells = regCells (0 - 1)
          rw [hc₂cells]
      · show Function.update c₂.work q ((c₂.work q).move .right) i
          = Function.update work q (regTape (0 - 1)) i
        rw [Function.update_of_ne hir, Function.update_of_ne hir]
        exact hc₂work i hir
    · show OutAcc ys c₂.output
      rw [show c₂.output = out from hout₁]
      exact hout
  · -- Positive register: erase the last mark, rewind.
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have hone₂ : (c₂.work q).read = Γ.one := by
      rw [Tape.read, hc₂head, hc₂cells]
      exact regCells_one (by omega) (by omega)
    have hstep₃ := decRegTM_step_erase_one c₂ rfl hone₂ hinpP₁ hc₂workP houtP₁
    set c₃ : Cfg n (decRegTM (n := n) q).Q :=
      { state := .back, input := c₂.input,
        work := Function.update c₂.work q
          (((c₂.work q).write Γw.blank).move .left),
        output := c₂.output } with hc₃
    have hc₃cells : (c₃.work q).cells = regCells e := by
      show (Function.update c₂.work q
        (((c₂.work q).write Γw.blank).move .left) q).cells = _
      rw [Function.update_self]
      show (((c₂.work q).write Γw.blank).move .left).cells = _
      show ((c₂.work q).write Γw.blank).cells = _
      rw [Tape.write, ite_eq_right (by rw [hc₂head]; omega)]
      show Function.update (c₂.work q).cells (c₂.work q).head Γw.blank.toΓ = _
      rw [hc₂cells, hc₂head]
      exact regCells_update_blank_succ e
    have hc₃head : (c₃.work q).head = e := by
      show (Function.update c₂.work q
        (((c₂.work q).write Γw.blank).move .left) q).head = e
      rw [Function.update_self]
      show ((c₂.work q).write Γw.blank).head - 1 = e
      have hwh : ((c₂.work q).write Γw.blank).head = (c₂.work q).head := by
        rw [Tape.write]
        split <;> rfl
      rw [hwh, hc₂head]
      omega
    obtain ⟨c₄, hreach₄, hst₄, hinp₄, hwork₄, hcells₄, hhead₄, hout₄⟩ :=
      decRegTM_back_run e c₃ rfl hinpP₁
        (fun i hi => by
          show Parked (Function.update c₂.work q
            (((c₂.work q).write Γw.blank).move .left) i)
          rw [Function.update_of_ne hi]
          exact hc₂workP i hi)
        houtP₁
        (by rw [hc₃cells]; rfl)
        (fun j hj => by
          rw [hc₃cells, regCells, ite_eq_right (by omega)]
          split <;> decide)
        hc₃head
    refine ⟨c₄, _, ?_,
      reachesIn_trans _ hreach₁ (.step hstep₂ (.step hstep₃ hreach₄)),
      hst₄, ?_, ?_, ?_⟩
    · omega
    · rw [hinp₄]
      exact hinp₁
    · funext i
      by_cases hir : i = q
      · subst hir
        rw [Function.update_self]
        refine Tape.ext ?_ ?_
        · rw [hhead₄]
          rfl
        · rw [hcells₄, hc₃cells]
          show regCells e = regCells (e + 1 - 1)
          rfl
      · rw [Function.update_of_ne hir, hwork₄ i hir]
        show Function.update c₂.work q
          (((c₂.work q).write Γw.blank).move .left) i = work i
        rw [Function.update_of_ne hir]
        exact hc₂work i hir
    · rw [hout₄]
      show OutAcc ys c₂.output
      rw [show c₂.output = out from hout₁]
      exact hout

end DecReg

end TM

end Complexity
