/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.SpaceTime.Internal.Observation
public import Complexitylib.Models.TuringMachine.SpaceTime.Internal.OutputFrontier
public import Complexitylib.Models.TuringMachine.Internal

/-!
# Reduced transducer snapshot dynamics — proof internals

This module proves that one-way, space-bounded transducer steps are determined
by the finite snapshot from `SpaceTime.Defs`, once the shared read-only input
contents are fixed.
-/

@[expose] public section

namespace Complexity

namespace Tape

/-- The output components retained by a transducer snapshot evolve
deterministically under a common non-left write-and-move action. -/
private theorem outputObservation_writeAndMove_congr {t u : Tape}
    (ht : t.BlankAfterHead) (hu : u.BlankAfterHead)
    (hzero : t.head = 0 ↔ u.head = 0) (hread : t.read = u.read)
    (s : Γ) (d : Dir3) (hd : d ≠ Dir3.left) :
    decide ((t.writeAndMove s d).head = 0) =
        decide ((u.writeAndMove s d).head = 0) ∧
      (t.writeAndMove s d).read = (u.writeAndMove s d).read := by
  cases d with
  | left => exact (hd rfl).elim
  | right =>
      constructor
      · simp [Tape.writeAndMove, Tape.move]
      · have htBlank : t.cells (t.head + 1) = Γ.blank := ht _ (by omega)
        have huBlank : u.cells (u.head + 1) = Γ.blank := hu _ (by omega)
        by_cases ht0 : t.head = 0
        · have hu0 : u.head = 0 := hzero.mp ht0
          simp [Tape.read, Tape.writeAndMove, Tape.move, Tape.write, ht0, hu0]
          simpa [ht0, hu0] using htBlank.trans huBlank.symm
        · have hu0 : u.head ≠ 0 := fun h => ht0 (hzero.mpr h)
          simp [Tape.read, Tape.writeAndMove, Tape.move, Tape.write, ht0, hu0,
            htBlank, huBlank]
  | stay =>
      constructor
      · by_cases ht0 : t.head = 0
        · have hu0 : u.head = 0 := hzero.mp ht0
          simp [Tape.writeAndMove, Tape.move, Tape.write_head, ht0, hu0]
        · have hu0 : u.head ≠ 0 := fun h => ht0 (hzero.mpr h)
          simp [Tape.writeAndMove, Tape.move, Tape.write_head, ht0, hu0]
      · by_cases ht0 : t.head = 0
        · have hu0 : u.head = 0 := hzero.mp ht0
          simpa [Tape.read, Tape.writeAndMove, Tape.move, Tape.write, ht0, hu0]
            using hread
        · have hu0 : u.head ≠ 0 := fun h => ht0 (hzero.mpr h)
          simp [Tape.read, Tape.writeAndMove, Tape.move, Tape.write, ht0, hu0]

end Tape

namespace TM

variable {k : ℕ} {tm : TM k} {inputLength space : ℕ}

/-- One transducer step preserves equality of finite snapshots when both
source configurations share the same read-only input contents and all source
and target work heads stay within the advertised space bound. -/
theorem transducerSnapshot_step_congr
    {c₁ c₂ d₁ d₂ : Cfg k tm.Q}
    (htrans : tm.IsTransducer)
    (hc₁ : c₁.WithinAuxSpace inputLength space)
    (hc₂ : c₂.WithinAuxSpace inputLength space)
    (hd₁ : d₁.WithinAuxSpace inputLength space)
    (hd₂ : d₂.WithinAuxSpace inputLength space)
    (hinput : c₁.input.cells = c₂.input.cells)
    (hblank₁ : c₁.output.BlankAfterHead)
    (hblank₂ : c₂.output.BlankAfterHead)
    (hsnap : tm.transducerSnapshot c₁ inputLength space hc₁ =
      tm.transducerSnapshot c₂ inputLength space hc₂)
    (hstep₁ : tm.step c₁ = some d₁)
    (hstep₂ : tm.step c₂ = some d₂) :
    tm.transducerSnapshot d₁ inputLength space hd₁ =
      tm.transducerSnapshot d₂ inputLength space hd₂ := by
  have hstate := state_eq_of_transducerSnapshot_eq hc₁ hc₂ hsnap
  have hinputRead := input_read_eq_of_transducerSnapshot_eq hc₁ hc₂ hsnap hinput
  have hworkRead : (fun i => (c₁.work i).read) =
      (fun i => (c₂.work i).read) := by
    funext i
    exact work_read_eq_of_transducerSnapshot_eq hc₁ hc₂ hsnap i
  have houtputRead := output_read_eq_of_transducerSnapshot_eq hc₁ hc₂ hsnap
  have hne₁ := state_ne_qhalt_of_step hstep₁
  have hne₂ := state_ne_qhalt_of_step hstep₂
  simp only [TM.step, hne₁, ↓reduceIte, Option.some.injEq] at hstep₁
  simp only [TM.step, hne₂, ↓reduceIte, Option.some.injEq] at hstep₂
  rw [← hstate, ← hinputRead, ← hworkRead, ← houtputRead] at hstep₂
  let tr :=
    tm.δ c₁.state c₁.input.read (fun i => (c₁.work i).read) c₁.output.read
  change
    { state := tr.1
      input := c₁.input.move tr.2.2.2.1
      work := fun i =>
        (c₁.work i).writeAndMove (tr.2.1 i).toΓ (tr.2.2.2.2.1 i)
      output := c₁.output.writeAndMove tr.2.2.1.toΓ tr.2.2.2.2.2 } = d₁ at hstep₁
  change
    { state := tr.1
      input := c₂.input.move tr.2.2.2.1
      work := fun i =>
        (c₂.work i).writeAndMove (tr.2.1 i).toΓ (tr.2.2.2.2.1 i)
      output := c₂.output.writeAndMove tr.2.2.1.toΓ tr.2.2.2.2.2 } = d₂ at hstep₂
  subst d₁
  subst d₂
  have hinputHead := input_head_eq_of_transducerSnapshot_eq hc₁ hc₂ hsnap
  have hinputMove :
      (c₁.input.move tr.2.2.2.1).head =
        (c₂.input.move tr.2.2.2.1).head := by
    cases tr.2.2.2.1 <;> simp [Tape.move, hinputHead]
  have hzero := output_head_eq_zero_iff_of_transducerSnapshot_eq hc₁ hc₂ hsnap
  have houtDir : tr.2.2.2.2.2 ≠ Dir3.left := by
    dsimp only [tr]
    exact htrans c₁.state c₁.input.read (fun i => (c₁.work i).read) c₁.output.read
  have houtObs := Tape.outputObservation_writeAndMove_congr hblank₁ hblank₂
    hzero houtputRead tr.2.2.1.toΓ tr.2.2.2.2.2 houtDir
  unfold transducerSnapshot
  apply Prod.ext
  · rfl
  apply Prod.ext
  · apply Fin.ext
    exact hinputMove
  apply Prod.ext
  · funext i
    exact Tape.boundedObs_writeAndMove_congr
      (hc₁.1 i) (hc₂.1 i)
      (work_boundedObs_eq_of_transducerSnapshot_eq hc₁ hc₂ hsnap i)
      (tr.2.1 i).toΓ (tr.2.2.2.2.1 i) (hd₁.1 i) (hd₂.1 i)
  apply Prod.ext
  · exact houtObs.1
  · exact houtObs.2

/-- Equal snapshots stay equal along equal-length transducer runs whose work
and input heads remain within the same auxiliary-space window. -/
theorem transducerSnapshot_reachesIn_congr
    {t : ℕ} {c₁ c₂ d₁ d₂ : Cfg k tm.Q}
    (htrans : tm.IsTransducer)
    (hreach₁ : tm.reachesIn t c₁ d₁)
    (hreach₂ : tm.reachesIn t c₂ d₂)
    (hspace₁ : ∀ {u : ℕ} {d : Cfg k tm.Q}, tm.reachesIn u c₁ d →
      d.WithinAuxSpace inputLength space)
    (hspace₂ : ∀ {u : ℕ} {d : Cfg k tm.Q}, tm.reachesIn u c₂ d →
      d.WithinAuxSpace inputLength space)
    (hinput : c₁.input.cells = c₂.input.cells)
    (hblank₁ : c₁.output.BlankAfterHead)
    (hblank₂ : c₂.output.BlankAfterHead)
    (hsnap : tm.transducerSnapshot c₁ inputLength space (hspace₁ .zero) =
      tm.transducerSnapshot c₂ inputLength space (hspace₂ .zero)) :
    tm.transducerSnapshot d₁ inputLength space (hspace₁ hreach₁) =
      tm.transducerSnapshot d₂ inputLength space (hspace₂ hreach₂) := by
  induction t generalizing c₁ c₂ d₁ d₂ with
  | zero =>
      cases hreach₁
      cases hreach₂
      exact hsnap
  | succ t ih =>
      cases hreach₁ with
      | @step _ mid₁ _ _ hstep₁ htail₁ =>
          cases hreach₂ with
          | @step _ mid₂ _ _ hstep₂ htail₂ =>
              let hone₁ : tm.reachesIn 1 c₁ mid₁ := .step hstep₁ .zero
              let hone₂ : tm.reachesIn 1 c₂ mid₂ := .step hstep₂ .zero
              have hspaceTail₁ : ∀ {u : ℕ} {d : Cfg k tm.Q},
                  tm.reachesIn u mid₁ d → d.WithinAuxSpace inputLength space := by
                intro u d hreach
                exact hspace₁ (tm.reachesIn_trans hone₁ hreach)
              have hspaceTail₂ : ∀ {u : ℕ} {d : Cfg k tm.Q},
                  tm.reachesIn u mid₂ d → d.WithinAuxSpace inputLength space := by
                intro u d hreach
                exact hspace₂ (tm.reachesIn_trans hone₂ hreach)
              have hnext := transducerSnapshot_step_congr htrans
                (hspace₁ .zero) (hspace₂ .zero)
                (hspaceTail₁ .zero) (hspaceTail₂ .zero)
                hinput hblank₁ hblank₂ hsnap hstep₁ hstep₂
              have hinputNext : mid₁.input.cells = mid₂.input.cells := by
                rw [input_cells_eq_of_step hstep₁, input_cells_eq_of_step hstep₂,
                  hinput]
              exact ih htail₁ htail₂ hspaceTail₁ hspaceTail₂ hinputNext
                (htrans.output_blankAfterHead_step hblank₁ hstep₁)
                (htrans.output_blankAfterHead_step hblank₂ hstep₂) hnext

end TM

end Complexity
