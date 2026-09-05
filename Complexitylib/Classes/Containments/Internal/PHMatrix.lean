/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PHLayout
public import Complexitylib.Models.TuringMachine.Combinators.ApplyDecide
public import Complexitylib.Models.TuringMachine.Hoare.SpaceFrame
public import Complexitylib.Models.TuringMachine.Placement.Window

/-!
# Running the matrix machine inside the enumerator

⚠️ Unreviewed by Bolton

One iteration of the enumerator runs the machine deciding the matrix language on the pair it has
just built. `TM.applyTM` reads that pair off a work tape and writes the verdict onto another, and
`TM.placeWorkTM 3 7` puts the whole thing where the layout says: the matrix machine's own tapes at
`3 … k + 2`, the pair it reads at `PolyExists.yIdx`, the verdict at `PolyExists.vIdx`, and the
enumerator's own tapes untouched on either side.

The contract below is the placed form of `TM.applyTM_hoareTime_decide_space_frame` — the
space-bounded one, since the width it reports is what the body's wipe has to clear. Besides the
verdict it records what the next iteration needs: the registers came through unchanged, and every
tape of the block is parked inside a window of width `H` with nothing written beyond it — which
is what makes the wipe that follows finite.

## Main results

- `PolyExists.matrixTM` — the placed evaluator, and `PolyExists.matrixEntry` the tapes it starts on
- `PolyExists.matrixTM_hoareTime` — its contract, with the frame the loop body needs
- `PolyExists.matrixTM_keepsWindowOn` — its window, from the matrix machine's space bound
-/

@[expose] public section

namespace Complexity

namespace PolyExists

variable {k : ℕ}

/-- The matrix machine, reading its input from a work tape and writing its verdict onto another,
placed where the enumerator's layout wants it. -/
def matrixTM (M : TM k) : TM (enumTapes k) := TM.placeWorkTM 3 7 (TM.applyTM M)

/-- The tapes the placed evaluator is entered with: its own block loaded with the pair `y`, and
the enumerator's own tapes carried through as they are. -/
def matrixEntry (M : TM k) (extras : Fin (enumTapes k) → Tape) (y : List Bool) (I : Tape) :
    Fin (enumTapes k) → Tape := fun i =>
  if h : TM.placeWorkInMiddle 3 (k + 2) i then
    TM.applyPre M y I (TM.placeWorkCoord 3 (k + 2) i h)
  else extras i

/-- The verdict tape is the placed image of the evaluator's result tape. -/
theorem placeWorkCoord_vIdx (k : ℕ) (h : TM.placeWorkInMiddle 3 (k + 2) (vIdx k)) :
    TM.placeWorkCoord 3 (k + 2) (vIdx k) h = Fin.last (k + 1) := by
  apply Fin.ext
  show (vIdx k).val - 3 = k + 1
  show 3 + k + 1 - 3 = k + 1
  omega

theorem vIdx_inMiddle (k : ℕ) : TM.placeWorkInMiddle 3 (k + 2) (vIdx k) := by
  constructor
  · show 3 ≤ 3 + k + 1
    omega
  · show 3 + k + 1 < 3 + (k + 2)
    omega

theorem yIdx_inMiddle (k : ℕ) : TM.placeWorkInMiddle 3 (k + 2) (yIdx k) := by
  constructor
  · show 3 ≤ 3 + k
    omega
  · show 3 + k < 3 + (k + 2)
    omega

/-- **One evaluation of the matrix machine, contracted.** From the placed entry tapes the stage
halts inside the matrix machine's own time bound, publishes its verdict on `y` in cell one of the
verdict tape, returns every tape outside its block untouched, and leaves its own block parked
inside a window of width `H`. -/
theorem matrixTM_hoareTime (M : TM k) {L : Language} {T S : ℕ → ℕ} (hdec : M.DecidesInTime L T)
    (hdecS : M.DecidesInSpace L S)
    (y : List Bool) (I : Tape) (hI : TM.Parked I) (hISI : Tape.StartInvariant I)
    (extras : Fin (enumTapes k) → Tape)
    (hinv : ∀ i, ¬ TM.placeWorkInMiddle 3 (k + 2) i → Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬ TM.placeWorkInMiddle 3 (k + 2) i → 1 ≤ (extras i).head)
    (H : ℕ) (hHS : y.length + S y.length + 2 ≤ H) :
    (matrixTM M).HoareTime
      (fun inp work out => inp = I ∧ work = matrixEntry M extras y I ∧ out = TM.parkedBlank)
      (fun inp work out => inp = I ∧ out = TM.parkedBlank ∧
        (y ∈ L → (work (vIdx k)).cells 1 = Γ.one) ∧
        (y ∉ L → (work (vIdx k)).cells 1 = Γ.zero) ∧
        (∀ i, ¬ TM.placeWorkInMiddle 3 (k + 2) i → work i = extras i) ∧
        (∀ i, TM.placeWorkInMiddle 3 (k + 2) i →
          Tape.StartInvariant (work i) ∧ (work i).head ≤ H ∧
            ∀ j, H < j → (work i).cells j = Γ.blank))
      (T y.length) := by
  rintro inp work out ⟨hi, hw, ho⟩
  obtain ⟨c', t, ht, hreach, hhalt, hinpEq, houtEq, hverdict, hframe⟩ :=
    TM.applyTM_hoareTime_decide_space_frame M hdec hdecS y I hI hISI H hHS
      I (TM.applyPre M y I) TM.parkedBlank ⟨rfl, rfl, rfl⟩
  refine ⟨TM.placeWorkCfg (TM.applyTM M) 3 7 extras c', t, ht, ?_, hhalt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hstart : (⟨(matrixTM M).qstart, inp, work, out⟩ :
        Cfg (enumTapes k) (matrixTM M).Q) =
        TM.placeWorkCfg (TM.applyTM M) 3 7 extras
          (⟨(TM.applyTM M).qstart, I, TM.applyPre M y I, TM.parkedBlank⟩ :
            Cfg (k + 2) (TM.applyTM M).Q) := by
      refine Cfg.ext rfl hi (funext fun j => ?_) ho
      rw [hw]
      show matrixEntry M extras y I j = _
      rw [matrixEntry]
      rfl
    rw [hstart]
    exact TM.placeWorkTM_reachesIn_placeWorkCfg_of_startInvariant (TM.applyTM M) 3 7 extras
      hreach hinv hhead
  · show c'.input = I
    exact hinpEq
  · show c'.output = TM.parkedBlank
    exact houtEq
  · intro hy
    show (if h : TM.placeWorkInMiddle 3 (k + 2) (vIdx k) then
      c'.work (TM.placeWorkCoord 3 (k + 2) (vIdx k) h) else extras (vIdx k)).cells 1 = Γ.one
    rw [dite_eq_left (vIdx_inMiddle k), placeWorkCoord_vIdx k (vIdx_inMiddle k)]
    exact hverdict.1 hy
  · intro hy
    show (if h : TM.placeWorkInMiddle 3 (k + 2) (vIdx k) then
      c'.work (TM.placeWorkCoord 3 (k + 2) (vIdx k) h) else extras (vIdx k)).cells 1 = Γ.zero
    rw [dite_eq_left (vIdx_inMiddle k), placeWorkCoord_vIdx k (vIdx_inMiddle k)]
    exact hverdict.2 hy
  · intro j hj
    show (if h : TM.placeWorkInMiddle 3 (k + 2) j then _ else extras j) = extras j
    rw [dite_eq_right hj]
  · intro j hj
    have heq : (TM.placeWorkCfg (TM.applyTM M) 3 7 extras c').work j
        = c'.work (TM.placeWorkCoord 3 (k + 2) j hj) := by
      show (if h : TM.placeWorkInMiddle 3 (k + 2) j then
        c'.work (TM.placeWorkCoord 3 (k + 2) j h) else extras j) = _
      rw [dite_eq_left hj]
    rw [heq]
    exact hframe _

/-- **The evaluating stage's window.** The matrix machine's own space bound is what limits it —
its running time is exponential and would limit nothing. -/
theorem matrixTM_keepsWindowOn (M : TM k) {L : Language} {S : ℕ → ℕ}
    (hdecS : M.DecidesInSpace L S) (hne : M.qstart ≠ M.qhalt)
    (y : List Bool) (I : Tape) (hISI : Tape.StartInvariant I)
    (extras : Fin (enumTapes k) → Tape)
    (hinv : ∀ i, ¬ TM.placeWorkInMiddle 3 (k + 2) i → Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬ TM.placeWorkInMiddle 3 (k + 2) i → 1 ≤ (extras i).head)
    {inputLength space : ℕ}
    (hextraW : ∀ i, ¬ TM.placeWorkInMiddle 3 (k + 2) i → (extras i).head ≤ space)
    (hspace : y.length + S y.length + 2 ≤ space)
    (hIhead : max I.head 1 ≤ inputLength + (y.length + S y.length + 1) + 1) :
    (matrixTM M).KeepsWindowOn
      (fun c => c.state = (matrixTM M).qstart ∧ c.input = I ∧
        c.work = matrixEntry M extras y I ∧ c.output = TM.parkedBlank)
      inputLength space := by
  intro c hc D hD
  obtain ⟨hst, hi, hw, ho⟩ := hc
  have hentry : c = TM.placeWorkCfg (TM.applyTM M) 3 7 extras
      (⟨(TM.applyTM M).qstart, I, TM.applyPre M y I, TM.parkedBlank⟩ :
        Cfg (k + 2) (TM.applyTM M).Q) := by
    refine Cfg.ext hst hi (funext fun j => ?_) ho
    rw [hw]
    show matrixEntry M extras y I j = _
    rw [matrixEntry]
    rfl
  rw [hentry] at hD
  refine TM.placeWorkTM_keepsWindow_of_reaches (TM.applyTM M) 3 7 extras _ hinv hhead
    hextraW (fun e he => ?_) D hD
  have hwin := TM.applyTM_keepsWindow_of_decidesInSpace M hdecS hne y I hISI
    (inputLength := inputLength) (space := y.length + S y.length + 1) (le_refl _) hIhead e
    (by rw [← TM.applyTM_entry_eq M y I]; exact he)
  obtain ⟨⟨hw', hi'⟩, ho'⟩ := hwin
  exact ⟨⟨fun i => by have := hw' i; omega, by omega⟩, by omega⟩

end PolyExists

end Complexity
