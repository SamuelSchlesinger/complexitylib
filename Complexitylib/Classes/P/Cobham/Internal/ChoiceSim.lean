/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Cobham.Internal.Simulate
public import Complexitylib.Models.TuringMachine.ChoiceTape

/-!
# Encoding the start of a nondeterministic path

`NTM.choiceTM` runs one path of a nondeterministic machine deterministically,
reading its choice bits from the last work tape. To simulate such a run inside
Cobham's algebra, the starting configuration must be encoded with the choice
string already on that tape and its head parked on the first bit.

This file supplies that encoder — `Cobham.initChoiceFn`, the counterpart of
`Cobham.initFn` — together with its algebra membership and the identification
with `Cobham.cfgCode` of the intended configuration.

## Main definitions

- `Cobham.choiceTape` — the choice string on a tape, head at cell 1
- `Cobham.choiceCfg` — the starting configuration of `NTM.choiceTM`
- `Cobham.initChoiceFn` — its encoding, as a function of the two strings

## Main results

- `Cobham.initChoiceFn_mem` — the encoder is in the algebra
- `Cobham.initChoiceFn_eq` — the encoder computes `cfgCode` of `choiceCfg`
- `Cobham.dropChoice_choiceCfg` — forgetting the choice tape gives the
  nondeterministic machine's own initial configuration
-/

@[expose] public section

namespace Complexity

namespace Cobham

variable {k : ℕ}

/-- The choice string on a tape, with the head parked on the first bit. -/
def choiceTape (c : List Bool) : Tape := ⟨1, (Tape.init (c.map Γ.ofBool)).cells⟩

@[simp] theorem choiceTape_head (c : List Bool) : (choiceTape c).head = 1 := rfl

@[simp] theorem choiceTape_cells (c : List Bool) :
    (choiceTape c).cells = (Tape.init (c.map Γ.ofBool)).cells := rfl

/-- The starting configuration of `NTM.choiceTM tm`: the input on the input
tape, the choice string on the appended choice tape. -/
noncomputable def choiceCfg (tm : NTM k) (x c : List Bool) : Cfg (k + 1) tm.Q where
  state := tm.qstart
  input := Tape.init (x.map Γ.ofBool)
  work := fun i => if i = Fin.last k then choiceTape c else Tape.init []
  output := Tape.init []

/-- Forgetting the choice tape gives the nondeterministic machine's own
initial configuration. -/
@[simp] theorem dropChoice_choiceCfg (tm : NTM k) (x c : List Bool) :
    NTM.dropChoice (choiceCfg tm x c) = tm.initCfg x := by
  refine Cfg.ext rfl rfl ?_ rfl
  funext i
  rw [NTM.dropChoice, choiceCfg]
  simp [(Fin.castSucc_lt_last i).ne]

/-- The encoded starting configuration of a nondeterministic path. Everything
but the input tape's and the choice tape's right half-blocks is a constant of
the machine. -/
noncomputable def initChoiceFn (tm : NTM k) (R x c : List Bool) : List Bool :=
  padTo R (stateCode tm.qstart) ++
    (padTo R [] ++ (padTo R (symCode Γ.start ++ encodeBits x) ++
      ((List.replicate (k + 1) (padTo R [] ++ padTo R (symCode Γ.start))).flatten ++
        (padTo R (symCode Γ.start) ++ padTo R (encodeBits c)))))

/-- **The encoder is in the algebra.** -/
theorem initChoiceFn_mem {n : ℕ} (tm : NTM k)
    {gR gx gc : (Fin n → List Bool) → List Bool} (hR : Cobham gR) (hx : Cobham gx)
    (hc : Cobham gc) :
    Cobham fun v : Fin n → List Bool => initChoiceFn tm (gR v) (gx v) (gc v) :=
  (appendFn (padFn hR (Cobham.const _))
    (appendFn (padFn hR Cobham.empty)
      (appendFn (padFn hR (appendFn (Cobham.const _) (encodeBitsFn hx)))
        (appendFn
          (repeatFn (appendFn (padFn hR Cobham.empty)
            (padFn hR (Cobham.const _))) (k + 1))
          (appendFn (padFn hR (Cobham.const _))
            (padFn hR (encodeBitsFn hc))))))).of_eq fun _ => rfl

private theorem flatten_tapesBlocks' (W : ℕ) : ∀ ts : List Tape,
    (tapesBlocks W ts).flatten
      = (ts.map fun t => padTo (blockRuler W) (leftCode t)
          ++ padTo (blockRuler W) (rightCode t W)).flatten := by
  intro ts
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      rw [tapesBlocks, List.flatMap_cons, List.flatten_append, ← tapesBlocks, ih,
        List.map_cons, List.flatten_cons, tapeBlocks]
      simp

private theorem cellsCode_of_bits' (x : List Bool) :
    ∀ (t : Tape) (i : ℕ), (∀ j, ∀ _ : j < x.length, t.cells (i + j) = Γ.ofBool x[j]) →
      cellsCode t i x.length = encodeBits x := by
  induction x with
  | nil => intro t i _; rfl
  | cons b x ih =>
      intro t i hcells
      rw [List.length_cons, cellsCode_succ_left, encodeBits_cons,
        show t.cells i = Γ.ofBool b from by have h0 := hcells 0 (by simp); simpa using h0]
      congr 1
      exact ih t (i + 1) fun j hj => by
        have := hcells (j + 1) (by rw [List.length_cons]; omega)
        rw [show i + 1 + j = i + (j + 1) from by omega]
        simpa using this

private theorem cellsCode_of_blank' (t : Tape) (i w : ℕ)
    (h : ∀ j < w, t.cells (i + j) = Γ.blank) :
    cellsCode t i w = List.replicate (2 * w) false := by
  induction w generalizing i with
  | zero => rfl
  | succ w ih =>
      rw [cellsCode_succ_left, show t.cells i = Γ.blank from by simpa using h 0 (by omega),
        ih (i + 1) fun j hj => by
          rw [show i + 1 + j = i + (j + 1) from by omega]; exact h (j + 1) (by omega),
        show 2 * (w + 1) = 2 + 2 * w from by omega, List.replicate_add]
      rfl

/-- The right half-block of a tape carrying `y` from cell `1`, head at cell 1. -/
private theorem padTo_rightCode_choiceTape (W : ℕ) (c : List Bool) (hc : c.length ≤ W) :
    padTo (blockRuler W) (rightCode (choiceTape c) W)
      = padTo (blockRuler W) (encodeBits c) := by
  have h1 : cellsCode (choiceTape c) 1 c.length = encodeBits c :=
    cellsCode_of_bits' c _ 1 fun j hj => by
      rw [choiceTape_cells, show 1 + j = j + 1 from by omega, Tape.init_cells_succ]
      have hjm : j < (c.map Γ.ofBool).length := by simpa using hj
      rw [List.getElem?_eq_getElem hjm]
      simp
  have h2 : cellsCode (choiceTape c) (1 + c.length) (W - c.length)
      = List.replicate (2 * (W - c.length)) false :=
    cellsCode_of_blank' _ _ _ fun j _ => by
      rw [choiceTape_cells, show 1 + c.length + j = (c.length + j) + 1 from by omega,
        Tape.init_cells_succ, List.getElem?_eq_none (by simp)]
      rfl
  have hcells : cellsCode (choiceTape c) 1 W
      = encodeBits c ++ List.replicate (2 * (W - c.length)) false := by
    rw [show W = c.length + (W - c.length) from by omega,
      cellsCode_add _ 1 c.length _]
    rw [h1]
    congr 1
    rw [show c.length + (W - c.length) - c.length = W - c.length from by omega]
    exact h2
  rw [rightCode, choiceTape_head, show W + 1 - 1 = W from by omega, hcells,
    padTo_append_replicate]

/-- **The encoder computes the encoding of the starting configuration.** -/
theorem initChoiceFn_eq (tm : NTM k) (W : ℕ) (x c : List Bool)
    (hx : x.length ≤ W) (hc : c.length ≤ W) :
    initChoiceFn tm (blockRuler W) x c = cfgCode W (choiceCfg tm x c) := by
  set R := blockRuler W with hR
  have hin : padTo R (rightCode (Tape.init (x.map Γ.ofBool)) W)
      = padTo R (symCode Γ.start ++ encodeBits x) := by
    have h0 : cellsCode (Tape.init (x.map Γ.ofBool)) 0 1 = symCode Γ.start := by
      rw [cellsCode_succ_left, cellsCode_zero, List.append_nil, Tape.init_cells_zero]
    have h1 : cellsCode (Tape.init (x.map Γ.ofBool)) 1 x.length = encodeBits x :=
      cellsCode_of_bits' x _ 1 fun j hj => by
        rw [show 1 + j = j + 1 from by omega, Tape.init_cells_succ]
        have hjm : j < (x.map Γ.ofBool).length := by simpa using hj
        rw [List.getElem?_eq_getElem hjm]
        simp
    have h2 : cellsCode (Tape.init (x.map Γ.ofBool)) (1 + x.length) (W - x.length)
        = List.replicate (2 * (W - x.length)) false :=
      cellsCode_of_blank' _ _ _ fun j _ => by
        rw [show 1 + x.length + j = (x.length + j) + 1 from by omega,
          Tape.init_cells_succ, List.getElem?_eq_none (by simp)]
        rfl
    have hcells : cellsCode (Tape.init (x.map Γ.ofBool)) 0 (W + 1)
        = symCode Γ.start ++ (encodeBits x
            ++ List.replicate (2 * (W - x.length)) false) := by
      rw [show W + 1 = 1 + (x.length + (W - x.length)) from by omega,
        cellsCode_add _ 0 1 _, cellsCode_add _ (0 + 1) x.length _]
      simp only [Nat.zero_add]
      rw [h0, h1, h2]
    rw [rightCode, Tape.init_head, Nat.sub_zero, hcells, ← List.append_assoc,
      padTo_append_replicate]
  have hblank : padTo R (rightCode (Tape.init []) W) = padTo R (symCode Γ.start) := by
    have h0 : cellsCode (Tape.init ([] : List Γ)) 0 1 = symCode Γ.start := by
      rw [cellsCode_succ_left, cellsCode_zero, List.append_nil, Tape.init_cells_zero]
    have h2 : cellsCode (Tape.init ([] : List Γ)) 1 W
        = List.replicate (2 * W) false :=
      cellsCode_of_blank' _ _ _ fun j _ => by
        rw [show 1 + j = j + 1 from by omega, Tape.init_nil_cells_succ]
    have hcells : cellsCode (Tape.init ([] : List Γ)) 0 (W + 1)
        = symCode Γ.start ++ List.replicate (2 * W) false := by
      rw [show W + 1 = 1 + W from by omega, cellsCode_add _ 0 1 W]
      simp only [Nat.zero_add]
      rw [h0, h2]
    rw [rightCode, Tape.init_head, Nat.sub_zero, hcells, padTo_append_replicate]
  have hleft : ∀ contents : List Γ, leftCode (Tape.init contents) = [] := fun _ => rfl
  have hcleft : leftCode (choiceTape c) = symCode Γ.start := by
    rw [leftCode, choiceTape_head, leftCodeFrom_succ, leftCodeFrom_zero,
      List.append_nil, choiceTape_cells, Tape.init_cells_zero]
  have hct : cfgTapes (choiceCfg tm x c)
      = Tape.init (x.map Γ.ofBool)
          :: (List.replicate (k + 1) (Tape.init []) ++ [choiceTape c]) := by
    rw [cfgTapes]
    congr 1
    show (Tape.init [] : Tape) :: List.ofFn (fun i : Fin (k + 1) =>
        if i = Fin.last k then choiceTape c else (Tape.init [] : Tape))
      = List.replicate (k + 1) (Tape.init []) ++ [choiceTape c]
    rw [List.ofFn_succ']
    have hcast : (List.ofFn fun i : Fin k =>
        (if i.castSucc = Fin.last k then choiceTape c else (Tape.init [] : Tape)))
        = List.replicate k (Tape.init []) := by
      rw [show (fun i : Fin k =>
          (if i.castSucc = Fin.last k then choiceTape c else (Tape.init [] : Tape)))
          = fun _ : Fin k => (Tape.init [] : Tape) from by
        funext i
        rw [ite_eq_right (Fin.castSucc_lt_last i).ne]]
      rw [List.ofFn_const]
    rw [hcast, ite_eq_left rfl, List.replicate_succ]
    simp
  rw [cfgCode, cfgBlocks_eq, List.flatten_cons, flatten_tapesBlocks', hct]
  simp only [List.map_cons, List.map_nil, List.map_append, List.map_replicate,
    List.flatten_cons, List.flatten_nil, List.flatten_append, List.append_nil,
    hleft, hcleft]
  rw [hin, hblank, padTo_rightCode_choiceTape W c hc]
  show _ = padTo R (stateCode tm.qstart) ++ _
  rw [initChoiceFn]
  simp only [← hR, List.append_assoc]

/-! ## Iterating the encoded step from a choice configuration -/

/-- Every tape of a run from a choice configuration keeps its left-end
marker. -/
theorem runCfg_choiceCfg_startInvariant (tm : NTM k) (x c : List Bool) (n : ℕ) :
    (TM.runCfg (NTM.choiceTM tm) (choiceCfg tm x c) n).input.StartInvariant ∧
      (∀ i, ((TM.runCfg (NTM.choiceTM tm) (choiceCfg tm x c) n).work i).StartInvariant) ∧
      (TM.runCfg (NTM.choiceTM tm) (choiceCfg tm x c) n).output.StartInvariant := by
  induction n with
  | zero =>
      refine ⟨Tape.StartInvariant.init_ofBool x, fun i => ?_, Tape.StartInvariant.init_nil⟩
      show (if i = Fin.last k then choiceTape c else Tape.init []).StartInvariant
      split
      · exact Tape.StartInvariant.init_ofBool c
      · exact Tape.StartInvariant.init_nil
  | succ n ih =>
      erw [TM.runCfg_succ]
      cases hs : (NTM.choiceTM tm).step (TM.runCfg (NTM.choiceTM tm) (choiceCfg tm x c) n) with
      | none => rw [Option.getD_none]; exact ih
      | some c' =>
          rw [Option.getD_some]
          exact TM.step_startInvariant _ hs ih.1 ih.2.1 ih.2.2

/-- After `n` steps of a run from a choice configuration every head is within
`n + 1` cells of the start: the choice head begins one cell in. -/
theorem runCfg_choiceCfg_head_le (tm : NTM k) (x c : List Bool) (n : ℕ) :
    (TM.runCfg (NTM.choiceTM tm) (choiceCfg tm x c) n).input.head ≤ n + 1 ∧
      (∀ i, ((TM.runCfg (NTM.choiceTM tm) (choiceCfg tm x c) n).work i).head ≤ n + 1) ∧
      (TM.runCfg (NTM.choiceTM tm) (choiceCfg tm x c) n).output.head ≤ n + 1 := by
  induction n with
  | zero =>
      refine ⟨by erw [TM.runCfg_zero]; simp [choiceCfg], fun i => ?_,
        by erw [TM.runCfg_zero]; simp [choiceCfg]⟩
      show (if i = Fin.last k then choiceTape c else Tape.init []).head ≤ 0 + 1
      split <;> simp
  | succ n ih =>
      erw [TM.runCfg_succ]
      cases hs : (NTM.choiceTM tm).step (TM.runCfg (NTM.choiceTM tm) (choiceCfg tm x c) n) with
      | none =>
          rw [Option.getD_none]
          exact ⟨by omega, fun i => by have := ih.2.1 i; omega, by omega⟩
      | some c' =>
          rw [Option.getD_some]
          obtain ⟨h1, h2, h3⟩ := TM.step_head_le _ hs
          exact ⟨by omega, fun i => by have := h2 i; have := ih.2.1 i; omega, by omega⟩

/-- The invariants of a choice run, in the form the encoding lemmas want. -/
theorem cfgTapes_runCfg_choiceCfg_inv (tm : NTM k) (x c : List Bool) (n W : ℕ)
    (hn : n + 1 ≤ W) :
    (∀ t ∈ cfgTapes (TM.runCfg (NTM.choiceTM tm) (choiceCfg tm x c) n), t.StartInvariant) ∧
      (∀ t ∈ cfgTapes (TM.runCfg (NTM.choiceTM tm) (choiceCfg tm x c) n), t.head ≤ W) := by
  obtain ⟨i1, w1, o1⟩ := runCfg_choiceCfg_startInvariant tm x c n
  obtain ⟨i2, w2, o2⟩ := runCfg_choiceCfg_head_le tm x c n
  constructor <;> intro t ht <;>
    · rw [cfgTapes, List.mem_cons, List.mem_cons, List.mem_ofFn] at ht
      rcases ht with rfl | rfl | ⟨i, rfl⟩
      · first | exact i1 | omega
      · first | exact o1 | omega
      · first | exact w1 i | (have := w2 i; omega)

/-- **The encoded iteration tracks a choice run.** -/
theorem iterate_stepFn_choice (tm : NTM k) (W : ℕ) (x c : List Bool)
    (hq : Fintype.card tm.Q ≤ blockWidth W) :
    ∀ n : ℕ, n + 1 ≤ W →
      (stepFn (NTM.choiceTM tm) (blockRuler W))^[n] (cfgCode W (choiceCfg tm x c))
        = cfgCode W (TM.runCfg (NTM.choiceTM tm) (choiceCfg tm x c) n) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      obtain ⟨hinv, hW⟩ := cfgTapes_runCfg_choiceCfg_inv tm x c n W (by omega)
      rw [Function.iterate_succ_apply', ih (by omega)]; erw [TM.runCfg_succ]
      cases hs : (NTM.choiceTM tm).step (TM.runCfg (NTM.choiceTM tm) (choiceCfg tm x c) n) with
      | none =>
          rw [Option.getD_none]
          exact stepFn_halted _ (TM.step_eq_none_iff_halted.mp hs) hq hW
      | some c' =>
          rw [Option.getD_some]
          have hgood := stepActs_forall₂ _ _ hinv hW
          refine stepFn_eq _ hs hq hW ?_ ?_ hgood
          · exact hinv _ (by simp [cfgTapes])
          · intro i
            exact hinv _ (by
              rw [cfgTapes]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_ofFn.mpr ⟨i, rfl⟩)))

/-! ## Running the path inside the algebra -/

@[simp] theorem initChoiceFn_length (tm : NTM k) (R x c : List Bool) :
    (initChoiceFn tm R x c).length = (2 * (k + 3) + 1) * R.length := by
  rw [initChoiceFn]
  simp only [List.length_append, padTo_length, List.length_flatten,
    List.map_replicate, List.sum_replicate]
  simp
  ring

/-- The encoded run stays inside its blocks. -/
theorem iterate_stepFn_choice_length_le (tm : NTM k) (R x c : List Bool) (n : ℕ) :
    ((stepFn (NTM.choiceTM tm) R)^[n] (initChoiceFn tm R x c)).length
      ≤ (2 * (k + 3) + 1) * R.length := by
  induction n with
  | zero => exact (initChoiceFn_length tm R x c).le
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact stepFn_length_le _ R _ ih

/-- The encoded configuration after running the path for `|c|` steps, under a
ruler derived from the clock string `u`. -/
noncomputable def runChoiceFn (tm : NTM k) (u x c : List Bool) : List Bool :=
  (stepFn (NTM.choiceTM tm) (clockRuler u))^[c.length]
    (initChoiceFn tm (clockRuler u) x c)

/-- **Running the path is in the algebra.** -/
theorem runChoiceFn_mem {n : ℕ} (tm : NTM k)
    {gu gx gc : (Fin n → List Bool) → List Bool}
    (hu : Cobham gu) (hx : Cobham gx) (hc : Cobham gc) :
    Cobham fun v : Fin n → List Bool => runChoiceFn tm (gu v) (gx v) (gc v) := by
  have hstage :=
    iterFn (n := 3)
      (e := fun w : Fin 3 → List Bool =>
        initChoiceFn tm (clockRuler (w 1)) (w 2) (w 0))
      (f := fun w : Fin 4 → List Bool =>
        stepFn (NTM.choiceTM tm) (clockRuler (w 2)) (w 0))
      (j := fun w : Fin 4 → List Bool =>
        (List.replicate (2 * (k + 3) + 1) (clockRuler (w 2))).flatten)
      (initChoiceFn_mem tm (clockRulerFn (Cobham.proj 1)) (Cobham.proj 2) (Cobham.proj 0))
      (stepFn_mem _ (clockRulerFn (Cobham.proj 2)) (Cobham.proj 0))
      (repeatFn (clockRulerFn (Cobham.proj 2)) _)
      (by
        intro c v
        have hlen := iterate_stepFn_choice_length_le tm (clockRuler (v 1)) (v 2) (v 0) c.length
        simp only [List.length_flatten, List.map_replicate, List.sum_replicate]
        exact hlen)
  have hg : ∀ i : Fin 4, Cobham (![gc, gc, gu, gx] i) := by
    intro i
    match i with
    | 0 => exact hc
    | 1 => exact hc
    | 2 => exact hu
    | 3 => exact hx
  refine (Cobham.comp hstage hg).of_eq fun v => ?_
  rfl

/-! ## Reading the verdict -/

/-- The output tape's two half-blocks after the run, rewound to cell `0`. -/
noncomputable def outPairChoiceFn (tm : NTM k) (u x c : List Bool) : List Bool :=
  (rewindFn (clockRuler u))^[u.length]
    (blockAt (clockRuler u) (runChoiceFn tm u x c) 3
      ++ blockAt (clockRuler u) (runChoiceFn tm u x c) 4)

/-- **The rewind stage is in the algebra.** -/
theorem outPairChoiceFn_mem {n : ℕ} (tm : NTM k)
    {gu gx gc : (Fin n → List Bool) → List Bool}
    (hu : Cobham gu) (hx : Cobham gx) (hc : Cobham gc) :
    Cobham fun v : Fin n → List Bool => outPairChoiceFn tm (gu v) (gx v) (gc v) := by
  have hstage :=
    iterFn (n := 3)
      (e := fun w : Fin 3 → List Bool =>
        blockAt (clockRuler (w 0)) (runChoiceFn tm (w 0) (w 1) (w 2)) 3
          ++ blockAt (clockRuler (w 0)) (runChoiceFn tm (w 0) (w 1) (w 2)) 4)
      (f := fun w : Fin 4 → List Bool => rewindFn (clockRuler (w 1)) (w 0))
      (j := fun w : Fin 4 → List Bool => clockRuler (w 1) ++ clockRuler (w 1))
      (appendFn
        (blockFn (clockRulerFn (Cobham.proj 0))
          (runChoiceFn_mem tm (Cobham.proj 0) (Cobham.proj 1) (Cobham.proj 2)) 3)
        (blockFn (clockRulerFn (Cobham.proj 0))
          (runChoiceFn_mem tm (Cobham.proj 0) (Cobham.proj 1) (Cobham.proj 2)) 4))
      (rewindFn_mem (clockRulerFn (Cobham.proj 1)) (Cobham.proj 0))
      (appendFn (clockRulerFn (Cobham.proj 1)) (clockRulerFn (Cobham.proj 1)))
      (by
        intro c v
        show ((rewindFn (clockRuler (v 0)))^[c.length]
            (blockAt (clockRuler (v 0)) (runChoiceFn tm (v 0) (v 1) (v 2)) 3
              ++ blockAt (clockRuler (v 0)) (runChoiceFn tm (v 0) (v 1) (v 2)) 4)).length
          ≤ (clockRuler (v 0) ++ clockRuler (v 0)).length
        rw [List.length_append]
        refine le_trans (iterate_rewindFn_length_le _ _ ?_ _) (by omega)
        rw [List.length_append, blockAt, blockAt, List.length_take, List.length_take]
        omega)
  have hg : ∀ i : Fin 4, Cobham (![gu, gu, gx, gc] i) := by
    intro i
    match i with
    | 0 => exact hu
    | 1 => exact hu
    | 2 => exact hx
    | 3 => exact hc
  refine (Cobham.comp hstage hg).of_eq fun v => ?_
  rfl

/-- The verdict of the path: the machine halted with `1` on output cell `1`. -/
noncomputable def acceptChoiceFn (tm : NTM k) (u x c : List Bool) : List Bool :=
  andBit
    (matchPrefix (stateCode tm.qhalt) (blockAt (clockRuler u) (runChoiceFn tm u x c) 0))
    (matchPrefix (symCode Γ.one)
      (((outPairChoiceFn tm u x c).drop (clockRuler u).length).drop 2))

/-- The verdict is a genuine one-bit flag. -/
theorem acceptChoiceFn_flag (tm : NTM k) (u x c : List Bool) :
    acceptChoiceFn tm u x c = [true] ∨ acceptChoiceFn tm u x c = [false] :=
  andBit_flag _ _

/-- **The verdict is in the algebra.** -/
theorem acceptChoiceFn_mem {n : ℕ} (tm : NTM k)
    {gu gx gc : (Fin n → List Bool) → List Bool}
    (hu : Cobham gu) (hx : Cobham gx) (hc : Cobham gc) :
    Cobham fun v : Fin n → List Bool => acceptChoiceFn tm (gu v) (gx v) (gc v) :=
  andFn
    (matchPrefixFn (blockFn (clockRulerFn hu) (runChoiceFn_mem tm hu hx hc) 0) _)
    (matchPrefixFn
      (dropFn (Cobham.const (List.replicate 2 false))
        (dropFn (clockRulerFn hu) (outPairChoiceFn_mem tm hu hx hc))) _)

/-! ## The run is the nondeterministic trace -/

/-- The choice bits found on the choice tape are the bits of `c`. -/
theorem choiceStream_choiceCfg (tm : NTM k) (x c : List Bool) (j : ℕ) (hj : j < c.length) :
    NTM.choiceStream (choiceCfg tm x c) j = c[j] := by
  have hwork : (choiceCfg tm x c).work (Fin.last k) = choiceTape c := by
    simp [choiceCfg]
  rw [NTM.choiceStream, hwork, choiceTape_head, choiceTape_cells,
    show 1 + j = j + 1 from by omega, Tape.init_cells_succ]
  have hjm : j < (c.map Γ.ofBool).length := by simpa using hj
  rw [List.getElem?_eq_getElem hjm]
  cases hb : c[j] <;> simp [hb, Γ.ofBool]

/-- **The deterministic run from a choice configuration is the trace.** -/
theorem dropChoice_runCfg_choiceCfg (tm : NTM k) (T : ℕ) (x c : List Bool) :
    NTM.dropChoice (TM.runCfg (NTM.choiceTM tm) (choiceCfg tm x c) T)
      = tm.trace T (fun j => NTM.choiceStream (choiceCfg tm x c) j.val) (tm.initCfg x) := by
  obtain ⟨c', t, hle, hreach, hstop, heq⟩ :=
    NTM.choiceTM_simulates tm T (choiceCfg tm x c)
      (by
        have hwork : (choiceCfg tm x c).work (Fin.last k) = choiceTape c := by
          simp [choiceCfg]
        rw [hwork]
        exact Tape.StartInvariant.init_ofBool c)
      (by
        have hwork : (choiceCfg tm x c).work (Fin.last k) = choiceTape c := by
          simp [choiceCfg]
        rw [hwork, choiceTape_head])
  have hrun : TM.runCfg (NTM.choiceTM tm) (choiceCfg tm x c) T = c' := by
    have hpart : TM.runCfg (NTM.choiceTM tm) (choiceCfg tm x c) t = c' :=
      TM.runCfg_of_reachesIn _ hreach
    rcases Nat.lt_or_ge t T with hlt | hge
    · have hhalt := hstop hlt
      erw [show T = t + (T - t) from by omega, TM.runCfg_add, hpart,
        TM.runCfg_of_halted _ hhalt]
    · have : t = T := by omega
      rw [← this, hpart]
  rw [hrun]
  rw [dropChoice_choiceCfg] at heq; exact heq

/-! ## The verdict is the path's verdict -/

private theorem andBit_eq_true_iff {x y : List Bool}
    (hx : x = [true] ∨ x = [false]) (hy : y = [true] ∨ y = [false]) :
    andBit x y = [true] ↔ x = [true] ∧ y = [true] := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [andBit]

/-- The predicate the verdict computes: after `|c|` steps along the choice bits
of `c`, the machine has halted with `1` on the first output cell. -/
def PathAccepts (tm : NTM k) (x c : List Bool) : Prop :=
  (tm.trace c.length (fun j => c[j.val]'j.isLt) (tm.initCfg x)).state = tm.qhalt ∧
    (tm.trace c.length (fun j => c[j.val]'j.isLt) (tm.initCfg x)).output.cells 1 = Γ.one

/-- **The algebra's verdict is the path's verdict.** -/
theorem acceptChoiceFn_eq_true_iff (tm : NTM k) (u x c : List Bool)
    (hlen : x.length + c.length + Fintype.card tm.Q + 3 ≤ u.length) :
    acceptChoiceFn tm u x c = [true] ↔ PathAccepts tm x c := by
  classical
  have hu1 : 1 ≤ u.length := by omega
  have hR : clockRuler u = blockRuler (u.length - 1) := clockRuler_eq hu1
  have hq : Fintype.card tm.Q ≤ blockWidth (u.length - 1) := by
    rw [blockWidth]; omega
  set W := u.length - 1 with hWdef
  set c' := TM.runCfg (NTM.choiceTM tm) (choiceCfg tm x c) c.length with hc'def
  have hrun : runChoiceFn tm u x c = cfgCode W c' := by
    rw [runChoiceFn, hR, initChoiceFn_eq tm W x c (by omega) (by omega),
      iterate_stepFn_choice tm W x c hq c.length (by omega)]
  -- the state half
  have hQcard : Fintype.card (NTM.choiceTM tm).Q = Fintype.card tm.Q := rfl
  have hblk0 : (cfgBlocks W c')[0]'(by rw [cfgBlocks_length]; omega)
      = padTo (blockRuler W) (stateCode c'.state) := rfl
  have hstate : blockAt (clockRuler u) (runChoiceFn tm u x c) 0
      = padTo (blockRuler W) (stateCode c'.state) := by
    rw [hrun, hR, blockAt_cfgCode W c' 0 (by rw [cfgBlocks_length]; omega), hblk0]
  have hcard : (stateCode c'.state).length = (stateCode tm.qhalt).length := by
    rw [stateCode_length, stateCode_length]
    exact hQcard
  have hstateiff : matchPrefix (stateCode tm.qhalt)
      (blockAt (clockRuler u) (runChoiceFn tm u x c) 0) = [true] ↔ c'.state = tm.qhalt := by
    rw [hstate, matchPrefix_eq_true_iff,
      padTo_eq_append _ _ (by
        rw [stateCode_length, blockRuler_length, hQcard, blockWidth]
        omega)]
    constructor
    · rintro ⟨t, ht⟩
      have := List.append_inj_left ht hcard.symm
      exact (stateCode_injective this).symm
    · intro h
      rw [h]
      exact ⟨_, rfl⟩
  -- the output half
  obtain ⟨hinvs, hheads⟩ := cfgTapes_runCfg_choiceCfg_inv tm x c c.length W (by omega)
  have hmem : c'.output ∈ cfgTapes c' := by simp [cfgTapes]
  have hinv : c'.output.StartInvariant := hinvs _ hmem
  have hhead : c'.output.head ≤ W := hheads _ hmem
  obtain ⟨hb3, hb4⟩ := blockAt_cfgCode_tape W c' 1 (by rw [cfgTapes_length]; omega)
  have hidx : (cfgTapes c')[1]'(by rw [cfgTapes_length]; omega) = c'.output := rfl
  rw [hidx, show 2 * 1 + 1 = 3 from rfl] at hb3
  rw [hidx, show 2 * 1 + 2 = 4 from rfl] at hb4
  have hpair : blockAt (clockRuler u) (runChoiceFn tm u x c) 3
      ++ blockAt (clockRuler u) (runChoiceFn tm u x c) 4 = pairCode W c'.output := by
    rw [hrun, hR, hb3, hb4, pairCode]
  have hrew : outPairChoiceFn tm u x c
      = pairCode W { head := 0, cells := c'.output.cells } := by
    rw [outPairChoiceFn, hpair, hR, iterate_rewindFn c'.output hinv hhead u.length,
      rewound c'.output (by omega)]
  have hdrop : ((outPairChoiceFn tm u x c).drop (clockRuler u).length).drop 2
      = cellsCode c'.output 1 W := by
    rw [hrew, hR, drop_pairCode_rewound, show W + 1 = 1 + W from by omega,
      cellsCode_add c'.output 0 1 W]
    rw [cellsCode_succ_left, cellsCode_zero, List.append_nil]
    cases c'.output.cells 0 <;> simp [symCode]
  have houtiff : matchPrefix (symCode Γ.one)
      (((outPairChoiceFn tm u x c).drop (clockRuler u).length).drop 2) = [true]
      ↔ c'.output.cells 1 = Γ.one := by
    rw [hdrop, show W = 1 + (W - 1) from by omega, cellsCode_add c'.output 1 1 (W - 1),
      matchPrefix_eq_true_iff]
    have hcell : cellsCode c'.output 1 1 = symCode (c'.output.cells 1) := by
      rw [cellsCode_succ_left, cellsCode_zero, List.append_nil]
    rw [hcell]
    constructor
    · rintro ⟨t, ht⟩
      have hl : (symCode Γ.one).length = (symCode (c'.output.cells 1)).length := by
        cases c'.output.cells 1 <;> rfl
      exact (symCode_injective (List.append_inj_left ht hl)).symm
    · rintro h
      rw [h]
      exact ⟨_, rfl⟩
  -- assemble
  rw [acceptChoiceFn, andBit_eq_true_iff (matchPrefix_flag _ _) (matchPrefix_flag _ _),
    hstateiff, houtiff]
  have htrace : NTM.dropChoice c' = tm.trace c.length (fun j => c[j.val]'j.isLt)
      (tm.initCfg x) := by
    rw [hc'def, dropChoice_runCfg_choiceCfg]
    congr 1
    funext j
    exact choiceStream_choiceCfg tm x c j.val j.isLt
  have hstate' : c'.state = (tm.trace c.length (fun j => c[j.val]'j.isLt)
      (tm.initCfg x)).state := by rw [← htrace]; rfl
  have hout' : c'.output = (tm.trace c.length (fun j => c[j.val]'j.isLt)
      (tm.initCfg x)).output := by rw [← htrace]; rfl
  rw [hstate', hout']
  rfl

end Cobham

end Complexity
