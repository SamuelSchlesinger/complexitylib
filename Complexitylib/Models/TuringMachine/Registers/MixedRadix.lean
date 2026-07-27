/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Registers.Horner

/-!
# Mixed-radix variable loading and literal emission

The Cook–Levin tableau's flat variable indices are mixed-radix numerals
`(((tag·A + a)·B + b)·C + c)·D + d`. `loadFlatVarTM` computes one such
index into the scratch register `tmp` by a `setConstTM` followed by four
Horner layers, where each digit comes either from a register (a loop
counter) or a hardwired constant, and each radix comes from a register.
`emitVarLitTM` then appends the encoded literal for that variable to the
output accumulator.

These two machines are the per-literal unit of every clause-family emitter:
a clause is a `bigSeqTM` of `emitVarLitTM`s followed by the clause
separator.
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- A digit source for the mixed-radix loader: a register index or a
    hardwired constant. -/
abbrev DigitSrc (n : ℕ) := Fin n ⊕ ℕ

/-- The source `s` supplies the value `w`: either a register (disjoint from
    the scratches) currently holding `w`, or the constant `w` itself. -/
def DigitSrcSpec (work₀ : Fin n → Tape) (tmp tmp2 : Fin n) : DigitSrc n → ℕ → Prop
  | .inl r, w => work₀ r = regTape w ∧ r ≠ tmp ∧ r ≠ tmp2
  | .inr c, w => c = w

/-- One mixed-radix step: `tmp := tmp · X + (digit from s)`. -/
def hornerStepTM (X tmp tmp2 : Fin n) : DigitSrc n → TM n
  | .inl r => hornerLayerRegTM X r tmp tmp2
  | .inr c => hornerLayerConstTM X tmp tmp2 c

/-- **`hornerStepTM` Hoare specification** (raw form, arbitrary scratch
    values). -/
theorem hornerStepTM_hoareTime {X tmp tmp2 : Fin n} (s : DigitSrc n)
    (hXt : X ≠ tmp) (hXt2 : X ≠ tmp2) (htt2 : tmp ≠ tmp2)
    (M x v w u : ℕ) (hx : x ≤ M) (hv : v ≤ M) (hu : u ≤ M)
    (hres : v * x + w ≤ M)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hX : work₀ X = regTape x) (hs : DigitSrcSpec work₀ tmp tmp2 s w)
    (ht : work₀ tmp = regTape v) (ht2 : work₀ tmp2 = regTape u) :
    (hornerStepTM X tmp tmp2 s).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀
        (Function.update (Function.update work₀ tmp2 (regTape (v * x + w))) tmp
          (regTape (v * x + w))) ys)
      (layerBudget M) := by
  cases s with
  | inl r =>
    obtain ⟨hr, _, hrt2⟩ := hs
    exact hornerLayerRegTM_hoareTime hXt hXt2 htt2 hrt2 M x v w u hx hv hu hres
      inp₀ work₀ ys hinp₀ hwork₀ hX hr ht ht2
  | inr c =>
    obtain rfl : c = w := hs
    exact hornerLayerConstTM_hoareTime hXt hXt2 htt2 M x v c u hx hv hu hres
      inp₀ work₀ ys hinp₀ hwork₀ hX ht ht2

/-- The canonical scratch state after a mixed-radix stage: both scratches
    hold `z`, everything else is `work₀`. -/
def scratch (work₀ : Fin n → Tape) (tmp tmp2 : Fin n) (z : ℕ) : Fin n → Tape :=
  Function.update (Function.update work₀ tmp2 (regTape z)) tmp (regTape z)

/-- A scratch state built from a parked register family is parked on every tape. -/
theorem scratch_parked {work₀ : Fin n → Tape} {tmp tmp2 : Fin n} (z : ℕ)
    (hwork₀ : ∀ i, Parked (work₀ i)) : ∀ i, Parked (scratch work₀ tmp tmp2 z i) := by
  intro i
  rw [scratch]
  by_cases hi : i = tmp
  · subst hi; rw [Function.update_self]; exact parked_regTape _
  · rw [Function.update_of_ne hi]
    by_cases hi2 : i = tmp2
    · subst hi2; rw [Function.update_self]; exact parked_regTape _
    · rw [Function.update_of_ne hi2]; exact hwork₀ i

/-- `scratch` leaves every register other than the two scratches unchanged. -/
theorem scratch_apply_ne {work₀ : Fin n → Tape} {tmp tmp2 : Fin n} {z : ℕ}
    {i : Fin n} (hit : i ≠ tmp) (hit2 : i ≠ tmp2) :
    scratch work₀ tmp tmp2 z i = work₀ i := by
  rw [scratch, Function.update_of_ne hit, Function.update_of_ne hit2]

/-- In the scratch state at `z`, the register `tmp` holds `z`. -/
theorem scratch_apply_tmp {work₀ : Fin n → Tape} {tmp tmp2 : Fin n} {z : ℕ} :
    scratch work₀ tmp tmp2 z tmp = regTape z := by
  rw [scratch, Function.update_self]

/-- In the scratch state at `z`, the register `tmp2` holds `z` (when the scratches differ). -/
theorem scratch_apply_tmp2 {work₀ : Fin n → Tape} {tmp tmp2 : Fin n} {z : ℕ}
    (htt2 : tmp ≠ tmp2) : scratch work₀ tmp tmp2 z tmp2 = regTape z := by
  rw [scratch, Function.update_of_ne (fun h => htt2 h.symm), Function.update_self]

/-- Updating a parked family with a parked tape stays parked. -/
theorem parked_update {W : Fin n → Tape} (hW : ∀ i, Parked (W i)) {j : Fin n}
    {t : Tape} (ht : Parked t) : ∀ i, Parked (Function.update W j t i) := by
  intro i
  by_cases hij : i = j
  · subst hij; rw [Function.update_self]; exact ht
  · rw [Function.update_of_ne hij]; exact hW i

/-- Updates at other registers slide past the scratch pair. -/
theorem scratch_update_comm {work₀ : Fin n → Tape} {tmp tmp2 i : Fin n}
    (hit : i ≠ tmp) (hit2 : i ≠ tmp2) (z : ℕ) (t : Tape) :
    Function.update (scratch work₀ tmp tmp2 z) i t
      = scratch (Function.update work₀ i t) tmp tmp2 z := by
  simp only [scratch]
  rw [Function.update_comm (fun h => hit h.symm),
    Function.update_comm (fun h => hit2 h.symm)]

/-- Scratching twice keeps only the second value. -/
theorem scratch_idem {work₀ : Fin n → Tape} {tmp tmp2 : Fin n}
    (htt2 : tmp ≠ tmp2) (z z' : ℕ) :
    scratch (scratch work₀ tmp tmp2 z) tmp tmp2 z' = scratch work₀ tmp tmp2 z' := by
  simp only [scratch]
  rw [Function.update_comm htt2, Function.update_idem, Function.update_idem]

/-- Source specifications survive scratching (sources avoid the scratches). -/
theorem DigitSrcSpec.scratch {work₀ : Fin n → Tape} {tmp tmp2 : Fin n} {s : DigitSrc n}
    {w : ℕ} (hs : DigitSrcSpec work₀ tmp tmp2 s w) (z : ℕ) :
    DigitSrcSpec (TM.scratch work₀ tmp tmp2 z) tmp tmp2 s w := by
  cases s with
  | inl r =>
    obtain ⟨hr, hrt, hrt2⟩ := hs
    exact ⟨by rw [scratch_apply_ne hrt hrt2]; exact hr, hrt, hrt2⟩
  | inr c => exact hs

/-- **`hornerStepTM` on canonical scratch states.** The composable form:
    scratches at `v` in, scratches at `v·x + w` out. -/
theorem hornerStepTM_hoareTime_scratch (X tmp tmp2 : Fin n) (s : DigitSrc n)
    (hXt : X ≠ tmp) (hXt2 : X ≠ tmp2) (htt2 : tmp ≠ tmp2)
    (M x v w : ℕ) (hx : x ≤ M) (hv : v ≤ M) (hres : v * x + w ≤ M)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hX : work₀ X = regTape x) (hs : DigitSrcSpec work₀ tmp tmp2 s w) :
    (hornerStepTM X tmp tmp2 s).HoareTime
      (EmitPred inp₀ (scratch work₀ tmp tmp2 v) ys)
      (EmitPred inp₀ (scratch work₀ tmp tmp2 (v * x + w)) ys)
      (layerBudget M) := by
  have hs' : DigitSrcSpec (scratch work₀ tmp tmp2 v) tmp tmp2 s w := by
    cases s with
    | inl r =>
      obtain ⟨hr, hrt, hrt2⟩ := hs
      exact ⟨by rw [scratch_apply_ne hrt hrt2]; exact hr, hrt, hrt2⟩
    | inr c => exact hs
  have hraw := hornerStepTM_hoareTime s hXt hXt2 htt2 M x v w v hx hv hv hres
    inp₀ (scratch work₀ tmp tmp2 v) ys hinp₀ (scratch_parked v hwork₀)
    (scratch_apply_ne hXt hXt2 ▸ hX) hs'
    scratch_apply_tmp (scratch_apply_tmp2 htt2)
  refine hraw.strengthen_post ?_
  rintro inp work out ⟨g1, g2, g3⟩
  refine ⟨g1, ?_, g3⟩
  rw [g2]
  simp only [scratch]
  rw [Function.update_comm htt2, Function.update_idem, Function.update_idem]

-- ════════════════════════════════════════════════════════════════════════
-- loadFlatVarTM: compute a mixed-radix variable index into tmp
-- ════════════════════════════════════════════════════════════════════════

/-- **Load the mixed-radix numeral** `(((tag·A + a)·B + b)·C + c)·D + d` into
    `tmp` (and `tmp2`), with radices read from registers `rA rB rC rD` and
    digits from the sources `sa sb sc sd`. -/
def loadFlatVarTM (rA rB rC rD tmp tmp2 : Fin n) (tag : ℕ)
    (sa sb sc sd : DigitSrc n) : TM n :=
  seqTM (setConstTM tmp tag)
    (seqTM (hornerStepTM rA tmp tmp2 sa)
      (seqTM (hornerStepTM rB tmp tmp2 sb)
        (seqTM (hornerStepTM rC tmp tmp2 sc) (hornerStepTM rD tmp tmp2 sd))))

/-- Time budget of `loadFlatVarTM`. -/
def loadBudget (M : ℕ) : ℕ := opBudget M + 4 * layerBudget M + 4

/-- **`loadFlatVarTM` Hoare specification.** All four radices from registers,
    all intermediate numeral values capped by `M`; ends on the canonical
    scratch state at the full numeral. -/
theorem loadFlatVarTM_hoareTime (rA rB rC rD tmp tmp2 : Fin n) (tag : ℕ)
    (sa sb sc sd : DigitSrc n)
    (hAt : rA ≠ tmp) (hAt2 : rA ≠ tmp2) (hBt : rB ≠ tmp) (hBt2 : rB ≠ tmp2)
    (hCt : rC ≠ tmp) (hCt2 : rC ≠ tmp2) (hDt : rD ≠ tmp) (hDt2 : rD ≠ tmp2)
    (htt2 : tmp ≠ tmp2)
    (M A B C D a b c d v u : ℕ)
    (hA : A ≤ M) (hB : B ≤ M) (hC : C ≤ M) (hD : D ≤ M)
    (htag : tag ≤ M) (hv : v ≤ M) (hu : u ≤ M)
    (h1 : tag * A + a ≤ M)
    (h2 : (tag * A + a) * B + b ≤ M)
    (h3 : ((tag * A + a) * B + b) * C + c ≤ M)
    (h4 : (((tag * A + a) * B + b) * C + c) * D + d ≤ M)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hrA : work₀ rA = regTape A) (hrB : work₀ rB = regTape B)
    (hrC : work₀ rC = regTape C) (hrD : work₀ rD = regTape D)
    (hsa : DigitSrcSpec work₀ tmp tmp2 sa a) (hsb : DigitSrcSpec work₀ tmp tmp2 sb b)
    (hsc : DigitSrcSpec work₀ tmp tmp2 sc c) (hsd : DigitSrcSpec work₀ tmp tmp2 sd d)
    (ht : work₀ tmp = regTape v) (ht2 : work₀ tmp2 = regTape u) :
    (loadFlatVarTM rA rB rC rD tmp tmp2 tag sa sb sc sd).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀
        (scratch work₀ tmp tmp2 ((((tag * A + a) * B + b) * C + c) * D + d)) ys)
      (loadBudget M) := by
  -- Stage 0: tmp := tag.
  have h₀ : (setConstTM tmp tag).HoareTime (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ (Function.update work₀ tmp (regTape tag)) ys) (opBudget M) :=
    (setConstTM_hoareTime tmp tag v inp₀ work₀ ys hinp₀ hwork₀ ht).mono_bound
      (setConstTM_le_opBudget htag hv)
  set W0 : Fin n → Tape := Function.update work₀ tmp (regTape tag) with hW0
  have hW0P : ∀ i, Parked (W0 i) := by
    intro i
    by_cases hi : i = tmp
    · subst hi; rw [hW0, Function.update_self]; exact parked_regTape _
    · rw [hW0, Function.update_of_ne hi]; exact hwork₀ i
  -- Stage 1 (raw form: pre is W0, not a canonical scratch pair).
  have hsa' : DigitSrcSpec W0 tmp tmp2 sa a := by
    cases sa with
    | inl r =>
      obtain ⟨hr, hrt, hrt2⟩ := hsa
      exact ⟨by rw [hW0, Function.update_of_ne hrt]; exact hr, hrt, hrt2⟩
    | inr c' => exact hsa
  have h₁ : (hornerStepTM rA tmp tmp2 sa).HoareTime (EmitPred inp₀ W0 ys)
      (EmitPred inp₀ (scratch work₀ tmp tmp2 (tag * A + a)) ys)
      (layerBudget M) := by
    refine (hornerStepTM_hoareTime sa hAt hAt2 htt2 M A tag a u hA htag hu h1
      inp₀ W0 ys hinp₀ hW0P
      (by rw [hW0, Function.update_of_ne hAt]; exact hrA) hsa'
      (by rw [hW0, Function.update_self])
      (by rw [hW0, Function.update_of_ne (fun h => htt2 h.symm)];
          exact ht2)).strengthen_post ?_
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, hW0, scratch, Function.update_comm htt2, Function.update_idem]
  -- Stages 2–4 (canonical form).
  have h₂ := hornerStepTM_hoareTime_scratch rB tmp tmp2 sb hBt hBt2 htt2 M B
    (tag * A + a) b hB h1 h2 inp₀ work₀ ys hinp₀ hwork₀ hrB hsb
  have h₃ := hornerStepTM_hoareTime_scratch rC tmp tmp2 sc hCt hCt2 htt2 M C
    ((tag * A + a) * B + b) c hC h2 h3 inp₀ work₀ ys hinp₀ hwork₀ hrC hsc
  have h₄ := hornerStepTM_hoareTime_scratch rD tmp tmp2 sd hDt hDt2 htt2 M D
    (((tag * A + a) * B + b) * C + c) d hD h3 h4 inp₀ work₀ ys hinp₀ hwork₀
    hrD hsd
  -- Glue.
  have h₃₄ := seqTM_hoareTime (hornerStepTM rC tmp tmp2 sc)
    (hornerStepTM rD tmp tmp2 sd) h₃
    (emitPred_transition hinp₀ (scratch_parked _ hwork₀) ys) h₄
  have h₂₃₄ := seqTM_hoareTime (hornerStepTM rB tmp tmp2 sb) _ h₂
    (emitPred_transition hinp₀ (scratch_parked _ hwork₀) ys) h₃₄
  have h₁₂₃₄ := seqTM_hoareTime (hornerStepTM rA tmp tmp2 sa) _ h₁
    (emitPred_transition hinp₀ (scratch_parked _ hwork₀) ys) h₂₃₄
  have h := seqTM_hoareTime (setConstTM tmp tag) _ h₀
    (emitPred_transition hinp₀ hW0P ys) h₁₂₃₄
  exact h.mono_bound (by rw [loadBudget]; omega)

-- ════════════════════════════════════════════════════════════════════════
-- emitVarLitTM: emit one literal whose variable is a mixed-radix numeral
-- ════════════════════════════════════════════════════════════════════════

/-- **Emit one literal**: load the mixed-radix variable index into `tmp`,
    then append the encoded literal with sign `sign` to the output. -/
def emitVarLitTM (rA rB rC rD tmp tmp2 : Fin n) (sign : Bool) (tag : ℕ)
    (sa sb sc sd : DigitSrc n) : TM n :=
  seqTM (loadFlatVarTM rA rB rC rD tmp tmp2 tag sa sb sc sd)
    (emitLitTM sign tmp)

/-- Time budget of `emitVarLitTM`. -/
def emitVarBudget (M : ℕ) : ℕ := loadBudget M + opBudget M + 1

/-- **`emitVarLitTM` Hoare specification.** Appends
    `[sign, sign] ++ 2·var trues ++ [false, true]` for the mixed-radix
    variable index `var`, leaving the scratches at `var` and everything else
    untouched. -/
theorem emitVarLitTM_hoareTime (rA rB rC rD tmp tmp2 : Fin n) (sign : Bool)
    (tag : ℕ) (sa sb sc sd : DigitSrc n)
    (hAt : rA ≠ tmp) (hAt2 : rA ≠ tmp2) (hBt : rB ≠ tmp) (hBt2 : rB ≠ tmp2)
    (hCt : rC ≠ tmp) (hCt2 : rC ≠ tmp2) (hDt : rD ≠ tmp) (hDt2 : rD ≠ tmp2)
    (htt2 : tmp ≠ tmp2)
    (M A B C D a b c d v u : ℕ)
    (hA : A ≤ M) (hB : B ≤ M) (hC : C ≤ M) (hD : D ≤ M)
    (htag : tag ≤ M) (hv : v ≤ M) (hu : u ≤ M)
    (h1 : tag * A + a ≤ M)
    (h2 : (tag * A + a) * B + b ≤ M)
    (h3 : ((tag * A + a) * B + b) * C + c ≤ M)
    (h4 : (((tag * A + a) * B + b) * C + c) * D + d ≤ M)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hrA : work₀ rA = regTape A) (hrB : work₀ rB = regTape B)
    (hrC : work₀ rC = regTape C) (hrD : work₀ rD = regTape D)
    (hsa : DigitSrcSpec work₀ tmp tmp2 sa a) (hsb : DigitSrcSpec work₀ tmp tmp2 sb b)
    (hsc : DigitSrcSpec work₀ tmp tmp2 sc c) (hsd : DigitSrcSpec work₀ tmp tmp2 sd d)
    (ht : work₀ tmp = regTape v) (ht2 : work₀ tmp2 = regTape u) :
    (emitVarLitTM rA rB rC rD tmp tmp2 sign tag sa sb sc sd).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀
        (scratch work₀ tmp tmp2 ((((tag * A + a) * B + b) * C + c) * D + d))
        (ys ++ ([sign, sign]
          ++ List.replicate (2 * ((((tag * A + a) * B + b) * C + c) * D + d)) true
          ++ [false, true])))
      (emitVarBudget M) := by
  have hload := loadFlatVarTM_hoareTime rA rB rC rD tmp tmp2 tag sa sb sc sd
    hAt hAt2 hBt hBt2 hCt hCt2 hDt hDt2 htt2 M A B C D a b c d v u
    hA hB hC hD htag hv hu h1 h2 h3 h4 inp₀ work₀ ys hinp₀ hwork₀
    hrA hrB hrC hrD hsa hsb hsc hsd ht ht2
  set V : ℕ := (((tag * A + a) * B + b) * C + c) * D + d with hV
  have hemit : (emitLitTM sign tmp).HoareTime
      (EmitPred inp₀ (scratch work₀ tmp tmp2 V) ys)
      (EmitPred inp₀ (scratch work₀ tmp tmp2 V)
        (ys ++ ([sign, sign] ++ List.replicate (2 * V) true ++ [false, true])))
      (opBudget M) := by
    refine (emitLitTM_hoareTime sign tmp V inp₀ (scratch work₀ tmp tmp2 V) ys
      hinp₀ (fun i _ => scratch_parked V hwork₀ i) ?_).mono_bound
      (emitLitTM_le_opBudget h4)
    rw [scratch_apply_tmp]
    exact reg_regT V
  have hseq := seqTM_hoareTime
    (loadFlatVarTM rA rB rC rD tmp tmp2 tag sa sb sc sd) (emitLitTM sign tmp)
    hload (emitPred_transition hinp₀ (scratch_parked V hwork₀) ys) hemit
  exact hseq.mono_bound (by rw [emitVarBudget]; omega)

/-- **`emitVarLitTM` on canonical scratch states** — the composable form used
    by the clause emitters: scratches at any `z ≤ M` in, scratches at the
    emitted variable out. -/
theorem emitVarLitTM_hoareTime_scratch (rA rB rC rD tmp tmp2 : Fin n) (sign : Bool)
    (tag : ℕ) (sa sb sc sd : DigitSrc n)
    (hAt : rA ≠ tmp) (hAt2 : rA ≠ tmp2) (hBt : rB ≠ tmp) (hBt2 : rB ≠ tmp2)
    (hCt : rC ≠ tmp) (hCt2 : rC ≠ tmp2) (hDt : rD ≠ tmp) (hDt2 : rD ≠ tmp2)
    (htt2 : tmp ≠ tmp2)
    (M A B C D a b c d z : ℕ)
    (hA : A ≤ M) (hB : B ≤ M) (hC : C ≤ M) (hD : D ≤ M)
    (htag : tag ≤ M) (hz : z ≤ M)
    (h1 : tag * A + a ≤ M)
    (h2 : (tag * A + a) * B + b ≤ M)
    (h3 : ((tag * A + a) * B + b) * C + c ≤ M)
    (h4 : (((tag * A + a) * B + b) * C + c) * D + d ≤ M)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hrA : work₀ rA = regTape A) (hrB : work₀ rB = regTape B)
    (hrC : work₀ rC = regTape C) (hrD : work₀ rD = regTape D)
    (hsa : DigitSrcSpec work₀ tmp tmp2 sa a) (hsb : DigitSrcSpec work₀ tmp tmp2 sb b)
    (hsc : DigitSrcSpec work₀ tmp tmp2 sc c) (hsd : DigitSrcSpec work₀ tmp tmp2 sd d) :
    (emitVarLitTM rA rB rC rD tmp tmp2 sign tag sa sb sc sd).HoareTime
      (EmitPred inp₀ (scratch work₀ tmp tmp2 z) ys)
      (EmitPred inp₀
        (scratch work₀ tmp tmp2 ((((tag * A + a) * B + b) * C + c) * D + d))
        (ys ++ ([sign, sign]
          ++ List.replicate (2 * ((((tag * A + a) * B + b) * C + c) * D + d)) true
          ++ [false, true])))
      (emitVarBudget M) := by
  have hraw := emitVarLitTM_hoareTime rA rB rC rD tmp tmp2 sign tag sa sb sc sd
    hAt hAt2 hBt hBt2 hCt hCt2 hDt hDt2 htt2 M A B C D a b c d z z
    hA hB hC hD htag hz hz h1 h2 h3 h4 inp₀ (scratch work₀ tmp tmp2 z) ys
    hinp₀ (scratch_parked z hwork₀)
    (by rw [scratch_apply_ne hAt hAt2]; exact hrA)
    (by rw [scratch_apply_ne hBt hBt2]; exact hrB)
    (by rw [scratch_apply_ne hCt hCt2]; exact hrC)
    (by rw [scratch_apply_ne hDt hDt2]; exact hrD)
    (hsa.scratch z) (hsb.scratch z) (hsc.scratch z) (hsd.scratch z)
    scratch_apply_tmp (scratch_apply_tmp2 htt2)
  refine hraw.strengthen_post ?_
  rintro inp work out ⟨g1, g2, g3⟩
  exact ⟨g1, by rw [g2, scratch_idem htt2], g3⟩

-- ════════════════════════════════════════════════════════════════════════
-- resetScratchTM: return the scratches to zero
-- ════════════════════════════════════════════════════════════════════════

/-- Zero both scratch registers (the fixed point of every clause emitter). -/
def resetScratchTM (tmp tmp2 : Fin n) : TM n :=
  seqTM (setConstTM tmp 0) (setConstTM tmp2 0)

/-- **`resetScratchTM` Hoare specification**: canonical scratches at `z` to
    canonical scratches at `0`. -/
theorem resetScratchTM_hoareTime (tmp tmp2 : Fin n) (htt2 : tmp ≠ tmp2)
    (M z : ℕ) (hz : z ≤ M)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i)) :
    (resetScratchTM tmp tmp2).HoareTime
      (EmitPred inp₀ (scratch work₀ tmp tmp2 z) ys)
      (EmitPred inp₀ (scratch work₀ tmp tmp2 0) ys)
      (2 * opBudget M + 1) := by
  have h₁ : (setConstTM tmp 0).HoareTime
      (EmitPred inp₀ (scratch work₀ tmp tmp2 z) ys)
      (EmitPred inp₀
        (Function.update (Function.update work₀ tmp2 (regTape z)) tmp (regTape 0)) ys)
      (opBudget M) := by
    refine ((setConstTM_hoareTime tmp 0 z inp₀ (scratch work₀ tmp tmp2 z) ys
      hinp₀ (scratch_parked z hwork₀) scratch_apply_tmp).mono_bound
      (setConstTM_le_opBudget (by omega) hz)).strengthen_post ?_
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2]
    simp only [scratch]
    rw [Function.update_idem]
  set W : Fin n → Tape :=
    Function.update (Function.update work₀ tmp2 (regTape z)) tmp (regTape 0) with hW
  have hWP : ∀ i, Parked (W i) := by
    intro i
    by_cases hi : i = tmp
    · subst hi; rw [hW, Function.update_self]; exact parked_regTape _
    · rw [hW, Function.update_of_ne hi]
      by_cases hi2 : i = tmp2
      · subst hi2; rw [Function.update_self]; exact parked_regTape _
      · rw [Function.update_of_ne hi2]; exact hwork₀ i
  have h₂ : (setConstTM tmp2 0).HoareTime (EmitPred inp₀ W ys)
      (EmitPred inp₀ (scratch work₀ tmp tmp2 0) ys) (opBudget M) := by
    refine ((setConstTM_hoareTime tmp2 0 z inp₀ W ys hinp₀ hWP
      (by rw [hW, Function.update_of_ne (fun h => htt2 h.symm),
            Function.update_self])).mono_bound
      (setConstTM_le_opBudget (by omega) hz)).strengthen_post ?_
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, hW]
    simp only [scratch]
    rw [Function.update_comm htt2, Function.update_idem]
  exact (seqTM_hoareTime (setConstTM tmp 0) (setConstTM tmp2 0) h₁
    (emitPred_transition hinp₀ hWP ys) h₂).mono_bound (by omega)

end TM

end Complexity
