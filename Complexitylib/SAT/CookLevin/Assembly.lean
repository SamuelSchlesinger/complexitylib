/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.SAT.CookLevin.Internal.EmitterActive
public import Complexitylib.Classes.NP.Reduction
public import Complexitylib.Models.TuringMachine.Registers.InputLen
public import Complexitylib.Models.TuringMachine.SingleTape
public import Complexitylib.SAT.CookLevin.Internal.EmitterStart
public import Complexitylib.SAT.Headline

/-!
# The reduction emitter, assembled

`emitTM N p` computes the Cook–Levin reduction: bump the tapes, measure
the input, evaluate the time polynomial, initialize the radix and fuel
registers, and emit the seven encoded clause families of
`tableauCNFFlat N (p.eval |x|) x`.

The file then proves the running time polynomially bounded (via the
`PolyBnd` closure kit), concluding `reductionFn N (p.eval ·) ∈ FP`, the
Cook–Levin reductions `cookLevin_reduction_singleTape` /
`cookLevin_reduction`, and the headlines `NPHard_language` and
`NPComplete_language` for the SAT language `language`.
-/


public section

namespace Complexity

namespace SAT

open Complexity

open TM Tableau

open Emit

/-- The register file after initialization (`tf` = the row-loop fuel). -/
def initVals (n steps P Qc tf : ℕ) : Fin nT → ℕ := fun i =>
  if i = tFuel then tf
  else if i = nReg then n
  else if i = stepsReg then steps
  else if i = pReg then P
  else if i = rA then steps + 1
  else if i = rB then max Qc 3
  else if i = rC then P + 2
  else if i = rD then 4
  else if i = pos1Fuel then P + 1
  else if i = pos2Fuel then P
  else if i = pos3Fuel then P
  else 0

/-- The corresponding tape file. -/
def Tape.inits (n steps P Qc tf : ℕ) : Fin nT → Tape :=
  fun i => regTape (initVals n steps P Qc tf i)

/-- Every tape in the initialized register file is `Parked`. -/
theorem Tape.inits_parked (n steps P Qc tf : ℕ) :
    ∀ i, Parked (Tape.inits n steps P Qc tf i) :=
  fun _ => parked_regTape _

/-- **The register initialization chain**: input length, time polynomial,
    tableau width, radices, and position fuels. -/
noncomputable def emitInitTM (N : NTM 1) (p : Polynomial ℕ) : TM nT :=
  seqTM (inputLenRegTM nReg)
    (seqTM (polyEvalTM nReg stepsReg tmp2 p)
      (seqTM (setConstTM tmp2 0)
        (seqTM (addIntoTM stepsReg pReg)
          (seqTM (addIntoTM nReg pReg)
            (seqTM (incRegTM pReg)
              (seqTM (copyIntoTM stepsReg rA)
                (seqTM (incRegTM rA)
                  (seqTM (setConstTM rB (max (Fintype.card N.Q) 3))
                    (seqTM (copyIntoTM pReg rC)
                      (seqTM (incRegTM rC)
                        (seqTM (incRegTM rC)
                          (seqTM (setConstTM rD 4)
                            (seqTM (copyIntoTM pReg pos1Fuel)
                              (seqTM (incRegTM pos1Fuel)
                                (seqTM (copyIntoTM pReg pos2Fuel)
                                  (copyIntoTM pReg pos3Fuel))))))))))))))))

/-- Budget of the initialization chain: the polynomial evaluation plus
    sixteen register operations. -/
def initBudget (Mp M : ℕ) (p : Polynomial ℕ) : ℕ :=
  opBudget M + 1
    + (opBudget Mp + 1 + ((p.natDegree + 1) * (layerBudget Mp + 1) + 1) + 1
      + (opBudget M + 1
        + (opBudget M + 1 + (opBudget M + 1 + (opBudget M + 1
          + (opBudget M + 1 + (opBudget M + 1 + (opBudget M + 1
            + (opBudget M + 1 + (opBudget M + 1 + (opBudget M + 1
              + (opBudget M + 1 + (opBudget M + 1 + (opBudget M + 1
                + (opBudget M + 1 + opBudget M)))))))))))))))

set_option maxHeartbeats 1600000 in
/-- **`emitInitTM` Hoare specification.** From the bumped all-zero register
    file, reach the initialized file; `Mp` caps the Horner evaluation,
    `M` the tableau values. -/
theorem emitInitTM_hoareTime (N : NTM 1) (p : Polynomial ℕ) (x : List Bool)
    (steps P Mp M : ℕ)
    (hsteps : steps = p.eval x.length) (hP : P = steps + x.length + 1)
    (hMp : ∀ k, k ≤ p.natDegree + 1 →
      hornerFold x.length (List.take k (polyCoeffs p)) 0 ≤ Mp)
    (hnMp : x.length ≤ Mp)
    (hM : 4 * (steps + 1) * (max (Fintype.card N.Q) 3) * (P + 2) * 4 ≤ M)
    (ys : List Bool) :
    (emitInitTM N p).HoareTime
      (EmitPred ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ (fun _ => regTape 0) ys)
      (EmitPred ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩
        (Tape.inits x.length steps P (Fintype.card N.Q) 0) ys)
      (initBudget Mp M p) := by
  set inp₁ : Tape := ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ with hinp₁
  have hinp₀ : Parked inp₁ := parked_init_input x
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hM
  have hstepsM : steps ≤ M := by omega
  have hPMle : P + 1 ≤ M := by omega
  have hnM : x.length ≤ M := by omega
  have hstepsMp : steps ≤ Mp := by
    have := hMp (p.natDegree + 1) (le_refl _)
    rw [List.take_of_length_le (by rw [polyCoeffs_length])] at this
    rw [hsteps, ← hornerFold_polyCoeffs]
    exact this
  -- Stage 1: nReg := |x|.
  have h₁ : (inputLenRegTM nReg : TM nT).HoareTime
      (EmitPred inp₁ (fun _ => regTape 0) ys)
      (EmitPred inp₁ (Function.update (fun _ => regTape 0) nReg
        (regTape x.length)) ys)
      (opBudget M) :=
    (inputLenRegTM_hoareTime nReg x (fun _ => regTape 0) ys
      (fun _ _ => parked_regTape 0) rfl).mono_bound
      (le_opBudget_of_le (by nlinarith))
  set W₁ : Fin nT → Tape :=
    Function.update (fun _ => regTape 0) nReg (regTape x.length) with hW₁
  have hW₁P : ∀ i, Parked (W₁ i) :=
    parked_update (fun _ => parked_regTape 0) (parked_regTape _)
  -- Stage 2: stepsReg := p.eval |x|.
  have h₂ := polyEvalTM_hoareTime nReg stepsReg tmp2 (by decide) (by decide)
    (by decide) p Mp x.length 0 0 hnMp (by omega) (by omega) hMp inp₁ W₁ ys
    hinp₀ hW₁P
    (by rw [hW₁, Function.update_self])
    (by rw [hW₁, Function.update_of_ne (by decide)])
    (by rw [hW₁, Function.update_of_ne (by decide)])
  rw [← hsteps] at h₂
  set W₂ : Fin nT → Tape :=
    Function.update (Function.update W₁ tmp2 (regTape steps)) stepsReg
      (regTape steps) with hW₂
  have hW₂P : ∀ i, Parked (W₂ i) :=
    parked_update (parked_update hW₁P (parked_regTape _)) (parked_regTape _)
  -- Stage 3: tmp2 := 0.
  have h₃ : (setConstTM tmp2 0 : TM nT).HoareTime
      (EmitPred inp₁ W₂ ys)
      (EmitPred inp₁ (Function.update W₂ tmp2 (regTape 0)) ys) (opBudget M) := by
    refine ((setConstTM_hoareTime tmp2 0 steps inp₁ W₂ ys hinp₀ hW₂P
      (by show W₂ tmp2 = regTape steps; rw [hW₂, hW₁]; rfl)).mono_bound
      (setConstTM_le_opBudget (show (0:ℕ) ≤ M by omega) hstepsM))
  set W₃ : Fin nT → Tape := Function.update W₂ tmp2 (regTape 0) with hW₃
  have hW₃P : ∀ i, Parked (W₃ i) := parked_update hW₂P (parked_regTape _)
  -- Stage 4: pReg += steps.
  have h₄ : (addIntoTM stepsReg pReg : TM nT).HoareTime
      (EmitPred inp₁ W₃ ys)
      (EmitPred inp₁ (Function.update W₃ pReg (regTape steps)) ys)
      (opBudget M) := by
    refine ((addIntoTM_hoareTime stepsReg pReg (by decide) steps 0 inp₁ W₃ ys
      hinp₀ (fun i _ => hW₃P i)
      (by show W₃ stepsReg = regTape steps; rw [hW₃, hW₂, hW₁]; rfl)
      (by show W₃ pReg = regTape 0; rw [hW₃, hW₂, hW₁]; rfl)).consequence
      (fun _ _ _ h => h) ?_ (addIntoTM_le_opBudget hstepsM (by omega)))
    rintro inp work out ⟨g1, g2, g3⟩
    exact ⟨g1, by rw [g2, Nat.zero_add], g3⟩
  set W₄ : Fin nT → Tape := Function.update W₃ pReg (regTape steps) with hW₄
  have hW₄P : ∀ i, Parked (W₄ i) := parked_update hW₃P (parked_regTape _)
  -- Stage 5: pReg += |x|.
  have h₅ : (addIntoTM nReg pReg : TM nT).HoareTime
      (EmitPred inp₁ W₄ ys)
      (EmitPred inp₁ (Function.update W₄ pReg (regTape (steps + x.length))) ys)
      (opBudget M) :=
    ((addIntoTM_hoareTime nReg pReg (by decide) x.length steps inp₁ W₄ ys
      hinp₀ (fun i _ => hW₄P i)
      (by show W₄ nReg = regTape x.length; rw [hW₄, hW₃, hW₂, hW₁]; rfl)
      (by show W₄ pReg = regTape steps; rw [hW₄]; rfl)).mono_bound
      (addIntoTM_le_opBudget hnM (by omega)))
  set W₅ : Fin nT → Tape :=
    Function.update W₄ pReg (regTape (steps + x.length)) with hW₅
  have hW₅P : ∀ i, Parked (W₅ i) := parked_update hW₄P (parked_regTape _)
  -- Stage 6: pReg += 1 (pReg = P).
  have h₆ : (incRegTM pReg : TM nT).HoareTime
      (EmitPred inp₁ W₅ ys)
      (EmitPred inp₁ (Function.update W₅ pReg (regTape P)) ys)
      (opBudget M) := by
    refine ((incRegTM_hoareTime pReg (steps + x.length) inp₁ W₅ ys hinp₀
      (fun i _ => hW₅P i)
      (by show W₅ pReg = regTape (steps + x.length); rw [hW₅]; rfl)).consequence
      (fun _ _ _ h => h) ?_ (incRegTM_le_opBudget (by omega)))
    rintro inp work out ⟨g1, g2, g3⟩
    exact ⟨g1, by rw [g2, show steps + x.length + 1 = P from hP.symm], g3⟩
  set W₆ : Fin nT → Tape := Function.update W₅ pReg (regTape P) with hW₆
  have hW₆P : ∀ i, Parked (W₆ i) := parked_update hW₅P (parked_regTape _)
  -- Stage 7: rA := steps.
  have h₇ : (copyIntoTM stepsReg rA : TM nT).HoareTime
      (EmitPred inp₁ W₆ ys)
      (EmitPred inp₁ (Function.update W₆ rA (regTape steps)) ys)
      (opBudget M) :=
    ((copyIntoTM_hoareTime stepsReg rA (by decide) steps 0 inp₁ W₆ ys hinp₀
      (fun i _ => hW₆P i)
      (by show W₆ stepsReg = regTape steps; rw [hW₆, hW₅, hW₄, hW₃, hW₂, hW₁]
          rfl)
      (by show W₆ rA = regTape 0; rw [hW₆, hW₅, hW₄, hW₃, hW₂, hW₁]
          rfl)).mono_bound
      (copyIntoTM_le_opBudget hstepsM (by omega)))
  set W₇ : Fin nT → Tape := Function.update W₆ rA (regTape steps) with hW₇
  have hW₇P : ∀ i, Parked (W₇ i) := parked_update hW₆P (parked_regTape _)
  -- Stage 8: rA += 1.
  have h₈ : (incRegTM rA : TM nT).HoareTime
      (EmitPred inp₁ W₇ ys)
      (EmitPred inp₁ (Function.update W₇ rA (regTape (steps + 1))) ys)
      (opBudget M) :=
    ((incRegTM_hoareTime rA steps inp₁ W₇ ys hinp₀ (fun i _ => hW₇P i)
      (by show W₇ rA = regTape steps; rw [hW₇]; rfl)).mono_bound
      (incRegTM_le_opBudget hstepsM))
  set W₈ : Fin nT → Tape := Function.update W₇ rA (regTape (steps + 1)) with hW₈
  have hW₈P : ∀ i, Parked (W₈ i) := parked_update hW₇P (parked_regTape _)
  -- Stage 9: rB := max Qc 3.
  have h₉ : (setConstTM rB (max (Fintype.card N.Q) 3) : TM nT).HoareTime
      (EmitPred inp₁ W₈ ys)
      (EmitPred inp₁
        (Function.update W₈ rB (regTape (max (Fintype.card N.Q) 3))) ys)
      (opBudget M) :=
    ((setConstTM_hoareTime rB (max (Fintype.card N.Q) 3) 0 inp₁ W₈ ys hinp₀
      hW₈P
      (by show W₈ rB = regTape 0; rw [hW₈, hW₇, hW₆, hW₅, hW₄, hW₃, hW₂, hW₁]
          rfl)).mono_bound
      (setConstTM_le_opBudget hBM (by omega)))
  set W₉ : Fin nT → Tape :=
    Function.update W₈ rB (regTape (max (Fintype.card N.Q) 3)) with hW₉
  have hW₉P : ∀ i, Parked (W₉ i) := parked_update hW₈P (parked_regTape _)
  -- Stage 10: rC := P.
  have h₁₀ : (copyIntoTM pReg rC : TM nT).HoareTime
      (EmitPred inp₁ W₉ ys)
      (EmitPred inp₁ (Function.update W₉ rC (regTape P)) ys)
      (opBudget M) :=
    ((copyIntoTM_hoareTime pReg rC (by decide) P 0 inp₁ W₉ ys hinp₀
      (fun i _ => hW₉P i)
      (by show W₉ pReg = regTape P; rw [hW₉, hW₈, hW₇, hW₆]; rfl)
      (by show W₉ rC = regTape 0
          rw [hW₉, hW₈, hW₇, hW₆, hW₅, hW₄, hW₃, hW₂, hW₁]
          rfl)).mono_bound
      (copyIntoTM_le_opBudget (by omega) (by omega)))
  set W₁₀ : Fin nT → Tape := Function.update W₉ rC (regTape P) with hW₁₀
  have hW₁₀P : ∀ i, Parked (W₁₀ i) := parked_update hW₉P (parked_regTape _)
  -- Stage 11: rC += 1.
  have h₁₁ : (incRegTM rC : TM nT).HoareTime
      (EmitPred inp₁ W₁₀ ys)
      (EmitPred inp₁ (Function.update W₁₀ rC (regTape (P + 1))) ys)
      (opBudget M) :=
    ((incRegTM_hoareTime rC P inp₁ W₁₀ ys hinp₀ (fun i _ => hW₁₀P i)
      (by show W₁₀ rC = regTape P; rw [hW₁₀]; rfl)).mono_bound
      (incRegTM_le_opBudget (by omega)))
  set W₁₁ : Fin nT → Tape := Function.update W₁₀ rC (regTape (P + 1)) with hW₁₁
  have hW₁₁P : ∀ i, Parked (W₁₁ i) := parked_update hW₁₀P (parked_regTape _)
  -- Stage 12: rC += 1 (rC = P + 2).
  have h₁₂ : (incRegTM rC : TM nT).HoareTime
      (EmitPred inp₁ W₁₁ ys)
      (EmitPred inp₁ (Function.update W₁₁ rC (regTape (P + 2))) ys)
      (opBudget M) := by
    refine ((incRegTM_hoareTime rC (P + 1) inp₁ W₁₁ ys hinp₀
      (fun i _ => hW₁₁P i)
      (by show W₁₁ rC = regTape (P + 1); rw [hW₁₁]; rfl)).consequence
      (fun _ _ _ h => h) ?_ (incRegTM_le_opBudget hPMle))
    rintro inp work out ⟨g1, g2, g3⟩
    exact ⟨g1, by rw [g2, Function.update_idem], g3⟩
  set W₁₂ : Fin nT → Tape := Function.update W₁₁ rC (regTape (P + 2)) with hW₁₂
  have hW₁₂P : ∀ i, Parked (W₁₂ i) := parked_update hW₁₁P (parked_regTape _)
  -- Stage 13: rD := 4.
  have h₁₃ : (setConstTM rD 4 : TM nT).HoareTime
      (EmitPred inp₁ W₁₂ ys)
      (EmitPred inp₁ (Function.update W₁₂ rD (regTape 4)) ys)
      (opBudget M) :=
    ((setConstTM_hoareTime rD 4 0 inp₁ W₁₂ ys hinp₀ hW₁₂P
      (by show W₁₂ rD = regTape 0
          rw [hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆, hW₅, hW₄, hW₃, hW₂, hW₁]
          rfl)).mono_bound
      (setConstTM_le_opBudget hDM (by omega)))
  set W₁₃ : Fin nT → Tape := Function.update W₁₂ rD (regTape 4) with hW₁₃
  have hW₁₃P : ∀ i, Parked (W₁₃ i) := parked_update hW₁₂P (parked_regTape _)
  -- Stage 14: pos1Fuel := P.
  have h₁₄ : (copyIntoTM pReg pos1Fuel : TM nT).HoareTime
      (EmitPred inp₁ W₁₃ ys)
      (EmitPred inp₁ (Function.update W₁₃ pos1Fuel (regTape P)) ys)
      (opBudget M) :=
    ((copyIntoTM_hoareTime pReg pos1Fuel (by decide) P 0 inp₁ W₁₃ ys hinp₀
      (fun i _ => hW₁₃P i)
      (by show W₁₃ pReg = regTape P
          rw [hW₁₃, hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆]
          rfl)
      (by show W₁₃ pos1Fuel = regTape 0
          rw [hW₁₃, hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆, hW₅, hW₄, hW₃,
            hW₂, hW₁]
          rfl)).mono_bound
      (copyIntoTM_le_opBudget (by omega) (by omega)))
  set W₁₄ : Fin nT → Tape :=
    Function.update W₁₃ pos1Fuel (regTape P) with hW₁₄
  have hW₁₄P : ∀ i, Parked (W₁₄ i) := parked_update hW₁₃P (parked_regTape _)
  -- Stage 15: pos1Fuel += 1.
  have h₁₅ : (incRegTM pos1Fuel : TM nT).HoareTime
      (EmitPred inp₁ W₁₄ ys)
      (EmitPred inp₁ (Function.update W₁₄ pos1Fuel (regTape (P + 1))) ys)
      (opBudget M) :=
    ((incRegTM_hoareTime pos1Fuel P inp₁ W₁₄ ys hinp₀ (fun i _ => hW₁₄P i)
      (by show W₁₄ pos1Fuel = regTape P; rw [hW₁₄]; rfl)).mono_bound
      (incRegTM_le_opBudget (by omega)))
  set W₁₅ : Fin nT → Tape :=
    Function.update W₁₄ pos1Fuel (regTape (P + 1)) with hW₁₅
  have hW₁₅P : ∀ i, Parked (W₁₅ i) := parked_update hW₁₄P (parked_regTape _)
  -- Stage 16: pos2Fuel := P.
  have h₁₆ : (copyIntoTM pReg pos2Fuel : TM nT).HoareTime
      (EmitPred inp₁ W₁₅ ys)
      (EmitPred inp₁ (Function.update W₁₅ pos2Fuel (regTape P)) ys)
      (opBudget M) :=
    ((copyIntoTM_hoareTime pReg pos2Fuel (by decide) P 0 inp₁ W₁₅ ys hinp₀
      (fun i _ => hW₁₅P i)
      (by show W₁₅ pReg = regTape P
          rw [hW₁₅, hW₁₄, hW₁₃, hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆]
          rfl)
      (by show W₁₅ pos2Fuel = regTape 0
          rw [hW₁₅, hW₁₄, hW₁₃, hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆, hW₅,
            hW₄, hW₃, hW₂, hW₁]
          rfl)).mono_bound
      (copyIntoTM_le_opBudget (by omega) (by omega)))
  set W₁₆ : Fin nT → Tape :=
    Function.update W₁₅ pos2Fuel (regTape P) with hW₁₆
  have hW₁₆P : ∀ i, Parked (W₁₆ i) := parked_update hW₁₅P (parked_regTape _)
  -- Stage 17: pos3Fuel := P.
  have h₁₇ : (copyIntoTM pReg pos3Fuel : TM nT).HoareTime
      (EmitPred inp₁ W₁₆ ys)
      (EmitPred inp₁ (Function.update W₁₆ pos3Fuel (regTape P)) ys)
      (opBudget M) :=
    ((copyIntoTM_hoareTime pReg pos3Fuel (by decide) P 0 inp₁ W₁₆ ys hinp₀
      (fun i _ => hW₁₆P i)
      (by show W₁₆ pReg = regTape P
          rw [hW₁₆, hW₁₅, hW₁₄, hW₁₃, hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆]
          rfl)
      (by show W₁₆ pos3Fuel = regTape 0
          rw [hW₁₆, hW₁₅, hW₁₄, hW₁₃, hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆,
            hW₅, hW₄, hW₃, hW₂, hW₁]
          rfl)).mono_bound
      (copyIntoTM_le_opBudget (by omega) (by omega)))
  -- The final file is the initialized one.
  have hfinal : Function.update W₁₆ pos3Fuel (regTape P)
      = Tape.inits x.length steps P (Fintype.card N.Q) 0 := by
    rw [hW₁₆, hW₁₅, hW₁₄, hW₁₃, hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆, hW₅,
      hW₄, hW₃, hW₂, hW₁]
    funext i
    fin_cases i <;> rfl
  rw [hfinal] at h₁₇
  -- Glue the seventeen stages.
  have c₁₇ := h₁₇
  have c₁₆ := seqTM_hoareTime _ _ h₁₆
    (emitPred_transition hinp₀ hW₁₆P _) c₁₇
  have c₁₅ := seqTM_hoareTime _ _ h₁₅
    (emitPred_transition hinp₀ hW₁₅P _) c₁₆
  have c₁₄ := seqTM_hoareTime _ _ h₁₄
    (emitPred_transition hinp₀ hW₁₄P _) c₁₅
  have c₁₃ := seqTM_hoareTime _ _ h₁₃
    (emitPred_transition hinp₀ hW₁₃P _) c₁₄
  have c₁₂ := seqTM_hoareTime _ _ h₁₂
    (emitPred_transition hinp₀ hW₁₂P _) c₁₃
  have c₁₁ := seqTM_hoareTime _ _ h₁₁
    (emitPred_transition hinp₀ hW₁₁P _) c₁₂
  have c₁₀ := seqTM_hoareTime _ _ h₁₀
    (emitPred_transition hinp₀ hW₁₀P _) c₁₁
  have c₉ := seqTM_hoareTime _ _ h₉
    (emitPred_transition hinp₀ hW₉P _) c₁₀
  have c₈ := seqTM_hoareTime _ _ h₈
    (emitPred_transition hinp₀ hW₈P _) c₉
  have c₇ := seqTM_hoareTime _ _ h₇
    (emitPred_transition hinp₀ hW₇P _) c₈
  have c₆ := seqTM_hoareTime _ _ h₆
    (emitPred_transition hinp₀ hW₆P _) c₇
  have c₅ := seqTM_hoareTime _ _ h₅
    (emitPred_transition hinp₀ hW₅P _) c₆
  have c₄ := seqTM_hoareTime _ _ h₄
    (emitPred_transition hinp₀ hW₄P _) c₅
  have c₃ := seqTM_hoareTime _ _ h₃
    (emitPred_transition hinp₀ hW₃P _) c₄
  have c₂ := seqTM_hoareTime _ _ h₂
    (emitPred_transition hinp₀
      (parked_update (parked_update hW₁P (parked_regTape _)) (parked_regTape _)) _)
    c₃
  have c₁ := seqTM_hoareTime _ _ h₁
    (emitPred_transition hinp₀ hW₁P _) c₂
  exact c₁.mono_bound (by rw [initBudget])


-- ════════════════════════════════════════════════════════════════════════
-- The family chain
-- ════════════════════════════════════════════════════════════════════════

/-- Overwriting `tFuel` in an initialized register file just changes the
    fuel parameter. -/
theorem Tape.inits_update_tFuel (n steps P Qc tf tf' : ℕ) :
    Function.update (Tape.inits n steps P Qc tf) tFuel (regTape tf')
      = Tape.inits n steps P Qc tf' := by
  funext i
  by_cases hi : i = tFuel
  · subst hi
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne hi]
    show regTape (initVals n steps P Qc tf i) = regTape (initVals n steps P Qc tf' i)
    congr 1
    rw [initVals, initVals, ite_eq_right hi, ite_eq_right hi]

/-- Zeroing the scratch registers `tmp`/`tmp2` of an initialized register
    file is a no-op: they already hold `0`. -/
theorem scratch_initTapes (n steps P Qc tf : ℕ) :
    scratch (Tape.inits n steps P Qc tf) tmp tmp2 0
      = Tape.inits n steps P Qc tf := by
  funext i
  by_cases h1 : i = tmp
  · subst h1
    rw [scratch_apply_tmp]
    rfl
  · by_cases h2 : i = tmp2
    · subst h2
      rw [scratch_apply_tmp2 (by decide)]
      rfl
    · rw [scratch_apply_ne h1 h2]

/-- **The family chain**: fuel setups, the seven families, counter resets. -/
noncomputable def emitBodyTM (N : NTM 1) : TM nT :=
  seqTM (copyIntoTM stepsReg tFuel)
    (seqTM (incRegTM tFuel)
      (seqTM (emitOneHotStatesTM (Fintype.card N.Q))
        (seqTM (setConstTM tReg 0)
          (seqTM emitOneHotCellsTM
            (seqTM (setConstTM tReg 0)
              (seqTM emitOneHotHeadsTM
                (seqTM (emitStartTM N)
                  (seqTM (setConstTM tReg 0)
                    (seqTM (copyIntoTM stepsReg tFuel)
                      (seqTM emitFrameTM
                        (seqTM (setConstTM tReg 0)
                          (seqTM (setConstTM tPlusReg 0)
                            (seqTM (emitActiveTM N)
                              (emitAcceptTM N))))))))))))))

/-- Budget of the family chain. -/
def bodyBudget (N : NTM 1) (M : ℕ) : ℕ :=
  opBudget M + 1 + (opBudget M + 1
    + (loopBudget M (cnfBudget (1 + M * M) (M + 2) M) + 1 + (opBudget M + 1
      + (loopBudget M (cellsBodyBudget M) + 1 + (opBudget M + 1
        + (loopBudget M (headsBodyBudget M) + 1 + (startBudget M + 1
          + (opBudget M + 1 + (opBudget M + 1
            + (loopBudget M (frameRowBudget M) + 1 + (opBudget M + 1
              + (opBudget M + 1 + (loopBudget M (activeRowBudget N M) + 1
                + cnfBudget 2 1 M)))))))))))))

set_option maxHeartbeats 4000000 in
/-- **`emitBodyTM` Hoare specification**: from the initialized register file
    and empty accumulator, emit the encoded flat tableau. -/
theorem emitBodyTM_hoareTime (N : NTM 1) (x : List Bool) (steps P M : ℕ)
    (hP : P = steps + x.length + 1)
    (hM : 4 * (steps + 1) * (max (Fintype.card N.Q) 3) * (P + 2) * 4 ≤ M)
    (ys : List Bool) :
    (emitBodyTM N).HoareTime
      (EmitPred ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩
        (Tape.inits x.length steps P (Fintype.card N.Q) 0) ys)
      (fun inp _work out => inp = ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ ∧
        OutAcc (ys ++ CNF.encode (tableauCNFFlat N steps x)) out)
      (bodyBudget N M) := by
  set n : ℕ := x.length with hn
  set Qc : ℕ := Fintype.card N.Q with hQc
  set inp₁ : Tape := ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ with hinp₁
  have hinp₀ : Parked inp₁ := parked_init_input x
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hM
  have hstepsM : steps ≤ M := by omega
  set W : ℕ → Fin nT → Tape := fun tf => Tape.inits n steps P Qc tf with hW
  have hWP : ∀ tf i, Parked (W tf i) := fun tf i => parked_regTape _
  have hSW : ∀ tf, scratch (W tf) tmp tmp2 0 = W tf := fun tf =>
    scratch_initTapes ..
  -- g1a: tFuel := steps.
  have g1a : (copyIntoTM stepsReg tFuel : TM nT).HoareTime
      (EmitPred inp₁ (W 0) ys) (EmitPred inp₁ (W steps) ys) (opBudget M) := by
    refine ((copyIntoTM_hoareTime stepsReg tFuel (by decide) steps 0 inp₁
      (W 0) ys hinp₀ (fun i _ => hWP 0 i) rfl rfl).consequence
      (fun _ _ _ h => h) ?_ (copyIntoTM_le_opBudget hstepsM (by omega)))
    rintro inp work out ⟨u1, u2, u3⟩
    exact ⟨u1, by rw [u2, hW, Tape.inits_update_tFuel], u3⟩
  -- g1b: tFuel := steps + 1.
  have g1b : (incRegTM tFuel : TM nT).HoareTime
      (EmitPred inp₁ (W steps) ys) (EmitPred inp₁ (W (steps + 1)) ys)
      (opBudget M) := by
    refine ((incRegTM_hoareTime tFuel steps inp₁ (W steps) ys hinp₀
      (fun i _ => hWP steps i) rfl).consequence
      (fun _ _ _ h => h) ?_ (incRegTM_le_opBudget hstepsM))
    rintro inp work out ⟨u1, u2, u3⟩
    exact ⟨u1, by rw [u2, hW, Tape.inits_update_tFuel], u3⟩
  -- f1: the state one-hots.
  have f1 := emitOneHotStatesTM_hoareTime N steps P M hM inp₁ (W (steps + 1))
    ys hinp₀ (hWP _) rfl rfl rfl rfl rfl rfl
  set ys₁ : List Bool := ys ++ CNF.encode (oneHotStatesF N steps P) with hys₁
  -- g2: tReg := 0.
  have g2 : (setConstTM tReg 0 : TM nT).HoareTime
      (EmitPred inp₁
        (scratch (Function.update (W (steps + 1)) tReg (regTape (steps + 1)))
          tmp tmp2 0) ys₁)
      (EmitPred inp₁ (scratch (W (steps + 1)) tmp tmp2 0) ys₁)
      (opBudget M) := by
    refine ((setConstTM_hoareTime tReg 0 (steps + 1) inp₁
      (scratch (Function.update (W (steps + 1)) tReg (regTape (steps + 1)))
        tmp tmp2 0) ys₁ hinp₀
      (scratch_parked 0 (parked_update (hWP _) (parked_regTape _)))
      (by rw [scratch_apply_ne (by decide) (by decide), Function.update_self])
      ).consequence (fun _ _ _ h => h) ?_
      (setConstTM_le_opBudget (show (0:ℕ) ≤ M by omega) hAM))
    rintro inp work out ⟨u1, u2, u3⟩
    refine ⟨u1, ?_, u3⟩
    rw [u2, scratch_update_comm (by decide) (by decide), Function.update_idem,
      show regTape 0 = W (steps + 1) tReg from rfl, Function.update_eq_self]
  -- f2: the cell one-hots.
  have f2 := emitOneHotCellsTM_hoareTime Qc steps P M hM inp₁ (W (steps + 1))
    ys₁ hinp₀ (hWP _) rfl rfl rfl rfl rfl rfl rfl rfl
  set ys₂ : List Bool := ys₁ ++ CNF.encode (oneHotCellsF Qc steps P) with hys₂
  -- g3: tReg := 0.
  have g3 : (setConstTM tReg 0 : TM nT).HoareTime
      (EmitPred inp₁
        (scratch (Function.update (W (steps + 1)) tReg (regTape (steps + 1)))
          tmp tmp2 0) ys₂)
      (EmitPred inp₁ (scratch (W (steps + 1)) tmp tmp2 0) ys₂)
      (opBudget M) := by
    refine ((setConstTM_hoareTime tReg 0 (steps + 1) inp₁
      (scratch (Function.update (W (steps + 1)) tReg (regTape (steps + 1)))
        tmp tmp2 0) ys₂ hinp₀
      (scratch_parked 0 (parked_update (hWP _) (parked_regTape _)))
      (by rw [scratch_apply_ne (by decide) (by decide), Function.update_self])
      ).consequence (fun _ _ _ h => h) ?_
      (setConstTM_le_opBudget (show (0:ℕ) ≤ M by omega) hAM))
    rintro inp work out ⟨u1, u2, u3⟩
    refine ⟨u1, ?_, u3⟩
    rw [u2, scratch_update_comm (by decide) (by decide), Function.update_idem,
      show regTape 0 = W (steps + 1) tReg from rfl, Function.update_eq_self]
  -- f3: the head one-hots.
  have f3 := emitOneHotHeadsTM_hoareTime Qc steps P M hM inp₁ (W (steps + 1))
    ys₂ hinp₀ (hWP _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  set ys₃ : List Bool := ys₂ ++ CNF.encode (oneHotHeadsF Qc steps P) with hys₃
  -- f4: the start clauses (at the row-counter-dirty state).
  set V3 : Fin nT → Tape :=
    Function.update (W (steps + 1)) tReg (regTape (steps + 1)) with hV3
  have hV3P : ∀ i, Parked (V3 i) := parked_update (hWP _) (parked_regTape _)
  have f4 := emitStartTM_hoareTime N x steps P M hP hM inp₁ V3 ys₃ hinp₀ rfl
    (by rw [hinp₁]; rfl)
    (fun pos => by
      show (Tape.init (x.map Γ.ofBool)).cells pos = initCellSym x 0 pos
      rw [Tape.init, initCellSym]
      simp)
    hV3P
    (by rw [hV3, Function.update_of_ne (by decide)]; rfl)
    (by rw [hV3, Function.update_of_ne (by decide)]; rfl)
    (by rw [hV3, Function.update_of_ne (by decide)]; rfl)
    (by rw [hV3, Function.update_of_ne (by decide)]; rfl)
    (by rw [hV3, Function.update_of_ne (by decide)]; rfl)
    (by rw [hV3, Function.update_of_ne (by decide)]; rfl)
  set ys₄ : List Bool := ys₃ ++ CNF.encode (startClausesF N steps x) with hys₄
  -- g4a: tReg := 0.
  have g4a : (setConstTM tReg 0 : TM nT).HoareTime
      (EmitPred inp₁ (scratch V3 tmp tmp2 0) ys₄)
      (EmitPred inp₁ (scratch (W (steps + 1)) tmp tmp2 0) ys₄)
      (opBudget M) := by
    refine ((setConstTM_hoareTime tReg 0 (steps + 1) inp₁
      (scratch V3 tmp tmp2 0) ys₄ hinp₀ (scratch_parked 0 hV3P)
      (by rw [scratch_apply_ne (by decide) (by decide), hV3,
        Function.update_self])).consequence (fun _ _ _ h => h) ?_
      (setConstTM_le_opBudget (show (0:ℕ) ≤ M by omega) hAM))
    rintro inp work out ⟨u1, u2, u3⟩
    refine ⟨u1, ?_, u3⟩
    rw [u2, scratch_update_comm (by decide) (by decide), hV3,
      Function.update_idem,
      show regTape 0 = W (steps + 1) tReg from rfl, Function.update_eq_self]
  -- g4b: tFuel := steps.
  have g4b : (copyIntoTM stepsReg tFuel : TM nT).HoareTime
      (EmitPred inp₁ (scratch (W (steps + 1)) tmp tmp2 0) ys₄)
      (EmitPred inp₁ (scratch (W steps) tmp tmp2 0) ys₄)
      (opBudget M) := by
    refine ((copyIntoTM_hoareTime stepsReg tFuel (by decide) steps (steps + 1)
      inp₁ (scratch (W (steps + 1)) tmp tmp2 0) ys₄ hinp₀
      (fun i _ => scratch_parked 0 (hWP _) i)
      (by rw [scratch_apply_ne (by decide) (by decide)]; rfl)
      (by rw [scratch_apply_ne (by decide) (by decide)]; rfl)).consequence
      (fun _ _ _ h => h) ?_ (copyIntoTM_le_opBudget hstepsM hAM))
    rintro inp work out ⟨u1, u2, u3⟩
    refine ⟨u1, ?_, u3⟩
    rw [u2, scratch_update_comm (by decide) (by decide), hW,
      Tape.inits_update_tFuel]
  -- f5: the frame clauses.
  have f5 := emitFrameTM_hoareTime Qc steps P M hM inp₁ (W steps) ys₄ hinp₀
    (hWP _) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  set ys₅ : List Bool := ys₄ ++ CNF.encode (frameClausesF Qc steps P) with hys₅
  -- g5a: tReg := 0.
  set V5 : Fin nT → Tape :=
    Function.update (Function.update (W steps) tReg (regTape steps)) tPlusReg
      (regTape steps) with hV5
  have hV5P : ∀ i, Parked (V5 i) :=
    parked_update (parked_update (hWP _) (parked_regTape _)) (parked_regTape _)
  have g5a : (setConstTM tReg 0 : TM nT).HoareTime
      (EmitPred inp₁ (scratch V5 tmp tmp2 0) ys₅)
      (EmitPred inp₁
        (scratch (Function.update (W steps) tPlusReg (regTape steps)) tmp tmp2 0)
        ys₅)
      (opBudget M) := by
    refine ((setConstTM_hoareTime tReg 0 steps inp₁ (scratch V5 tmp tmp2 0)
      ys₅ hinp₀ (scratch_parked 0 hV5P)
      (by rw [scratch_apply_ne (by decide) (by decide), hV5,
        Function.update_of_ne (by decide), Function.update_self])
      ).consequence (fun _ _ _ h => h) ?_
      (setConstTM_le_opBudget (show (0:ℕ) ≤ M by omega) hstepsM))
    rintro inp work out ⟨u1, u2, u3⟩
    refine ⟨u1, ?_, u3⟩
    rw [u2, scratch_update_comm (by decide) (by decide), hV5]
    rw [show Function.update
        (Function.update (Function.update (W steps) tReg (regTape steps))
          tPlusReg (regTape steps)) tReg (regTape 0)
      = Function.update (Function.update (W steps) tPlusReg (regTape steps))
          tReg (regTape 0) from by
        rw [Function.update_comm (show tReg ≠ tPlusReg by decide),
          Function.update_idem,
          Function.update_comm (show tPlusReg ≠ tReg by decide)]]
    rw [show (regTape 0 : Tape)
        = Function.update (W steps) tPlusReg (regTape steps) tReg from by
      rw [Function.update_of_ne (by decide)]; rfl]
    rw [Function.update_eq_self]
  -- g5b: tPlusReg := 0.
  have g5b : (setConstTM tPlusReg 0 : TM nT).HoareTime
      (EmitPred inp₁
        (scratch (Function.update (W steps) tPlusReg (regTape steps)) tmp tmp2 0)
        ys₅)
      (EmitPred inp₁ (scratch (W steps) tmp tmp2 0) ys₅)
      (opBudget M) := by
    refine ((setConstTM_hoareTime tPlusReg 0 steps inp₁
      (scratch (Function.update (W steps) tPlusReg (regTape steps)) tmp tmp2 0)
      ys₅ hinp₀ (scratch_parked 0 (parked_update (hWP _) (parked_regTape _)))
      (by rw [scratch_apply_ne (by decide) (by decide), Function.update_self])
      ).consequence (fun _ _ _ h => h) ?_
      (setConstTM_le_opBudget (show (0:ℕ) ≤ M by omega) hstepsM))
    rintro inp work out ⟨u1, u2, u3⟩
    refine ⟨u1, ?_, u3⟩
    rw [u2, scratch_update_comm (by decide) (by decide), Function.update_idem,
      show regTape 0 = W steps tPlusReg from rfl, Function.update_eq_self]
  -- f6: the active transitions.
  have f6 := emitActiveTM_hoareTime N Qc steps P M hQc hM inp₁ (W steps) ys₅
    hinp₀ (hWP _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  set ys₆ : List Bool :=
    ys₅ ++ CNF.encode (activeTransitionClausesF N steps P) with hys₆
  -- f7: the accept clauses.
  have f7 := emitAcceptTM_hoareTime N steps P M hM inp₁ V5 ys₆ hinp₀ hV5P
    (by rw [hV5, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; rfl)
    (by rw [hV5, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; rfl)
    (by rw [hV5, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; rfl)
    (by rw [hV5, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; rfl)
    (by rw [hV5, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; rfl)
  -- Chain everything.
  have hpre1 : ∀ inp work out, EmitPred inp₁ (W (steps + 1)) ys inp work out →
      EmitPred inp₁ (scratch (W (steps + 1)) tmp tmp2 0) ys inp work out := by
    rintro inp work out ⟨u1, u2, u3⟩
    exact ⟨u1, by rw [u2, hSW], u3⟩
  have c7 : (emitAcceptTM N).HoareTime
      (EmitPred inp₁ (scratch V5 tmp tmp2 0) ys₆)
      (fun inp work out => inp = inp₁ ∧
        OutAcc (ys₆ ++ CNF.encode (acceptClausesF N steps P)) out)
      (cnfBudget 2 1 M) :=
    f7.strengthen_post (fun inp work out h => ⟨h.1, h.2.2⟩)
  have c6 := seqTM_hoareTime _ _ f6
    (emitPred_transition hinp₀ (scratch_parked 0 hV5P) _) c7
  have c5b := seqTM_hoareTime _ _ g5b
    (emitPred_transition hinp₀ (scratch_parked 0 (hWP _)) _) c6
  have c5a := seqTM_hoareTime _ _ g5a
    (emitPred_transition hinp₀
      (scratch_parked 0 (parked_update (hWP _) (parked_regTape _))) _) c5b
  have c5 := seqTM_hoareTime _ _ f5
    (emitPred_transition hinp₀ (scratch_parked 0 hV5P) _) c5a
  have c4b := seqTM_hoareTime _ _ g4b
    (emitPred_transition hinp₀ (scratch_parked 0 (hWP _)) _) c5
  have c4a := seqTM_hoareTime _ _ g4a
    (emitPred_transition hinp₀ (scratch_parked 0 (hWP _)) _) c4b
  have c4 := seqTM_hoareTime _ _ f4
    (emitPred_transition hinp₀ (scratch_parked 0 hV3P) _) c4a
  have c3 := seqTM_hoareTime _ _ f3
    (emitPred_transition hinp₀ (scratch_parked 0 hV3P) _) c4
  have c2' := seqTM_hoareTime _ _ g3
    (emitPred_transition hinp₀ (scratch_parked 0 (hWP _)) _) c3
  have c2 := seqTM_hoareTime _ _ f2
    (emitPred_transition hinp₀ (scratch_parked 0 hV3P) _) c2'
  have c1' := seqTM_hoareTime _ _ g2
    (emitPred_transition hinp₀ (scratch_parked 0 (hWP _)) _) c2
  have c1 := seqTM_hoareTime _ _ f1
    (emitPred_transition hinp₀ (scratch_parked 0 hV3P) _) c1'
  have cb := seqTM_hoareTime _ _ g1b
    (emitPred_transition hinp₀ (hWP _) _) (c1.weaken_pre hpre1)
  have ca := seqTM_hoareTime _ _ g1a
    (emitPred_transition hinp₀ (hWP _) _) cb
  refine ca.consequence (fun _ _ _ h => h) ?_ (by rw [bodyBudget])
  rintro inp work out ⟨u1, u2⟩
  refine ⟨u1, ?_⟩
  rw [show tableauCNFFlat N steps x
      = oneHotStatesF N steps P ++ oneHotCellsF Qc steps P
        ++ oneHotHeadsF Qc steps P ++ startClausesF N steps x
        ++ frameClausesF Qc steps P ++ activeTransitionClausesF N steps P
        ++ acceptClausesF N steps P from by
    rw [tableauCNFFlat, ← hP, ← hQc]]
  rw [hys₆, hys₅, hys₄, hys₃, hys₂, hys₁] at u2
  simp only [CNF.encode_append, List.append_assoc] at u2 ⊢
  exact u2


-- ════════════════════════════════════════════════════════════════════════
-- The reduction machine and its running time
-- ════════════════════════════════════════════════════════════════════════

/-- **The Cook–Levin reduction machine**: bump, initialize, emit. -/
noncomputable def emitTM (N : NTM 1) (p : Polynomial ℕ) : TM nT :=
  seqTM bumpTM (seqTM (emitInitTM N p) (emitBodyTM N))

/-- The Horner-evaluation value cap. -/
def emitMp (p : Polynomial ℕ) (n : ℕ) : ℕ :=
  ((polyCoeffs p).sum + 1) * (n + 1) ^ (p.natDegree + 1) + n

/-- The tableau value cap. -/
def emitM (N : NTM 1) (p : Polynomial ℕ) (n : ℕ) : ℕ :=
  4 * (p.eval n + 1) * (max (Fintype.card N.Q) 3)
    * (p.eval n + n + 1 + 2) * 4

/-- The reduction machine's running time. -/
def emitTime (N : NTM 1) (p : Polynomial ℕ) (n : ℕ) : ℕ :=
  1 + 1 + (initBudget (emitMp p n) (emitM N p n) p + 1
    + bodyBudget N (emitM N p n))

set_option maxHeartbeats 1600000 in
/-- **The reduction machine computes the reduction function.** -/
theorem emitTM_computesInTime (N : NTM 1) (p : Polynomial ℕ) :
    (emitTM N p).ComputesInTime (reductionFn N (fun n => p.eval n))
      (emitTime N p) := by
  intro x
  set n : ℕ := x.length with hn
  set steps : ℕ := p.eval n with hsteps
  set P : ℕ := steps + n + 1 with hP
  have hMp : ∀ k, k ≤ p.natDegree + 1 →
      hornerFold n (List.take k (polyCoeffs p)) 0 ≤ emitMp p n := by
    intro k _
    refine le_trans (hornerFold_take_le n (polyCoeffs p) k) ?_
    rw [emitMp, polyCoeffs_length]
    omega
  have hM : 4 * (steps + 1) * (max (Fintype.card N.Q) 3) * (P + 2) * 4
      ≤ emitM N p n := by
    rw [emitM, hP, hsteps]
  have hinit := emitInitTM_hoareTime N p x steps P (emitMp p n)
    (emitM N p n) hsteps hP hMp (by rw [emitMp]; omega) hM []
  have hbody := emitBodyTM_hoareTime N x steps P (emitM N p n) hP hM []
  have hbump := bumpTM_hoareTime (n := nT) x
  -- Adapters.
  have htrans₁ : ∀ (inp : Tape) (work : Fin nT → Tape) (out : Tape),
      (inp = { head := 1, cells := (Tape.init (x.map Γ.ofBool)).cells } ∧
        (∀ i, IsReg 0 (work i)) ∧ OutAcc [] out) →
      EmitPred ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ (fun _ => regTape 0) []
        (transitionInput inp) (fun i => transitionTape (work i))
        (transitionTape out) := by
    rintro inp work out ⟨rfl, hwork, hout⟩
    refine ⟨Parked.transitionInput_eq_self (parked_init_input x), ?_, ?_⟩
    · funext i
      rw [Parked.transitionTape_eq_self ((hwork i).parked), (hwork i).eq_regT]
    · rw [Parked.transitionTape_eq_self hout.parked]
      exact hout
  have htrans₂ : ∀ inp work out,
      EmitPred ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩
        (Tape.inits n steps P (Fintype.card N.Q) 0) [] inp work out →
      EmitPred ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩
        (Tape.inits n steps P (Fintype.card N.Q) 0) []
        (transitionInput inp) (fun i => transitionTape (work i))
        (transitionTape out) :=
    emitPred_transition (parked_init_input x)
      (fun _ => parked_regTape _) []
  have hchain := seqTM_hoareTime bumpTM (seqTM (emitInitTM N p) (emitBodyTM N))
    hbump htrans₁
    (seqTM_hoareTime (emitInitTM N p) (emitBodyTM N) hinit htrans₂ hbody)
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ := hchain
    (Tape.init (x.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
    ⟨rfl, fun _ => rfl, rfl⟩
  refine ⟨c', t, le_trans ht (by rw [emitTime]), hreach, hhalt, ?_⟩
  show c'.output.HasOutput (reductionFn N (fun n => p.eval n) x)
  have : reductionFn N (fun n => p.eval n) x
      = CNF.encode (tableauCNFFlat N steps x) := rfl
  rw [this]
  exact TM.OutAcc.hasOutput hpost.2

-- ════════════════════════════════════════════════════════════════════════
-- Polynomial boundedness of the running time
-- ════════════════════════════════════════════════════════════════════════

/-- Dominated by a `Polynomial ℕ` evaluation. -/
def PolyBnd (f : ℕ → ℕ) : Prop := ∃ q : Polynomial ℕ, ∀ n, f n ≤ q.eval n

namespace PolyBnd

/-- Constant functions are polynomially bounded. -/
theorem const (c : ℕ) : PolyBnd (fun _ => c) :=
  ⟨Polynomial.C c, fun n => by simp⟩

/-- The identity function is polynomially bounded. -/
theorem id : PolyBnd (fun n => n) :=
  ⟨Polynomial.X, fun n => by simp⟩

/-- Polynomial boundedness is closed under pointwise addition. -/
theorem add {f g : ℕ → ℕ} (hf : PolyBnd f) (hg : PolyBnd g) :
    PolyBnd (fun n => f n + g n) := by
  obtain ⟨q₁, h₁⟩ := hf
  obtain ⟨q₂, h₂⟩ := hg
  exact ⟨q₁ + q₂, fun n => by
    rw [Polynomial.eval_add]
    exact Nat.add_le_add (h₁ n) (h₂ n)⟩

/-- Polynomial boundedness is closed under pointwise multiplication. -/
theorem mul {f g : ℕ → ℕ} (hf : PolyBnd f) (hg : PolyBnd g) :
    PolyBnd (fun n => f n * g n) := by
  obtain ⟨q₁, h₁⟩ := hf
  obtain ⟨q₂, h₂⟩ := hg
  exact ⟨q₁ * q₂, fun n => by
    rw [Polynomial.eval_mul]
    exact Nat.mul_le_mul (h₁ n) (h₂ n)⟩

/-- A function pointwise below a polynomially bounded one is itself
    polynomially bounded. -/
theorem mono {f g : ℕ → ℕ} (hg : PolyBnd g) (h : ∀ n, f n ≤ g n) :
    PolyBnd f := by
  obtain ⟨q, hq⟩ := hg
  exact ⟨q, fun n => le_trans (h n) (hq n)⟩

/-- Polynomial boundedness is closed under a fixed power. -/
theorem pow {f : ℕ → ℕ} (hf : PolyBnd f) (k : ℕ) :
    PolyBnd (fun n => f n ^ k) := by
  induction k with
  | zero => exact ⟨1, fun _ => by simp⟩
  | succ k ih =>
    refine PolyBnd.mono (PolyBnd.mul ih hf) fun n => ?_
    rw [pow_succ]

/-- Evaluating a `Polynomial ℕ` is polynomially bounded (by itself). -/
theorem eval (p : Polynomial ℕ) : PolyBnd (fun n => p.eval n) :=
  ⟨p, fun _ => le_refl _⟩

end PolyBnd

/-- Budget compositions preserve polynomial boundedness. -/
theorem PolyBnd.opBudget {f : ℕ → ℕ} (hf : PolyBnd f) :
    PolyBnd (fun n => opBudget (f n)) := by
  have h2 : PolyBnd (fun n => f n + 2) := hf.add (PolyBnd.const 2)
  exact (PolyBnd.const 32).mul ((h2.mul h2).mul h2)

/-- `layerBudget` of a polynomially bounded value cap is polynomially
    bounded. -/
theorem PolyBnd.layerBudget {f : ℕ → ℕ} (hf : PolyBnd f) :
    PolyBnd (fun n => layerBudget (f n)) :=
  ((PolyBnd.const 4).mul hf.opBudget).add (PolyBnd.const 3)

/-- `loadBudget` of a polynomially bounded value cap is polynomially
    bounded. -/
theorem PolyBnd.loadBudget {f : ℕ → ℕ} (hf : PolyBnd f) :
    PolyBnd (fun n => loadBudget (f n)) :=
  (hf.opBudget.add ((PolyBnd.const 4).mul hf.layerBudget)).add
    (PolyBnd.const 4)

/-- `emitVarBudget` of a polynomially bounded value cap is polynomially
    bounded. -/
theorem PolyBnd.emitVarBudget {f : ℕ → ℕ} (hf : PolyBnd f) :
    PolyBnd (fun n => emitVarBudget (f n)) :=
  (hf.loadBudget.add hf.opBudget).add (PolyBnd.const 1)

/-- `clauseBudget` with polynomially bounded length and value cap is
    polynomially bounded. -/
theorem PolyBnd.clauseBudget {L : ℕ → ℕ} {f : ℕ → ℕ} (hL : PolyBnd L)
    (hf : PolyBnd f) : PolyBnd (fun n => clauseBudget (L n) (f n)) :=
  ((hL.mul (hf.emitVarBudget.add (PolyBnd.const 1))).add
    ((PolyBnd.const 2).mul hf.opBudget)).add (PolyBnd.const 6)

/-- `cnfBudget` with polynomially bounded clause count, clause length, and
    value cap is polynomially bounded. -/
theorem PolyBnd.cnfBudget {K L f : ℕ → ℕ} (hK : PolyBnd K) (hL : PolyBnd L)
    (hf : PolyBnd f) : PolyBnd (fun n => cnfBudget (K n) (L n) (f n)) :=
  (hK.mul ((hL.clauseBudget hf).add (PolyBnd.const 1))).add (PolyBnd.const 1)

/-- `loopBudget` with polynomially bounded iteration count and body budget
    is polynomially bounded. -/
theorem PolyBnd.loopBudget {f inner : ℕ → ℕ} (hf : PolyBnd f)
    (hinner : PolyBnd inner) :
    PolyBnd (fun n => loopBudget (f n) (inner n)) :=
  (hf.mul (((hinner.add (PolyBnd.const 1)).add hf.opBudget).add
    (PolyBnd.const 2))).add (hf.add (PolyBnd.const 2))


/-- **The running time is polynomially bounded.** A mechanical walk over the
    budget definitions with the `PolyBnd` closure kit. -/
theorem emitTime_polyBnd (N : NTM 1) (p : Polynomial ℕ) :
    PolyBnd (emitTime N p) := by
  have hM : PolyBnd (emitM N p) := by
    rw [show emitM N p = fun n => 4 * (p.eval n + 1)
      * (max (Fintype.card N.Q) 3) * (p.eval n + n + 1 + 2) * 4 from rfl]
    exact ((((PolyBnd.const 4).mul
      ((PolyBnd.eval p).add (PolyBnd.const 1))).mul
      (PolyBnd.const (max (Fintype.card N.Q) 3))).mul
      ((((PolyBnd.eval p).add PolyBnd.id).add (PolyBnd.const 1)).add
        (PolyBnd.const 2))).mul (PolyBnd.const 4)
  have hMp : PolyBnd (emitMp p) := by
    rw [show emitMp p = fun n => ((polyCoeffs p).sum + 1)
      * (n + 1) ^ (p.natDegree + 1) + n from rfl]
    exact ((PolyBnd.const ((polyCoeffs p).sum + 1)).mul
      ((PolyBnd.id.add (PolyBnd.const 1)).pow (p.natDegree + 1))).add
      PolyBnd.id
  have hop : PolyBnd (fun n => opBudget (emitM N p n)) := hM.opBudget
  have h1 : PolyBnd (fun n => cnfBudget (1 + emitM N p n * emitM N p n)
      (emitM N p n + 2) (emitM N p n)) :=
    PolyBnd.cnfBudget ((PolyBnd.const 1).add (hM.mul hM))
      (hM.add (PolyBnd.const 2)) hM
  have hstates : PolyBnd (fun n => loopBudget (emitM N p n)
      (cnfBudget (1 + emitM N p n * emitM N p n) (emitM N p n + 2)
        (emitM N p n))) := hM.loopBudget h1
  have hposChunk : PolyBnd (fun n => posChunkBudget (emitM N p n)) := by
    rw [show (fun n => posChunkBudget (emitM N p n)) = fun n =>
      loopBudget (emitM N p n) (cnfBudget 17 6 (emitM N p n)) + 1
        + opBudget (emitM N p n) from rfl]
    exact ((hM.loopBudget (PolyBnd.cnfBudget (PolyBnd.const 17)
      (PolyBnd.const 6) hM)).add (PolyBnd.const 1)).add hop
  have hcellsBody : PolyBnd (fun n => cellsBodyBudget (emitM N p n)) :=
    ((PolyBnd.const 3).mul hposChunk).add (PolyBnd.const 2)
  have hcells : PolyBnd (fun n => loopBudget (emitM N p n)
      (cellsBodyBudget (emitM N p n))) := hM.loopBudget hcellsBody
  have hAtLeast : PolyBnd (fun n => headAtLeastBudget (emitM N p n)) := by
    rw [show (fun n => headAtLeastBudget (emitM N p n)) = fun n =>
      loopBudget (emitM N p n) (emitVarBudget (emitM N p n) + 1
        + (2 * opBudget (emitM N p n) + 1)) + 1
        + (2 + 1 + opBudget (emitM N p n)) from rfl]
    exact ((hM.loopBudget ((hM.emitVarBudget.add (PolyBnd.const 1)).add
      (((PolyBnd.const 2).mul hop).add (PolyBnd.const 1)))).add
      (PolyBnd.const 1)).add (((PolyBnd.const 2).add (PolyBnd.const 1)).add
      hop)
  have hpairBody : PolyBnd (fun n => pairBodyBudget (emitM N p n)) := by
    rw [show (fun n => pairBodyBudget (emitM N p n)) = fun n =>
      loopBudget (emitM N p n) (clauseBudget 2 (emitM N p n))
        + 4 * opBudget (emitM N p n) + 4 from rfl]
    exact ((hM.loopBudget (PolyBnd.clauseBudget (PolyBnd.const 2) hM)).add
      ((PolyBnd.const 4).mul hop)).add (PolyBnd.const 4)
  have hAtMost : PolyBnd (fun n => headAtMostBudget (emitM N p n)) :=
    ((hM.loopBudget hpairBody).add (PolyBnd.const 1)).add hop
  have hheadLeaf : PolyBnd (fun n => headLeafBudget (emitM N p n)) :=
    (hop.add (PolyBnd.const 1)).add ((hAtLeast.add (PolyBnd.const 1)).add
      hAtMost)
  have hheadsBody : PolyBnd (fun n => headsBodyBudget (emitM N p n)) :=
    ((PolyBnd.const 3).mul hheadLeaf).add (PolyBnd.const 2)
  have hheads : PolyBnd (fun n => loopBudget (emitM N p n)
      (headsBodyBudget (emitM N p n))) := hM.loopBudget hheadsBody
  have hblank : PolyBnd (fun n => startBlankBudget (emitM N p n)) := by
    rw [show (fun n => startBlankBudget (emitM N p n)) = fun n =>
      cnfBudget 1 1 (emitM N p n) + 1 + (opBudget (emitM N p n) + 1
        + (loopBudget (emitM N p n) (clauseBudget 1 (emitM N p n)) + 1
          + opBudget (emitM N p n))) from rfl]
    exact ((PolyBnd.cnfBudget (PolyBnd.const 1) (PolyBnd.const 1) hM).add
      (PolyBnd.const 1)).add ((hop.add (PolyBnd.const 1)).add
      (((hM.loopBudget (PolyBnd.clauseBudget (PolyBnd.const 1) hM)).add
        (PolyBnd.const 1)).add hop))
  have hprobeBody : PolyBnd (fun n => startProbeBodyBudget (emitM N p n)) :=
    (hM.loadBudget.add ((PolyBnd.const 4).mul hop)).add (PolyBnd.const 7)
  have hprobe : PolyBnd (fun n => startProbeBudget (emitM N p n)) := by
    rw [show (fun n => startProbeBudget (emitM N p n)) = fun n =>
      cnfBudget 1 1 (emitM N p n) + 1 + (opBudget (emitM N p n) + 1
        + (loopBudget (emitM N p n) (startProbeBodyBudget (emitM N p n)) + 1
          + opBudget (emitM N p n))) from rfl]
    exact ((PolyBnd.cnfBudget (PolyBnd.const 1) (PolyBnd.const 1) hM).add
      (PolyBnd.const 1)).add ((hop.add (PolyBnd.const 1)).add
      (((hM.loopBudget hprobeBody).add (PolyBnd.const 1)).add hop))
  have hstart : PolyBnd (fun n => startBudget (emitM N p n)) := by
    rw [show (fun n => startBudget (emitM N p n)) = fun n =>
      cnfBudget 4 1 (emitM N p n) + 1 + (startProbeBudget (emitM N p n) + 1
        + (startBlankBudget (emitM N p n) + 1
          + startBlankBudget (emitM N p n))) from rfl]
    exact ((PolyBnd.cnfBudget (PolyBnd.const 4) (PolyBnd.const 1) hM).add
      (PolyBnd.const 1)).add ((hprobe.add (PolyBnd.const 1)).add
      ((hblank.add (PolyBnd.const 1)).add hblank))
  have hframeChunk : PolyBnd (fun n => framePosChunkBudget (emitM N p n)) :=
    ((hM.loopBudget (PolyBnd.cnfBudget (PolyBnd.const 8) (PolyBnd.const 3)
      hM)).add (PolyBnd.const 1)).add hop
  have hframeRow : PolyBnd (fun n => frameRowBudget (emitM N p n)) :=
    (hop.add (PolyBnd.const 1)).add (((PolyBnd.const 3).mul hframeChunk).add
      (PolyBnd.const 2))
  have hframe : PolyBnd (fun n => loopBudget (emitM N p n)
      (frameRowBudget (emitM N p n))) := hM.loopBudget hframeRow
  have hleaf : PolyBnd (fun n => activeLeafBudget (emitM N p n)) :=
    (((PolyBnd.const 7).mul (PolyBnd.clauseBudget (PolyBnd.const 9) hM)).add
      ((PolyBnd.const 7).mul hop)).add (PolyBnd.const 13)
  have hbLevel : PolyBnd (fun n => activeBLevelBudget (emitM N p n)) :=
    ((PolyBnd.const 2).mul (hleaf.add (PolyBnd.const 1))).add
      (PolyBnd.const 1)
  have hsoLevel : PolyBnd (fun n => activeSoLevelBudget (emitM N p n)) :=
    ((PolyBnd.const 4).mul (hbLevel.add (PolyBnd.const 1))).add
      (PolyBnd.const 1)
  have hpoSplit : PolyBnd (fun n => activePoSplitBudget (emitM N p n)) :=
    (hsoLevel.add (PolyBnd.const 1)).add ((hop.add (PolyBnd.const 1)).add
      (((hM.loopBudget hsoLevel).add (PolyBnd.const 1)).add hop))
  have hswLevel : PolyBnd (fun n => activeSwLevelBudget (emitM N p n)) :=
    ((PolyBnd.const 4).mul (hpoSplit.add (PolyBnd.const 1))).add
      (PolyBnd.const 1)
  have hpwSplit : PolyBnd (fun n => activePwSplitBudget (emitM N p n)) :=
    (hswLevel.add (PolyBnd.const 1)).add ((hop.add (PolyBnd.const 1)).add
      (((hM.loopBudget hswLevel).add (PolyBnd.const 1)).add hop))
  have hsiLevel : PolyBnd (fun n => activeSiLevelBudget (emitM N p n)) :=
    ((PolyBnd.const 4).mul (hpwSplit.add (PolyBnd.const 1))).add
      (PolyBnd.const 1)
  have hpiLoop : PolyBnd (fun n => activePiLoopBudget (emitM N p n)) :=
    ((hM.loopBudget hsiLevel).add (PolyBnd.const 1)).add hop
  have hqLevel : PolyBnd (fun n => activeQLevelBudget N (emitM N p n)) :=
    ((PolyBnd.const (Fintype.card N.Q)).mul (hpiLoop.add
      (PolyBnd.const 1))).add (PolyBnd.const 1)
  have hrow : PolyBnd (fun n => activeRowBudget N (emitM N p n)) :=
    (hop.add (PolyBnd.const 1)).add hqLevel
  have hactive : PolyBnd (fun n => loopBudget (emitM N p n)
      (activeRowBudget N (emitM N p n))) := hM.loopBudget hrow
  have haccept : PolyBnd (fun n => cnfBudget 2 1 (emitM N p n)) :=
    PolyBnd.cnfBudget (PolyBnd.const 2) (PolyBnd.const 1) hM
  have hbody : PolyBnd (fun n => bodyBudget N (emitM N p n)) := by
    have t1 := (hactive.add (PolyBnd.const 1)).add haccept
    have t2 := (hop.add (PolyBnd.const 1)).add t1
    have t3 := (hop.add (PolyBnd.const 1)).add t2
    have t4 := (hframe.add (PolyBnd.const 1)).add t3
    have t5 := (hop.add (PolyBnd.const 1)).add t4
    have t6 := (hop.add (PolyBnd.const 1)).add t5
    have t7 := (hstart.add (PolyBnd.const 1)).add t6
    have t8 := (hheads.add (PolyBnd.const 1)).add t7
    have t9 := (hop.add (PolyBnd.const 1)).add t8
    have t10 := (hcells.add (PolyBnd.const 1)).add t9
    have t11 := (hop.add (PolyBnd.const 1)).add t10
    have t12 := (hstates.add (PolyBnd.const 1)).add t11
    have t13 := (hop.add (PolyBnd.const 1)).add t12
    exact (hop.add (PolyBnd.const 1)).add t13
  have hopMp : PolyBnd (fun n => opBudget (emitMp p n)) := hMp.opBudget
  have hinit : PolyBnd (fun n =>
      initBudget (emitMp p n) (emitM N p n) p) := by
    have hpoly := ((hopMp.add (PolyBnd.const 1)).add
      (((PolyBnd.const (p.natDegree + 1)).mul
        (hMp.layerBudget.add (PolyBnd.const 1))).add
        (PolyBnd.const 1))).add (PolyBnd.const 1)
    have t1 := (hop.add (PolyBnd.const 1)).add hop
    have t2 := (hop.add (PolyBnd.const 1)).add t1
    have t3 := (hop.add (PolyBnd.const 1)).add t2
    have t4 := (hop.add (PolyBnd.const 1)).add t3
    have t5 := (hop.add (PolyBnd.const 1)).add t4
    have t6 := (hop.add (PolyBnd.const 1)).add t5
    have t7 := (hop.add (PolyBnd.const 1)).add t6
    have t8 := (hop.add (PolyBnd.const 1)).add t7
    have t9 := (hop.add (PolyBnd.const 1)).add t8
    have t10 := (hop.add (PolyBnd.const 1)).add t9
    have t11 := (hop.add (PolyBnd.const 1)).add t10
    have t12 := (hop.add (PolyBnd.const 1)).add t11
    have t13 := (hop.add (PolyBnd.const 1)).add t12
    have t14 := (hop.add (PolyBnd.const 1)).add t13
    exact (hop.add (PolyBnd.const 1)).add (hpoly.add t14)
  exact ((PolyBnd.const 1).add (PolyBnd.const 1)).add
    ((hinit.add (PolyBnd.const 1)).add hbody)

/-- **The reduction is polynomial-time computable** — for an explicit
    polynomial time bound `n ↦ p.eval n`. The tableau has size polynomial in
    `p.eval |x|` (hence in `|x|`), and `emitTM` emits its encoding in
    polynomial time. -/
theorem reductionFn_mem_FP (N : NTM 1) (p : Polynomial ℕ) :
    reductionFn N (fun n => p.eval n) ∈ FP := by
  obtain ⟨q, hq⟩ := emitTime_polyBnd N p
  exact ⟨q.natDegree, nT, emitTM N p, emitTime N p,
    emitTM_computesInTime N p, Complexity.BigO.of_polynomial_bound q hq⟩

/-- **Single-tape Cook–Levin reduction.** A single-work-tape machine deciding
    `L` in polynomial time yields a polynomial-time many-one reduction to
    `language`. The abstract bound `T` is first replaced by a dominating explicit
    polynomial (`BigO.pow_polynomial_bound`), since the reduction function is
    only computable for explicit bounds; deciding transfers by
    monotonicity. -/
theorem cookLevin_reduction_singleTape {L : Language} (N : NTM 1) (T : ℕ → ℕ)
    (c : ℕ) (hdec : N.DecidesInTime L T) (hTO : T =O (· ^ c)) :
    L ≤ₚ language := by
  obtain ⟨p, hp⟩ := hTO.pow_polynomial_bound
  exact ⟨reductionFn N (fun n => p.eval n), reductionFn_mem_FP N p,
    tableauCNF_correct N _ (hdec.mono hp)⟩

/-- **Per-machine Cook–Levin reduction.** If a nondeterministic machine `N`
    decides `L` within a polynomial time bound, then `L` polynomial-time
    many-one reduces to `language`. Reduces to the single-work-tape case
    (`NTM.exists_singleTape_decidesInTime`) and then builds the tableau formula. -/
theorem cookLevin_reduction {k : ℕ} {L : Language} (N : NTM k) (T : ℕ → ℕ)
    (c : ℕ) (hdec : N.DecidesInTime L T) (hTO : T =O (· ^ c)) :
    L ≤ₚ language := by
  obtain ⟨N', T', c', hdec', hTO'⟩ := N.exists_singleTape_decidesInTime hdec hTO
  exact cookLevin_reduction_singleTape N' T' c' hdec' hTO'

/-- **NP-hardness of SAT.** Every language in `NP` polynomial-time reduces to
    `language`. -/
theorem NPHard_language : NPHard language := by
  intro L hL
  obtain ⟨d, hLd⟩ := Set.mem_iUnion.mp hL
  obtain ⟨k, N, f, hdec, hfO⟩ := hLd
  exact cookLevin_reduction N f d hdec hfO

/-- **Cook–Levin theorem: SAT is NP-complete.** -/
theorem NPComplete_language : NPComplete language :=
  ⟨language_mem_NP, NPHard_language⟩

end SAT

end Complexity
