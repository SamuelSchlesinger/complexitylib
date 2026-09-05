/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.SAT.CookLevin.Internal.EmitterFamilies
public import Complexitylib.Models.TuringMachine.Registers.Probe

/-!
# The start-clause family emitter

`startClausesF` pins row 0 of the tableau: the start state, the three head
positions, and every initial cell symbol. The cell symbols of tape 0 are
the input bits, so their unit clauses are emitted by a probe loop — load
the variable's positional part, `symProbeTM` the input symbol index into
the scratch, emit. Tapes 1 and 2 are blank beyond `▷`, so their loops are
ordinary constant-digit clause loops.
-/


@[expose] public section

namespace Complexity

namespace SAT

open TM Tableau

open Emit

/-- The symbol-index map, packaged for the probe. -/
def fSym : Γ → Fin 4 := fun s => ⟨symIdx s, symIdx_lt s⟩

/-- The probe's bound fits the budget. -/
theorem probeBudget {p d M : ℕ} (hp : p ≤ M) (hd : d ≤ M) :
    3 * p + 2 * d + 20 ≤ opBudget M :=
  le_opBudget_of_le (by nlinarith)

/-- The four constant start clauses: start state and the three heads. -/
noncomputable def startConstD (N : NTM 1) : List (List (LitDesc nT)) :=
  [[⟨true, 0, .inr 0, .inr (stateIdx N N.qstart), .inr 0, .inr 0⟩],
   [⟨true, 3, .inr 0, .inr 0, .inr 0, .inr 0⟩],
   [⟨true, 3, .inr 0, .inr 1, .inr 0, .inr 0⟩],
   [⟨true, 3, .inr 0, .inr 2, .inr 0, .inr 0⟩]]

/-- **The constant start clauses emitter.** -/
noncomputable def emitStartConstTM (N : NTM 1) : TM nT :=
  emitCNFTM rA rB rC rD tmp tmp2 (startConstD N)

/-- **`emitStartConstTM` Hoare specification.** -/
theorem emitStartConstTM_hoareTime (N : NTM 1) (steps P M : ℕ)
    (hM : 4 * (steps + 1) * (max (Fintype.card N.Q) 3) * (P + 2) * 4 ≤ M)
    (inp₀ : Tape) (work₀ : Fin nT → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hrA : work₀ rA = regTape (steps + 1))
    (hrB : work₀ rB = regTape (max (Fintype.card N.Q) 3))
    (hrC : work₀ rC = regTape (P + 2))
    (hrD : work₀ rD = regTape 4) :
    (emitStartConstTM N).HoareTime
      (EmitPred inp₀ (scratch work₀ tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch work₀ tmp tmp2 0)
        (ys ++ CNF.encode
          [[⟨true, vStateF (Fintype.card N.Q) steps P 0 (stateIdx N N.qstart)⟩],
           [⟨true, vHeadF (Fintype.card N.Q) steps P 0 0 0⟩],
           [⟨true, vHeadF (Fintype.card N.Q) steps P 0 1 0⟩],
           [⟨true, vHeadF (Fintype.card N.Q) steps P 0 2 0⟩]]))
      (cnfBudget 4 1 M) := by
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hM
  have hf : List.Forall₂
      (List.Forall₂ (LitDesc.Spec work₀ tmp tmp2 M (steps + 1)
        (max (Fintype.card N.Q) 3) (P + 2) 4))
      (startConstD N)
      [[⟨true, vStateF (Fintype.card N.Q) steps P 0 (stateIdx N N.qstart)⟩],
       [⟨true, vHeadF (Fintype.card N.Q) steps P 0 0 0⟩],
       [⟨true, vHeadF (Fintype.card N.Q) steps P 0 1 0⟩],
       [⟨true, vHeadF (Fintype.card N.Q) steps P 0 2 0⟩]] := by
    rw [startConstD]
    refine .cons (.cons ?_ .nil) (.cons (.cons ?_ .nil)
      (.cons (.cons ?_ .nil) (.cons (.cons ?_ .nil) .nil)))
    · obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 0) (by omega)
        (show 0 < steps + 1 by omega)
        (lt_of_lt_of_le (stateIdx_lt N N.qstart) (le_max_left _ 3))
        (show 0 < P + 2 by omega) (show (0:ℕ) < 4 by omega) hM
      exact ⟨0, stateIdx N N.qstart, 0, 0, rfl, rfl, rfl, rfl, rfl, rfl,
        k0, k1, k2, k3, k4⟩
    · obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 3) (by omega)
        (show 0 < steps + 1 by omega)
        (show 0 < max (Fintype.card N.Q) 3 by omega)
        (show 0 < P + 2 by omega) (show (0:ℕ) < 4 by omega) hM
      exact ⟨0, 0, 0, 0, rfl, rfl, rfl, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
    · obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 3) (by omega)
        (show 0 < steps + 1 by omega)
        (show 1 < max (Fintype.card N.Q) 3 by omega)
        (show 0 < P + 2 by omega) (show (0:ℕ) < 4 by omega) hM
      exact ⟨0, 1, 0, 0, rfl, rfl, rfl, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
    · obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 3) (by omega)
        (show 0 < steps + 1 by omega)
        (show 2 < max (Fintype.card N.Q) 3 by omega)
        (show 0 < P + 2 by omega) (show (0:ℕ) < 4 by omega) hM
      exact ⟨0, 2, 0, 0, rfl, rfl, rfl, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
  exact emitCNFTM_hoareTime rA rB rC rD tmp tmp2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    hAM hBM hCM hDM inp₀ hinp₀ hf
    (L := 1)
    (by
      intro descs hdescs
      rw [startConstD] at hdescs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hdescs
      rcases hdescs with rfl | rfl | rfl | rfl <;> simp)
    ys hwork₀ hrA hrB hrC hrD

-- ════════════════════════════════════════════════════════════════════════
-- The blank-tape cell loops (tapes 1 and 2)
-- ════════════════════════════════════════════════════════════════════════

/-- The cell unit clause at position read from `pos1Reg`, constant symbol
    digit `d`. -/
def startCellD (tp d : ℕ) : LitDesc nT :=
  ⟨true, 2, .inr 0, .inr tp, .inl pos1Reg, .inr d⟩

/-- One start-cell block for tape `tp ∈ {1,2}`: the `▷` clause at position
    0, then the blank clauses at positions `1..P`. -/
def startBlankPartTM (tp : ℕ) : TM nT :=
  seqTM (emitCNFTM rA rB rC rD tmp tmp2
      [[⟨true, 2, .inr 0, .inr tp, .inr 0, .inr 3⟩]])
    (seqTM (setConstTM pos1Reg 1)
      (seqTM (emitLoopTM (emitClauseTM rA rB rC rD tmp tmp2
          [startCellD tp 2]) pos1Reg pReg)
        (setConstTM pos1Reg 0)))

/-- Budget of one blank-tape start block. -/
def startBlankBudget (M : ℕ) : ℕ :=
  cnfBudget 1 1 M + 1
    + (opBudget M + 1 + (loopBudget M (clauseBudget 1 M) + 1 + opBudget M))

/-- **`startBlankPartTM` Hoare specification** (tape `tp ∈ {1,2}`). -/
theorem startBlankPartTM_hoareTime (tp : ℕ) (htp1 : 1 ≤ tp) (htp : tp < 3)
    (x : List Bool) (Qc steps P M : ℕ)
    (hM : 4 * (steps + 1) * (max Qc 3) * (P + 2) * 4 ≤ M)
    (inp₀ : Tape) (V : Fin nT → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hV : ∀ j, Parked (V j))
    (hVrA : V rA = regTape (steps + 1)) (hVrB : V rB = regTape (max Qc 3))
    (hVrC : V rC = regTape (P + 2)) (hVrD : V rD = regTape 4)
    (hVp1 : V pos1Reg = regTape 0) (hVpReg : V pReg = regTape P) :
    (startBlankPartTM tp).HoareTime
      (EmitPred inp₀ (scratch V tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch V tmp tmp2 0)
        (ys ++ CNF.encode ((List.range (P + 1)).map (fun pos =>
          ([⟨true, vCellF Qc steps P 0 tp pos
            (symIdx (initCellSym x tp pos))⟩] : Clause)))))
      (startBlankBudget M) := by
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hM
  -- Normalize the family: position 0 pins `▷`, the rest pin blanks.
  have hnorm : (List.range (P + 1)).map (fun pos =>
      ([⟨true, vCellF Qc steps P 0 tp pos
        (symIdx (initCellSym x tp pos))⟩] : Clause))
      = ([⟨true, vCellF Qc steps P 0 tp 0 3⟩] : Clause)
        :: (List.range P).map (fun j =>
          ([⟨true, vCellF Qc steps P 0 tp (1 + j) 2⟩] : Clause)) := by
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map,
      Function.comp_def, List.cons.injEq]
    refine ⟨⟨rfl, trivial⟩, ?_⟩
    refine List.map_congr_left fun j _ => ?_
    show ([⟨true, vCellF Qc steps P 0 tp (j + 1)
      (symIdx (initCellSym x tp (j + 1)))⟩] : Clause)
      = [⟨true, vCellF Qc steps P 0 tp (1 + j) 2⟩]
    rw [show initCellSym x tp (j + 1) = Γ.blank from by
        rw [initCellSym, ite_eq_right (by omega), ite_eq_right (by omega)],
      show (1 : ℕ) + j = j + 1 from by omega]
    rfl
  -- Stage 1: the position-0 clause.
  have h₀ : (emitCNFTM rA rB rC rD tmp tmp2
      [[⟨true, 2, .inr 0, .inr tp, .inr 0, .inr 3⟩]]).HoareTime
      (EmitPred inp₀ (scratch V tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch V tmp tmp2 0)
        (ys ++ CNF.encode [([⟨true, vCellF Qc steps P 0 tp 0 3⟩] : Clause)]))
      (cnfBudget 1 1 M) := by
    have hf : List.Forall₂
        (List.Forall₂ (LitDesc.Spec V tmp tmp2 M (steps + 1) (max Qc 3)
          (P + 2) 4))
        [[⟨true, 2, .inr 0, .inr tp, .inr 0, .inr 3⟩]]
        [[⟨true, vCellF Qc steps P 0 tp 0 3⟩]] := by
      refine .cons (.cons ?_ .nil) .nil
      obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega)
        (show 0 < steps + 1 by omega) (show tp < max Qc 3 by omega)
        (show 0 < P + 2 by omega) (show (3:ℕ) < 4 by omega) hM
      exact ⟨0, tp, 0, 3, rfl, rfl, rfl, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
    exact emitCNFTM_hoareTime rA rB rC rD tmp tmp2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hAM hBM hCM hDM inp₀ hinp₀ hf (L := 1)
      (by intro descs hdescs; simp at hdescs; subst hdescs; simp)
      ys hV hVrA hVrB hVrC hVrD
  -- Stage 2: position counter to 1.
  set ys₁ : List Bool :=
    ys ++ CNF.encode [([⟨true, vCellF Qc steps P 0 tp 0 3⟩] : Clause)]
    with hys₁
  have h₁ : (setConstTM pos1Reg 1).HoareTime
      (EmitPred inp₀ (scratch V tmp tmp2 0) ys₁)
      (EmitPred inp₀
        (Function.update (scratch V tmp tmp2 0) pos1Reg (regTape 1)) ys₁)
      (opBudget M) := by
    refine ((setConstTM_hoareTime pos1Reg 1 0 inp₀ (scratch V tmp tmp2 0) ys₁
      hinp₀ (scratch_parked 0 hV)
      (by rw [scratch_apply_ne (by decide) (by decide)]; exact hVp1)
      ).consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
      (setConstTM_le_opBudget (by omega) (by omega)))
  -- Stage 3: the blank clauses at positions 1..P.
  have hbody : ∀ j, j < P →
      (emitClauseTM rA rB rC rD tmp tmp2 [startCellD tp 2]).HoareTime
        (EmitPred inp₀
          (Function.update
            (Function.update
              (Function.update (scratch V tmp tmp2 0) pos1Reg (regTape 1))
              pos1Reg (regTape (1 + j))) pReg ⟨j + 2, regCells P⟩)
          (ys₁ ++ (List.range j).flatMap (fun j' =>
            Clause.encode ([⟨true, vCellF Qc steps P 0 tp (1 + j') 2⟩] : Clause)
              ++ [true, false])))
        (EmitPred inp₀
          (Function.update
            (Function.update
              (Function.update (scratch V tmp tmp2 0) pos1Reg (regTape 1))
              pos1Reg (regTape (1 + j))) pReg ⟨j + 2, regCells P⟩)
          (ys₁ ++ (List.range (j + 1)).flatMap (fun j' =>
            Clause.encode ([⟨true, vCellF Qc steps P 0 tp (1 + j') 2⟩] : Clause)
              ++ [true, false])))
        (clauseBudget 1 M) := by
    intro j hj
    set base : Fin nT → Tape :=
      Function.update (Function.update V pos1Reg (regTape (1 + j))) pReg
        ⟨j + 2, regCells P⟩ with hbase
    have hstate : Function.update
        (Function.update
          (Function.update (scratch V tmp tmp2 0) pos1Reg (regTape 1)) pos1Reg
          (regTape (1 + j))) pReg ⟨j + 2, regCells P⟩
        = scratch base tmp tmp2 0 := by
      rw [Function.update_idem, scratch_update_comm (by decide) (by decide),
        scratch_update_comm (by decide) (by decide)]
    have hbaseP : ∀ l, Parked (base l) :=
      parked_update (parked_update hV (parked_regTape _))
        (parked_regCells (by omega))
    have hbp : base pos1Reg = regTape (1 + j) := by
      rw [hbase, Function.update_of_ne (by decide), Function.update_self]
    have hf : List.Forall₂
        (LitDesc.Spec base tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4)
        [startCellD tp 2]
        ([⟨true, vCellF Qc steps P 0 tp (1 + j) 2⟩] : Clause) := by
      refine .cons ?_ .nil
      obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega)
        (show 0 < steps + 1 by omega) (show tp < max Qc 3 by omega)
        (show 1 + j < P + 2 by omega) (show (2:ℕ) < 4 by omega) hM
      exact ⟨0, tp, 1 + j, 2, rfl, rfl, ⟨hbp, by decide, by decide⟩, rfl,
        rfl, rfl, k0, k1, k2, k3, k4⟩
    have hcl := emitClauseTM_hoareTime rA rB rC rD tmp tmp2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hAM hBM hCM hDM hf
      (L := 1) (by simp)
      inp₀
      (ys₁ ++ (List.range j).flatMap (fun j' =>
        Clause.encode ([⟨true, vCellF Qc steps P 0 tp (1 + j') 2⟩] : Clause)
          ++ [true, false]))
      hinp₀ hbaseP
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hVrA)
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hVrB)
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hVrC)
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hVrD)
    rw [hstate]
    refine hcl.strengthen_post ?_
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, g2, ?_⟩
    rw [flatMap_range_succ, ← List.append_assoc]
    exact g3
  have hloop := emitLoopFrom_hoareTime
    (emitClauseTM rA rB rC rD tmp tmp2 [startCellD tp 2]) pos1Reg pReg
    (by decide) 1 P M (clauseBudget 1 M) (by omega)
    (fun j' => Clause.encode
      ([⟨true, vCellF Qc steps P 0 tp (1 + j') 2⟩] : Clause) ++ [true, false])
    inp₀ (Function.update (scratch V tmp tmp2 0) pos1Reg (regTape 1)) ys₁ hinp₀
    (parked_update (scratch_parked 0 hV) (parked_regTape _))
    (by rw [Function.update_of_ne (by decide),
      scratch_apply_ne (by decide) (by decide)]; exact hVpReg)
    (by rw [Function.update_self])
    hbody
  -- Stage 4: position counter back to 0.
  have h₃ : (setConstTM pos1Reg 0).HoareTime
      (EmitPred inp₀
        (Function.update
          (Function.update (scratch V tmp tmp2 0) pos1Reg (regTape 1)) pos1Reg
          (regTape (1 + P)))
        (ys₁ ++ (List.range P).flatMap (fun j' =>
          Clause.encode ([⟨true, vCellF Qc steps P 0 tp (1 + j') 2⟩] : Clause)
            ++ [true, false])))
      (EmitPred inp₀ (scratch V tmp tmp2 0)
        (ys₁ ++ (List.range P).flatMap (fun j' =>
          Clause.encode ([⟨true, vCellF Qc steps P 0 tp (1 + j') 2⟩] : Clause)
            ++ [true, false])))
      (opBudget M) := by
    refine ((setConstTM_hoareTime pos1Reg 0 (1 + P) inp₀
      (Function.update
        (Function.update (scratch V tmp tmp2 0) pos1Reg (regTape 1)) pos1Reg
        (regTape (1 + P))) _ hinp₀
      (parked_update (parked_update (scratch_parked 0 hV) (parked_regTape _))
        (parked_regTape _))
      (by rw [Function.update_self])).consequence
      (fun _ _ _ h => h) ?_
      (setConstTM_le_opBudget (show (0:ℕ) ≤ M by omega) (show 1 + P ≤ M by omega)))
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, Function.update_idem, Function.update_idem,
      show regTape 0 = scratch V tmp tmp2 0 pos1Reg from by
        rw [scratch_apply_ne (by decide) (by decide)]; exact hVp1.symm,
      Function.update_eq_self]
  -- Glue.
  have h₂₃ := seqTM_hoareTime _ (setConstTM pos1Reg 0)
    (hloop.mono_bound (loop_le_loopBudget (show P ≤ M by omega)))
    (emitPred_transition hinp₀
      (parked_update (parked_update (scratch_parked 0 hV) (parked_regTape _))
        (parked_regTape _)) _) h₃
  have h₁₂₃ := seqTM_hoareTime (setConstTM pos1Reg 1) _ h₁
    (emitPred_transition hinp₀
      (parked_update (scratch_parked 0 hV) (parked_regTape _)) _) h₂₃
  have hall := seqTM_hoareTime
    (emitCNFTM rA rB rC rD tmp tmp2
      [[⟨true, 2, .inr 0, .inr tp, .inr 0, .inr 3⟩]]) _ h₀
    (emitPred_transition hinp₀ (scratch_parked 0 hV) _) h₁₂₃
  refine hall.consequence (fun _ _ _ h => h) ?_
    (by rw [startBlankBudget])
  rintro inp work out ⟨g1, g2, g3⟩
  refine ⟨g1, g2, ?_⟩
  rw [hnorm, CNF.encode_cons, CNF.encode_map]
  rw [hys₁] at g3
  simp only [CNF.encode_cons, CNF.encode_nil, List.append_nil,
    List.append_assoc] at g3 ⊢
  exact g3


-- ════════════════════════════════════════════════════════════════════════
-- The input-tape cell loop (tape 0): probe the input per position
-- ════════════════════════════════════════════════════════════════════════

/-- The probe loop body: load the positional part of the cell variable,
    probe the input symbol index into the scratch, emit the unit clause. -/
def startProbeBodyTM : TM nT :=
  seqTM (loadFlatVarTM rA rB rC rD tmp tmp2 2 (.inr 0) (.inr 0)
      (.inl pos1Reg) (.inr 0))
    (seqTM (symProbeTM fSym pos1Reg tmp)
      (seqTM (emitLitTM true tmp)
        (seqTM (emitBitsTM [true, false])
          (seqTM (setConstTM tmp 0) (setConstTM tmp2 0)))))

/-- The input-tape start-cell block. -/
def startProbePartTM : TM nT :=
  seqTM (emitCNFTM rA rB rC rD tmp tmp2
      [[⟨true, 2, .inr 0, .inr 0, .inr 0, .inr 3⟩]])
    (seqTM (setConstTM pos1Reg 1)
      (seqTM (emitLoopTM startProbeBodyTM pos1Reg pReg)
        (setConstTM pos1Reg 0)))

/-- Budget of the probe body. -/
def startProbeBodyBudget (M : ℕ) : ℕ := loadBudget M + 4 * opBudget M + 7

/-- Budget of the input-tape start block. -/
def startProbeBudget (M : ℕ) : ℕ :=
  cnfBudget 1 1 M + 1
    + (opBudget M + 1
      + (loopBudget M (startProbeBodyBudget M) + 1 + opBudget M))

/-- **`startProbeBodyTM` Hoare specification** (at position `1 + j`). -/
theorem startProbeBodyTM_hoareTime (x : List Bool) (Qc steps P M j : ℕ)
    (hM : 4 * (steps + 1) * (max Qc 3) * (P + 2) * 4 ≤ M)
    (hj : j < P)
    (inp₀ : Tape) (V : Fin nT → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hhead : inp₀.head = 1)
    (hwfcell : inp₀.cells 0 = Γ.start)
    (hcells : ∀ pos, inp₀.cells pos = initCellSym x 0 pos)
    (hV : ∀ l, Parked (V l))
    (hVrA : V rA = regTape (steps + 1)) (hVrB : V rB = regTape (max Qc 3))
    (hVrC : V rC = regTape (P + 2)) (hVrD : V rD = regTape 4)
    (hVp1 : V pos1Reg = regTape (1 + j)) :
    startProbeBodyTM.HoareTime
      (EmitPred inp₀ (scratch V tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch V tmp tmp2 0)
        (ys ++ CNF.encode
          [([⟨true, vCellF Qc steps P 0 0 (1 + j)
            (symIdx (initCellSym x 0 (1 + j)))⟩] : Clause)]))
      (startProbeBodyBudget M) := by
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hM
  obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega)
    (show 0 < steps + 1 by omega) (show 0 < max Qc 3 by omega)
    (show 1 + j < P + 2 by omega) (show (0:ℕ) < 4 by omega) hM
  set Vb : ℕ :=
    (((2 * (steps + 1) + 0) * (max Qc 3) + 0) * (P + 2) + (1 + j)) * 4 + 0
    with hVb
  set kj : ℕ := (fSym (inp₀.cells (1 + j))).val with hkj
  have hkj4 : kj < 4 := (fSym (inp₀.cells (1 + j))).isLt
  have hVbkjM : Vb + kj ≤ M := by
    obtain ⟨_, _, _, _, k4'⟩ := flatCaps (tag := 2) (by omega)
      (show 0 < steps + 1 by omega) (show 0 < max Qc 3 by omega)
      (show 1 + j < P + 2 by omega) hkj4 hM
    have hre : Vb + kj
        = (((2 * (steps + 1) + 0) * (max Qc 3) + 0) * (P + 2) + (1 + j)) * 4
          + kj := by
      rw [hVb]
      omega
    omega
  -- Stage 1: load the positional part.
  have h₁ := loadFlatVarTM_hoareTime rA rB rC rD tmp tmp2 2
    (.inr 0) (.inr 0) (.inl pos1Reg) (.inr 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    M (steps + 1) (max Qc 3) (P + 2) 4 0 0 (1 + j) 0 0 0
    hAM hBM hCM hDM (by omega) (by omega) (by omega) k1 k2 k3 k4
    inp₀ (scratch V tmp tmp2 0) ys hinp₀ (scratch_parked 0 hV)
    (by rw [scratch_apply_ne (by decide) (by decide)]; exact hVrA)
    (by rw [scratch_apply_ne (by decide) (by decide)]; exact hVrB)
    (by rw [scratch_apply_ne (by decide) (by decide)]; exact hVrC)
    (by rw [scratch_apply_ne (by decide) (by decide)]; exact hVrD)
    rfl rfl
    (⟨by rw [scratch_apply_ne (by decide) (by decide)]; exact hVp1,
      by decide, by decide⟩)
    rfl
    scratch_apply_tmp (scratch_apply_tmp2 (by decide))
  rw [scratch_idem (by decide)] at h₁
  -- Stage 2: probe the input symbol into the scratch.
  have h₂ : (symProbeTM fSym pos1Reg tmp).HoareTime
      (EmitPred inp₀ (scratch V tmp tmp2 Vb) ys)
      (EmitPred inp₀
        (Function.update (scratch V tmp tmp2 Vb) tmp (regTape (Vb + kj))) ys)
      (opBudget M) :=
    ((symProbeTM_hoareTime fSym pos1Reg tmp (by decide) (1 + j) Vb
      inp₀ (scratch V tmp tmp2 Vb) ys hinp₀ hhead hwfcell
      (scratch_parked Vb hV)
      (by rw [scratch_apply_ne (by decide) (by decide)]; exact hVp1)
      scratch_apply_tmp).consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
      (probeBudget (show 1 + j ≤ M by omega) (by omega)))
  -- Stage 3: emit the literal.
  have h₃ : (emitLitTM true tmp).HoareTime
      (EmitPred inp₀
        (Function.update (scratch V tmp tmp2 Vb) tmp (regTape (Vb + kj))) ys)
      (EmitPred inp₀
        (Function.update (scratch V tmp tmp2 Vb) tmp (regTape (Vb + kj)))
        (ys ++ ([true, true] ++ List.replicate (2 * (Vb + kj)) true
          ++ [false, true])))
      (opBudget M) :=
    ((emitLitTM_hoareTime true tmp (Vb + kj) inp₀
      (Function.update (scratch V tmp tmp2 Vb) tmp (regTape (Vb + kj))) ys hinp₀
      (fun l _ => parked_update (scratch_parked Vb hV) (parked_regTape _) l)
      (by rw [Function.update_self]; exact reg_regT _)).consequence
      (fun _ _ _ h => h) (fun _ _ _ h => h) (emitLitTM_le_opBudget hVbkjM))
  -- Stage 4: the clause separator.
  have h₄ := emitBitsTM_hoareTime (n := nT) [true, false] inp₀
    (Function.update (scratch V tmp tmp2 Vb) tmp (regTape (Vb + kj)))
    (ys ++ ([true, true] ++ List.replicate (2 * (Vb + kj)) true
      ++ [false, true]))
    hinp₀ (parked_update (scratch_parked Vb hV) (parked_regTape _))
  -- Stages 5–6: reset the scratches.
  set ys' : List Bool := ys ++ ([true, true]
    ++ List.replicate (2 * (Vb + kj)) true ++ [false, true]) ++ [true, false]
    with hys'
  have h₅ : (setConstTM tmp 0).HoareTime
      (EmitPred inp₀
        (Function.update (scratch V tmp tmp2 Vb) tmp (regTape (Vb + kj))) ys')
      (EmitPred inp₀
        (Function.update (scratch V tmp tmp2 Vb) tmp (regTape 0)) ys')
      (opBudget M) := by
    refine ((setConstTM_hoareTime tmp 0 (Vb + kj) inp₀
      (Function.update (scratch V tmp tmp2 Vb) tmp (regTape (Vb + kj))) ys'
      hinp₀ (parked_update (scratch_parked Vb hV) (parked_regTape _))
      (by rw [Function.update_self])).consequence (fun _ _ _ h => h) ?_
      (setConstTM_le_opBudget (show (0:ℕ) ≤ M by omega) hVbkjM))
    rintro inp work out ⟨g1, g2, g3⟩
    exact ⟨g1, by rw [g2, Function.update_idem], g3⟩
  have h₆ : (setConstTM tmp2 0).HoareTime
      (EmitPred inp₀
        (Function.update (scratch V tmp tmp2 Vb) tmp (regTape 0)) ys')
      (EmitPred inp₀ (scratch V tmp tmp2 0) ys')
      (opBudget M) := by
    refine ((setConstTM_hoareTime tmp2 0 Vb inp₀
      (Function.update (scratch V tmp tmp2 Vb) tmp (regTape 0)) ys'
      hinp₀ (parked_update (scratch_parked Vb hV) (parked_regTape _))
      (by rw [Function.update_of_ne (by decide),
        scratch_apply_tmp2 (by decide)])).consequence
      (fun _ _ _ h => h) ?_ (setConstTM_le_opBudget (show (0:ℕ) ≤ M by omega)
        (by omega)))
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2]
    simp only [scratch]
    rw [Function.update_idem, Function.update_comm (show tmp ≠ tmp2 by decide),
      Function.update_idem]
  -- Glue.
  have h₅₆ := seqTM_hoareTime (setConstTM tmp 0) (setConstTM tmp2 0) h₅
    (emitPred_transition hinp₀
      (parked_update (scratch_parked Vb hV) (parked_regTape _)) _) h₆
  have h₄₅₆ := seqTM_hoareTime (emitBitsTM [true, false]) _ h₄
    (emitPred_transition hinp₀
      (parked_update (scratch_parked Vb hV) (parked_regTape _)) _) h₅₆
  have h₃₄₅₆ := seqTM_hoareTime (emitLitTM true tmp) _ h₃
    (emitPred_transition hinp₀
      (parked_update (scratch_parked Vb hV) (parked_regTape _)) _) h₄₅₆
  have h₂₃₄₅₆ := seqTM_hoareTime (symProbeTM fSym pos1Reg tmp) _ h₂
    (emitPred_transition hinp₀
      (parked_update (scratch_parked Vb hV) (parked_regTape _)) _) h₃₄₅₆
  have hall := seqTM_hoareTime
    (loadFlatVarTM rA rB rC rD tmp tmp2 2 (.inr 0) (.inr 0)
      (.inl pos1Reg) (.inr 0)) _ h₁
    (emitPred_transition hinp₀ (scratch_parked Vb hV) _) h₂₃₄₅₆
  refine hall.consequence (fun _ _ _ h => h) ?_ ?_
  · rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, g2, ?_⟩
    have hclause : ([([⟨true, vCellF Qc steps P 0 0 (1 + j)
          (symIdx (initCellSym x 0 (1 + j)))⟩] : Clause)] : CNF)
        = [([⟨true, Vb + kj⟩] : Clause)] := by
      rw [← hcells (1 + j)]
      rfl
    rw [hclause, CNF.encode_cons, Clause.encode_cons_word, Lit.word]
    rw [hys'] at g3
    simp only [CNF.encode_nil, Clause.encode_nil, List.append_nil,
      List.append_assoc] at g3 ⊢
    exact g3
  · rw [startProbeBodyBudget]
    simp only [List.length_cons, List.length_nil]
    omega


/-- **`startProbePartTM` Hoare specification**: the input-tape start cells. -/
theorem startProbePartTM_hoareTime (x : List Bool) (Qc steps P M : ℕ)
    (hM : 4 * (steps + 1) * (max Qc 3) * (P + 2) * 4 ≤ M)
    (inp₀ : Tape) (V : Fin nT → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hhead : inp₀.head = 1)
    (hwfcell : inp₀.cells 0 = Γ.start)
    (hcells : ∀ pos, inp₀.cells pos = initCellSym x 0 pos)
    (hV : ∀ j, Parked (V j))
    (hVrA : V rA = regTape (steps + 1)) (hVrB : V rB = regTape (max Qc 3))
    (hVrC : V rC = regTape (P + 2)) (hVrD : V rD = regTape 4)
    (hVp1 : V pos1Reg = regTape 0) (hVpReg : V pReg = regTape P) :
    startProbePartTM.HoareTime
      (EmitPred inp₀ (scratch V tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch V tmp tmp2 0)
        (ys ++ CNF.encode ((List.range (P + 1)).map (fun pos =>
          ([⟨true, vCellF Qc steps P 0 0 pos
            (symIdx (initCellSym x 0 pos))⟩] : Clause)))))
      (startProbeBudget M) := by
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hM
  have hnorm : (List.range (P + 1)).map (fun pos =>
      ([⟨true, vCellF Qc steps P 0 0 pos
        (symIdx (initCellSym x 0 pos))⟩] : Clause))
      = ([⟨true, vCellF Qc steps P 0 0 0 3⟩] : Clause)
        :: (List.range P).map (fun j =>
          ([⟨true, vCellF Qc steps P 0 0 (j + 1)
            (symIdx (initCellSym x 0 (j + 1)))⟩] : Clause)) := by
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map,
      Function.comp_def, List.cons.injEq]
    exact ⟨⟨rfl, trivial⟩, trivial⟩
  -- Stage 1: the position-0 clause.
  have h₀ : (emitCNFTM rA rB rC rD tmp tmp2
      [[⟨true, 2, .inr 0, .inr 0, .inr 0, .inr 3⟩]]).HoareTime
      (EmitPred inp₀ (scratch V tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch V tmp tmp2 0)
        (ys ++ CNF.encode [([⟨true, vCellF Qc steps P 0 0 0 3⟩] : Clause)]))
      (cnfBudget 1 1 M) := by
    have hf : List.Forall₂
        (List.Forall₂ (LitDesc.Spec V tmp tmp2 M (steps + 1) (max Qc 3)
          (P + 2) 4))
        [[⟨true, 2, .inr 0, .inr 0, .inr 0, .inr 3⟩]]
        [[⟨true, vCellF Qc steps P 0 0 0 3⟩]] := by
      refine .cons (.cons ?_ .nil) .nil
      obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega)
        (show 0 < steps + 1 by omega) (show 0 < max Qc 3 by omega)
        (show 0 < P + 2 by omega) (show (3:ℕ) < 4 by omega) hM
      exact ⟨0, 0, 0, 3, rfl, rfl, rfl, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
    exact emitCNFTM_hoareTime rA rB rC rD tmp tmp2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hAM hBM hCM hDM inp₀ hinp₀ hf (L := 1)
      (by intro descs hdescs; simp at hdescs; subst hdescs; simp)
      ys hV hVrA hVrB hVrC hVrD
  set ys₁ : List Bool :=
    ys ++ CNF.encode [([⟨true, vCellF Qc steps P 0 0 0 3⟩] : Clause)]
    with hys₁
  -- Stage 2: position counter to 1.
  have h₁ : (setConstTM pos1Reg 1).HoareTime
      (EmitPred inp₀ (scratch V tmp tmp2 0) ys₁)
      (EmitPred inp₀
        (Function.update (scratch V tmp tmp2 0) pos1Reg (regTape 1)) ys₁)
      (opBudget M) :=
    ((setConstTM_hoareTime pos1Reg 1 0 inp₀ (scratch V tmp tmp2 0) ys₁
      hinp₀ (scratch_parked 0 hV)
      (by rw [scratch_apply_ne (by decide) (by decide)]; exact hVp1)
      ).consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
      (setConstTM_le_opBudget (show (1:ℕ) ≤ M by omega) (show (0:ℕ) ≤ M by omega)))
  -- Stage 3: the probe loop over positions 1..P.
  have hbody : ∀ j, j < P → startProbeBodyTM.HoareTime
      (EmitPred inp₀
        (Function.update
          (Function.update
            (Function.update (scratch V tmp tmp2 0) pos1Reg (regTape 1))
            pos1Reg (regTape (1 + j))) pReg ⟨j + 2, regCells P⟩)
        (ys₁ ++ (List.range j).flatMap (fun j' =>
          CNF.encode [([⟨true, vCellF Qc steps P 0 0 (1 + j')
            (symIdx (initCellSym x 0 (1 + j')))⟩] : Clause)])))
      (EmitPred inp₀
        (Function.update
          (Function.update
            (Function.update (scratch V tmp tmp2 0) pos1Reg (regTape 1))
            pos1Reg (regTape (1 + j))) pReg ⟨j + 2, regCells P⟩)
        (ys₁ ++ (List.range (j + 1)).flatMap (fun j' =>
          CNF.encode [([⟨true, vCellF Qc steps P 0 0 (1 + j')
            (symIdx (initCellSym x 0 (1 + j')))⟩] : Clause)])))
      (startProbeBodyBudget M) := by
    intro j hj
    set base : Fin nT → Tape :=
      Function.update (Function.update V pos1Reg (regTape (1 + j))) pReg
        ⟨j + 2, regCells P⟩ with hbase
    have hstate : Function.update
        (Function.update
          (Function.update (scratch V tmp tmp2 0) pos1Reg (regTape 1)) pos1Reg
          (regTape (1 + j))) pReg ⟨j + 2, regCells P⟩
        = scratch base tmp tmp2 0 := by
      rw [Function.update_idem, scratch_update_comm (by decide) (by decide),
        scratch_update_comm (by decide) (by decide)]
    have hbaseP : ∀ l, Parked (base l) :=
      parked_update (parked_update hV (parked_regTape _))
        (parked_regCells (by omega))
    have hb := startProbeBodyTM_hoareTime x Qc steps P M j hM hj inp₀ base
      (ys₁ ++ (List.range j).flatMap (fun j' =>
        CNF.encode [([⟨true, vCellF Qc steps P 0 0 (1 + j')
          (symIdx (initCellSym x 0 (1 + j')))⟩] : Clause)]))
      hinp₀ hhead hwfcell hcells hbaseP
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hVrA)
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hVrB)
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hVrC)
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hVrD)
      (by rw [hbase, Function.update_of_ne (by decide), Function.update_self])
    rw [hstate]
    refine hb.strengthen_post ?_
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, g2, ?_⟩
    rw [flatMap_range_succ, ← List.append_assoc]
    exact g3
  have hloop := emitLoopFrom_hoareTime startProbeBodyTM pos1Reg pReg
    (by decide) 1 P M (startProbeBodyBudget M) (by omega)
    (fun j' => CNF.encode [([⟨true, vCellF Qc steps P 0 0 (1 + j')
      (symIdx (initCellSym x 0 (1 + j')))⟩] : Clause)])
    inp₀ (Function.update (scratch V tmp tmp2 0) pos1Reg (regTape 1)) ys₁ hinp₀
    (parked_update (scratch_parked 0 hV) (parked_regTape _))
    (by rw [Function.update_of_ne (by decide),
      scratch_apply_ne (by decide) (by decide)]; exact hVpReg)
    (by rw [Function.update_self])
    hbody
  -- Stage 4: position counter back to 0.
  have h₃ : (setConstTM pos1Reg 0).HoareTime
      (EmitPred inp₀
        (Function.update
          (Function.update (scratch V tmp tmp2 0) pos1Reg (regTape 1)) pos1Reg
          (regTape (1 + P)))
        (ys₁ ++ (List.range P).flatMap (fun j' =>
          CNF.encode [([⟨true, vCellF Qc steps P 0 0 (1 + j')
            (symIdx (initCellSym x 0 (1 + j')))⟩] : Clause)])))
      (EmitPred inp₀ (scratch V tmp tmp2 0)
        (ys₁ ++ (List.range P).flatMap (fun j' =>
          CNF.encode [([⟨true, vCellF Qc steps P 0 0 (1 + j')
            (symIdx (initCellSym x 0 (1 + j')))⟩] : Clause)])))
      (opBudget M) := by
    refine ((setConstTM_hoareTime pos1Reg 0 (1 + P) inp₀
      (Function.update
        (Function.update (scratch V tmp tmp2 0) pos1Reg (regTape 1)) pos1Reg
        (regTape (1 + P))) _ hinp₀
      (parked_update (parked_update (scratch_parked 0 hV) (parked_regTape _))
        (parked_regTape _))
      (by rw [Function.update_self])).consequence
      (fun _ _ _ h => h) ?_
      (setConstTM_le_opBudget (show (0:ℕ) ≤ M by omega) (show 1 + P ≤ M by omega)))
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, Function.update_idem, Function.update_idem,
      show regTape 0 = scratch V tmp tmp2 0 pos1Reg from by
        rw [scratch_apply_ne (by decide) (by decide)]; exact hVp1.symm,
      Function.update_eq_self]
  -- Glue.
  have h₂₃ := seqTM_hoareTime _ (setConstTM pos1Reg 0)
    (hloop.mono_bound (loop_le_loopBudget (show P ≤ M by omega)))
    (emitPred_transition hinp₀
      (parked_update (parked_update (scratch_parked 0 hV) (parked_regTape _))
        (parked_regTape _)) _) h₃
  have h₁₂₃ := seqTM_hoareTime (setConstTM pos1Reg 1) _ h₁
    (emitPred_transition hinp₀
      (parked_update (scratch_parked 0 hV) (parked_regTape _)) _) h₂₃
  have hall := seqTM_hoareTime
    (emitCNFTM rA rB rC rD tmp tmp2
      [[⟨true, 2, .inr 0, .inr 0, .inr 0, .inr 3⟩]]) _ h₀
    (emitPred_transition hinp₀ (scratch_parked 0 hV) _) h₁₂₃
  refine hall.consequence (fun _ _ _ h => h) ?_
    (by rw [startProbeBudget])
  rintro inp work out ⟨g1, g2, g3⟩
  refine ⟨g1, g2, ?_⟩
  rw [hnorm, CNF.encode_cons, CNF.encode_map]
  rw [hys₁] at g3
  rw [show (List.range P).flatMap (fun j' =>
      CNF.encode [([⟨true, vCellF Qc steps P 0 0 (1 + j')
        (symIdx (initCellSym x 0 (1 + j')))⟩] : Clause)])
    = (List.range P).flatMap (fun j =>
      Clause.encode ([⟨true, vCellF Qc steps P 0 0 (j + 1)
        (symIdx (initCellSym x 0 (j + 1)))⟩] : Clause) ++ [true, false])
    from by
    refine flatMap_congr fun j _ => ?_
    rw [CNF.encode_cons, CNF.encode_nil, List.append_nil,
      show (1 : ℕ) + j = j + 1 from by omega]] at g3
  simp only [CNF.encode_cons, CNF.encode_nil, List.append_nil,
    List.append_assoc] at g3 ⊢
  exact g3

-- ════════════════════════════════════════════════════════════════════════
-- The start family, assembled
-- ════════════════════════════════════════════════════════════════════════

/-- **The start-family emitter**: the constant clauses, then the three
    per-tape cell blocks. -/
noncomputable def emitStartTM (N : NTM 1) : TM nT :=
  seqTM (emitStartConstTM N)
    (seqTM startProbePartTM
      (seqTM (startBlankPartTM 1) (startBlankPartTM 2)))

/-- Budget of the start family. -/
def startBudget (M : ℕ) : ℕ :=
  cnfBudget 4 1 M + 1
    + (startProbeBudget M + 1 + (startBlankBudget M + 1 + startBlankBudget M))

/-- **`emitStartTM` Hoare specification**: appends the encoded start
    clauses. -/
theorem emitStartTM_hoareTime (N : NTM 1) (x : List Bool) (steps P M : ℕ)
    (hP : P = steps + x.length + 1)
    (hM : 4 * (steps + 1) * (max (Fintype.card N.Q) 3) * (P + 2) * 4 ≤ M)
    (inp₀ : Tape) (work₀ : Fin nT → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hhead : inp₀.head = 1)
    (hwfcell : inp₀.cells 0 = Γ.start)
    (hcells : ∀ pos, inp₀.cells pos = initCellSym x 0 pos)
    (hwork₀ : ∀ i, Parked (work₀ i))
    (hrA : work₀ rA = regTape (steps + 1))
    (hrB : work₀ rB = regTape (max (Fintype.card N.Q) 3))
    (hrC : work₀ rC = regTape (P + 2))
    (hrD : work₀ rD = regTape 4)
    (hp1 : work₀ pos1Reg = regTape 0)
    (hpReg : work₀ pReg = regTape P) :
    (emitStartTM N).HoareTime
      (EmitPred inp₀ (scratch work₀ tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch work₀ tmp tmp2 0)
        (ys ++ CNF.encode (startClausesF N steps x)))
      (startBudget M) := by
  have h₀ := emitStartConstTM_hoareTime N steps P M hM inp₀ work₀ ys hinp₀
    hwork₀ hrA hrB hrC hrD
  set Qc : ℕ := Fintype.card N.Q with hQc
  set ys₁ : List Bool := ys ++ CNF.encode
    [[⟨true, vStateF Qc steps P 0 (stateIdx N N.qstart)⟩],
     [⟨true, vHeadF Qc steps P 0 0 0⟩],
     [⟨true, vHeadF Qc steps P 0 1 0⟩],
     [⟨true, vHeadF Qc steps P 0 2 0⟩]] with hys₁
  have h₁ := startProbePartTM_hoareTime x Qc steps P M hM inp₀ work₀ ys₁
    hinp₀ hhead hwfcell hcells hwork₀ hrA hrB hrC hrD hp1 hpReg
  set ys₂ : List Bool := ys₁ ++ CNF.encode
    ((List.range (P + 1)).map (fun pos =>
      ([⟨true, vCellF Qc steps P 0 0 pos
        (symIdx (initCellSym x 0 pos))⟩] : Clause))) with hys₂
  have h₂ := startBlankPartTM_hoareTime 1 (by omega) (by omega) x Qc steps P M
    hM inp₀ work₀ ys₂ hinp₀ hwork₀ hrA hrB hrC hrD hp1 hpReg
  set ys₃ : List Bool := ys₂ ++ CNF.encode
    ((List.range (P + 1)).map (fun pos =>
      ([⟨true, vCellF Qc steps P 0 1 pos
        (symIdx (initCellSym x 1 pos))⟩] : Clause))) with hys₃
  have h₃ := startBlankPartTM_hoareTime 2 (by omega) (by omega) x Qc steps P M
    hM inp₀ work₀ ys₃ hinp₀ hwork₀ hrA hrB hrC hrD hp1 hpReg
  have h₂₃ := seqTM_hoareTime (startBlankPartTM 1) (startBlankPartTM 2) h₂
    (emitPred_transition hinp₀ (scratch_parked 0 hwork₀) _) h₃
  have h₁₂₃ := seqTM_hoareTime startProbePartTM _ h₁
    (emitPred_transition hinp₀ (scratch_parked 0 hwork₀) _) h₂₃
  have hall := seqTM_hoareTime (emitStartConstTM N) _ h₀
    (emitPred_transition hinp₀ (scratch_parked 0 hwork₀) _) h₁₂₃
  refine hall.consequence (fun _ _ _ h => h) ?_ (by rw [startBudget])
  rintro inp work out ⟨g1, g2, g3⟩
  refine ⟨g1, g2, ?_⟩
  rw [show startClausesF N steps x
      = ([⟨true, vStateF Qc steps P 0 (stateIdx N N.qstart)⟩] : Clause)
        :: (([[⟨true, vHeadF Qc steps P 0 0 0⟩],
             [⟨true, vHeadF Qc steps P 0 1 0⟩],
             [⟨true, vHeadF Qc steps P 0 2 0⟩]] : CNF)
          ++ ((List.range (P + 1)).map (fun pos =>
              ([⟨true, vCellF Qc steps P 0 0 pos
                (symIdx (initCellSym x 0 pos))⟩] : Clause))
            ++ ((List.range (P + 1)).map (fun pos =>
              ([⟨true, vCellF Qc steps P 0 1 pos
                (symIdx (initCellSym x 1 pos))⟩] : Clause))
              ++ ((List.range (P + 1)).map (fun pos =>
                ([⟨true, vCellF Qc steps P 0 2 pos
                  (symIdx (initCellSym x 2 pos))⟩] : Clause)) ++ []))))
      from by
    simp only [startClausesF]
    rw [← hP, ← hQc]
    rw [show List.range (1 + 2) = [0, 1, 2] from by decide]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append]]
  rw [hys₃, hys₂, hys₁] at g3
  simp only [CNF.encode_cons, CNF.encode_append, CNF.encode_nil,
    List.append_nil, List.append_assoc] at g3 ⊢
  exact g3

end SAT

end Complexity
