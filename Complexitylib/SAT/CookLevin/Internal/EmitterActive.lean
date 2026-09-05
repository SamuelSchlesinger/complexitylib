/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.SAT.CookLevin.Internal.EmitterFamilies

/-!
# The active-transition family emitter

`activeTransitionClausesF` quantifies over rows, machine states, three head
positions, three read symbols, and the choice bit; per tuple it emits seven
implication clauses (the eight-literal reading condition plus one
consequence each). States, symbols, and the choice bit are finite data
unrolled at definition level (`bigSeqTM` over their lists); rows and
positions are runtime loops.
-/


@[expose] public section

namespace Complexity

namespace SAT

open TM Tableau

open Emit

-- ════════════════════════════════════════════════════════════════════════
-- Generic: a bigSeq of uniform emitters emits the flatMap
-- ════════════════════════════════════════════════════════════════════════

/-- **Unrolled emission**: if every element's machine appends its word from
    any accumulator, the `bigSeqTM` of the mapped list appends the
    `flatMap`. -/
theorem bigSeq_emit_hoareTime {α : Type _} (F : α → TM nT)
    (E : α → List Bool) (b : ℕ) (inp₀ : Tape) (W : Fin nT → Tape)
    (hinp₀ : Parked inp₀) (hWP : ∀ i, Parked (W i)) :
    ∀ (l : List α),
    (∀ a ∈ l, ∀ ys, (F a).HoareTime
      (EmitPred inp₀ W ys) (EmitPred inp₀ W (ys ++ E a)) b) →
    ∀ ys, (bigSeqTM (l.map F)).HoareTime
      (EmitPred inp₀ W ys) (EmitPred inp₀ W (ys ++ l.flatMap E))
      (l.length * (b + 1) + 1) := by
  intro l
  induction l with
  | nil =>
    intro _ ys
    have hskip := skipTM_hoareTime inp₀ W ys hinp₀ hWP
    refine hskip.consequence (fun _ _ _ h => h) ?_ (by simp)
    rintro inp work out ⟨g1, g2, g3⟩
    exact ⟨g1, g2, by simpa using g3⟩
  | cons a l ih =>
    intro hspec ys
    have hhead := hspec a List.mem_cons_self ys
    have hrest := ih (fun a' ha' ys' => hspec a' (List.mem_cons_of_mem _ ha')
      ys') (ys ++ E a)
    have hseq := seqTM_hoareTime (F a) (bigSeqTM (l.map F)) hhead
      (emitPred_transition hinp₀ hWP _) hrest
    refine hseq.consequence (fun _ _ _ h => h) ?_ ?_
    · rintro inp work out ⟨g1, g2, g3⟩
      refine ⟨g1, g2, ?_⟩
      rw [List.flatMap_cons, ← List.append_assoc]
      exact g3
    · simp only [List.length_cons]
      have : (l.length + 1) * (b + 1) = l.length * (b + 1) + (b + 1) :=
        Nat.succ_mul ..
      omega

/-- Peel the zero iteration off a range `flatMap`. -/
theorem flatMap_range_split {γ : Type _} (n : ℕ) (G : ℕ → List γ) :
    (List.range (n + 1)).flatMap G
      = G 0 ++ (List.range n).flatMap (fun j => G (1 + j)) := by
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  congr 1
  exact flatMap_congr fun j _ => by
    rw [show Nat.succ j = 1 + j from by omega]

-- ════════════════════════════════════════════════════════════════════════
-- Consequence head positions
-- ════════════════════════════════════════════════════════════════════════

/-- Load `posMove`-of-a-position into the scratch position register: copy,
    then adjust by the (definition-level) move. `none` means the halting
    state's frozen head. -/
def setupPosTM (p : Fin nT) : Option Dir3 → TM nT
  | none => copyIntoTM p auxReg2
  | some .stay => copyIntoTM p auxReg2
  | some .left => seqTM (copyIntoTM p auxReg2) (decRegTM auxReg2)
  | some .right => seqTM (copyIntoTM p auxReg2) (incRegTM auxReg2)

/-- The value `setupPosTM` leaves in `auxReg2`. -/
def posMoveOpt (v : ℕ) : Option Dir3 → ℕ
  | none => v
  | some d => posMove v d

/-- `posMoveOpt` moves a position bounded by `P` to one bounded by `P + 1`. -/
theorem posMoveOpt_le (v P : ℕ) (mv : Option Dir3) (hv : v ≤ P) :
    posMoveOpt v mv ≤ P + 1 := by
  cases mv with
  | none => show v ≤ P + 1; omega
  | some d =>
    cases d with
    | left => show v - 1 ≤ P + 1; omega
    | stay => show v ≤ P + 1; omega
    | right => show v + 1 ≤ P + 1; omega

/-- **`setupPosTM` Hoare specification**: `auxReg2 := posMoveOpt` of the
    position register's value. -/
theorem setupPosTM_hoareTime (p : Fin nT) (hp : p ≠ auxReg2)
    (mv : Option Dir3) (M v a : ℕ)
    (hv : v + 1 ≤ M) (ha : a ≤ M)
    (inp₀ : Tape) (work₀ : Fin nT → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hpv : work₀ p = regTape v) (haux : work₀ auxReg2 = regTape a) :
    (setupPosTM p mv).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀
        (Function.update work₀ auxReg2 (regTape (posMoveOpt v mv))) ys)
      (2 * opBudget M + 1) := by
  have hcopy : (copyIntoTM p auxReg2).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ (Function.update work₀ auxReg2 (regTape v)) ys)
      (opBudget M) :=
    (copyIntoTM_hoareTime p auxReg2 hp v a inp₀ work₀ ys hinp₀
      (fun i _ => hwork₀ i) hpv haux).mono_bound
      (copyIntoTM_le_opBudget (by omega) ha)
  have hmidP : ∀ i, Parked (Function.update work₀ auxReg2 (regTape v) i) :=
    parked_update hwork₀ (parked_regTape _)
  cases mv with
  | none => exact hcopy.mono_bound (by omega)
  | some d =>
    cases d with
    | stay => exact hcopy.mono_bound (by omega)
    | left =>
      have hdec : (decRegTM auxReg2).HoareTime
          (EmitPred inp₀ (Function.update work₀ auxReg2 (regTape v)) ys)
          (EmitPred inp₀
            (Function.update work₀ auxReg2 (regTape (v - 1))) ys)
          (opBudget M) := by
        refine ((decRegTM_hoareTime auxReg2 v inp₀
          (Function.update work₀ auxReg2 (regTape v)) ys hinp₀
          (fun i _ => hmidP i)
          (by rw [Function.update_self])).consequence
          (fun _ _ _ h => h) ?_ (incRegTM_le_opBudget (by omega)))
        rintro inp work out ⟨g1, g2, g3⟩
        exact ⟨g1, by rw [g2, Function.update_idem], g3⟩
      exact (seqTM_hoareTime (copyIntoTM p auxReg2) (decRegTM auxReg2) hcopy
        (emitPred_transition hinp₀ hmidP _) hdec).mono_bound (by omega)
    | right =>
      have hinc : (incRegTM auxReg2).HoareTime
          (EmitPred inp₀ (Function.update work₀ auxReg2 (regTape v)) ys)
          (EmitPred inp₀
            (Function.update work₀ auxReg2 (regTape (v + 1))) ys)
          (opBudget M) := by
        refine ((incRegTM_hoareTime auxReg2 v inp₀
          (Function.update work₀ auxReg2 (regTape v)) ys hinp₀
          (fun i _ => hmidP i)
          (by rw [Function.update_self])).consequence
          (fun _ _ _ h => h) ?_ (incRegTM_le_opBudget (by omega)))
        rintro inp work out ⟨g1, g2, g3⟩
        exact ⟨g1, by rw [g2, Function.update_idem], g3⟩
      exact (seqTM_hoareTime (copyIntoTM p auxReg2) (incRegTM auxReg2) hcopy
        (emitPred_transition hinp₀ hmidP _) hinc).mono_bound (by omega)


-- ════════════════════════════════════════════════════════════════════════
-- The reading condition
-- ════════════════════════════════════════════════════════════════════════

/-- Descriptors of the eight-literal reading condition. -/
noncomputable def activeCondD (N : NTM 1) (q : N.Q) (si sw so : Γ)
    (b : Bool) : List (LitDesc nT) :=
  [⟨false, 0, .inl tReg, .inr (stateIdx N q), .inr 0, .inr 0⟩,
   ⟨false, 3, .inl tReg, .inr 0, .inl pos1Reg, .inr 0⟩,
   ⟨false, 2, .inl tReg, .inr 0, .inl pos1Reg, .inr (symIdx si)⟩,
   ⟨false, 3, .inl tReg, .inr 1, .inl pos2Reg, .inr 0⟩,
   ⟨false, 2, .inl tReg, .inr 1, .inl pos2Reg, .inr (symIdx sw)⟩,
   ⟨false, 3, .inl tReg, .inr 2, .inl pos3Reg, .inr 0⟩,
   ⟨false, 2, .inl tReg, .inr 2, .inl pos3Reg, .inr (symIdx so)⟩,
   ⟨!b, 1, .inl tReg, .inr 0, .inr 0, .inr 0⟩]

section ActiveContext

variable (N : NTM 1)

/-- The standing register facts of the active family's leaves. -/
structure ActiveBase (Qc steps P M t pi pw po : ℕ)
    (base : Fin nT → Tape) : Prop where
  /-- The mixed-radix capacity product is within the modulus bound `M`. -/
  hM : 4 * (steps + 1) * (max Qc 3) * (P + 2) * 4 ≤ M
  /-- The row index is below the row count. -/
  ht : t < steps
  /-- The input-head position is within the position bound. -/
  hpi : pi ≤ P
  /-- The work-head position is within the position bound. -/
  hpw : pw ≤ P
  /-- The output-head position is within the position bound. -/
  hpo : po ≤ P
  /-- Every work tape is parked (head at cell 0). -/
  parked : ∀ l, Parked (base l)
  /-- Radix register A holds the row capacity `steps + 1`. -/
  hrA : base rA = regTape (steps + 1)
  /-- Radix register B holds the state capacity `max Qc 3`. -/
  hrB : base rB = regTape (max Qc 3)
  /-- Radix register C holds the position capacity `P + 2`. -/
  hrC : base rC = regTape (P + 2)
  /-- Radix register D holds the symbol capacity `4`. -/
  hrD : base rD = regTape 4
  /-- The row register holds the current row `t`. -/
  htReg : base tReg = regTape t
  /-- The successor-row register holds `t + 1`. -/
  htPlus : base tPlusReg = regTape (t + 1)
  /-- The first position register holds the input-head position. -/
  hp1 : base pos1Reg = regTape pi
  /-- The second position register holds the work-head position. -/
  hp2 : base pos2Reg = regTape pw
  /-- The third position register holds the output-head position. -/
  hp3 : base pos3Reg = regTape po

/-- The base facts survive scratch-position updates. -/
theorem ActiveBase.update_aux {Qc steps P M t pi pw po : ℕ}
    {base : Fin nT → Tape}
    (hB : ActiveBase Qc steps P M t pi pw po base) (z : ℕ) :
    ActiveBase Qc steps P M t pi pw po
      (Function.update base auxReg2 (regTape z)) :=
  ⟨hB.hM, hB.ht, hB.hpi, hB.hpw, hB.hpo,
   parked_update hB.parked (parked_regTape _),
   by rw [Function.update_of_ne (by decide)]; exact hB.hrA,
   by rw [Function.update_of_ne (by decide)]; exact hB.hrB,
   by rw [Function.update_of_ne (by decide)]; exact hB.hrC,
   by rw [Function.update_of_ne (by decide)]; exact hB.hrD,
   by rw [Function.update_of_ne (by decide)]; exact hB.htReg,
   by rw [Function.update_of_ne (by decide)]; exact hB.htPlus,
   by rw [Function.update_of_ne (by decide)]; exact hB.hp1,
   by rw [Function.update_of_ne (by decide)]; exact hB.hp2,
   by rw [Function.update_of_ne (by decide)]; exact hB.hp3⟩

/-- The reading condition denotes `activeCondF`. -/
theorem activeCondD_spec (q : N.Q) (si sw so : Γ) (b : Bool)
    {Qc steps P M t pi pw po : ℕ} {base : Fin nT → Tape}
    (hQc : Qc = Fintype.card N.Q)
    (hB : ActiveBase Qc steps P M t pi pw po base) :
    List.Forall₂
      (LitDesc.Spec base tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4)
      (activeCondD N q si sw so b)
      (activeCondF N steps P t q pi si pw sw po so b) := by
  subst hQc
  obtain ⟨hM, ht, hpi, hpw, hpo, hparked, hrA', hrB', hrC', hrD', htR,
    htPlus', hp1', hp2', hp3'⟩ := hB
  rw [activeCondD, activeCondF]
  have hcapS : stateIdx N q < max (Fintype.card N.Q) 3 :=
    lt_of_lt_of_le (stateIdx_lt N q) (le_max_left _ 3)
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
    (.cons ?_ (.cons ?_ .nil)))))))
  · obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 0) (by omega)
      (show t < steps + 1 by omega) hcapS
      (show 0 < P + 2 by omega) (show (0:ℕ) < 4 by omega) hM
    exact ⟨t, stateIdx N q, 0, 0, ⟨htR, by decide, by decide⟩, rfl, rfl,
      rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
  · exact headLitD_spec (by omega) hM (by omega) hpi (by decide)
      (by decide) false htR hp1'
  · obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega)
      (show t < steps + 1 by omega) (show 0 < max (Fintype.card N.Q) 3
        by omega)
      (show pi < P + 2 by omega) (symIdx_lt si) hM
    exact ⟨t, 0, pi, symIdx si, ⟨htR, by decide, by decide⟩, rfl,
      ⟨hp1', by decide, by decide⟩, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
  · exact headLitD_spec (by omega) hM (by omega) hpw (by decide)
      (by decide) false htR hp2'
  · obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega)
      (show t < steps + 1 by omega) (show 1 < max (Fintype.card N.Q) 3
        by omega)
      (show pw < P + 2 by omega) (symIdx_lt sw) hM
    exact ⟨t, 1, pw, symIdx sw, ⟨htR, by decide, by decide⟩, rfl,
      ⟨hp2', by decide, by decide⟩, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
  · exact headLitD_spec (by omega) hM (by omega) hpo (by decide)
      (by decide) false htR hp3'
  · obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega)
      (show t < steps + 1 by omega) (show 2 < max (Fintype.card N.Q) 3
        by omega)
      (show po < P + 2 by omega) (symIdx_lt so) hM
    exact ⟨t, 2, po, symIdx so, ⟨htR, by decide, by decide⟩, rfl,
      ⟨hp3', by decide, by decide⟩, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
  · obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 1) (by omega)
      (show t < steps + 1 by omega) (show 0 < max (Fintype.card N.Q) 3
        by omega)
      (show 0 < P + 2 by omega) (show (0:ℕ) < 4 by omega) hM
    exact ⟨t, 0, 0, 0, ⟨htR, by decide, by decide⟩, rfl, rfl, rfl, rfl,
      rfl, k0, k1, k2, k3, k4⟩


-- ════════════════════════════════════════════════════════════════════════
-- The per-tuple leaf: seven implication clauses
-- ════════════════════════════════════════════════════════════════════════

/-- One conseq clause emission: the condition plus one consequence literal. -/
noncomputable def activeClauseTM (N : NTM 1) (q : N.Q) (si sw so : Γ)
    (b : Bool) (d9 : LitDesc nT) : TM nT :=
  emitClauseTM rA rB rC rD tmp tmp2 (activeCondD N q si sw so b ++ [d9])

/-- **The per-tuple leaf**: the seven implication clauses, with the write
    symbols and head moves resolved at definition level. -/
noncomputable def activeLeafTM (N : NTM 1) (q : N.Q) (si sw so : Γ)
    (b : Bool) (wSymVal oSymVal : Γ) (mvI mvW mvO : Option Dir3) : TM nT :=
  seqTM (activeClauseTM N q si sw so b
      ⟨true, 0, .inl tPlusReg,
        .inr (stateIdx N (if q = N.qhalt then q
          else (N.δ b q si (fun _ => sw) so).1)), .inr 0, .inr 0⟩)
    (seqTM (activeClauseTM N q si sw so b
        ⟨true, 2, .inl tPlusReg, .inr 0, .inl pos1Reg, .inr (symIdx si)⟩)
      (seqTM (activeClauseTM N q si sw so b
          ⟨true, 2, .inl tPlusReg, .inr 1, .inl pos2Reg,
            .inr (symIdx wSymVal)⟩)
        (seqTM (activeClauseTM N q si sw so b
            ⟨true, 2, .inl tPlusReg, .inr 2, .inl pos3Reg,
              .inr (symIdx oSymVal)⟩)
          (seqTM (setupPosTM pos1Reg mvI)
            (seqTM (activeClauseTM N q si sw so b
                ⟨true, 3, .inl tPlusReg, .inr 0, .inl auxReg2, .inr 0⟩)
              (seqTM (setupPosTM pos2Reg mvW)
                (seqTM (activeClauseTM N q si sw so b
                    ⟨true, 3, .inl tPlusReg, .inr 1, .inl auxReg2, .inr 0⟩)
                  (seqTM (setupPosTM pos3Reg mvO)
                    (seqTM (activeClauseTM N q si sw so b
                        ⟨true, 3, .inl tPlusReg, .inr 2, .inl auxReg2,
                          .inr 0⟩)
                      (setConstTM auxReg2 0))))))))))

/-- Budget of the leaf. -/
def activeLeafBudget (M : ℕ) : ℕ :=
  7 * clauseBudget 9 M + 7 * opBudget M + 13

/-- One conseq-clause emission from an `ActiveBase` state. -/
theorem activeClauseTM_hoareTime (q : N.Q) (si sw so : Γ) (b : Bool)
    {Qc steps P M t pi pw po : ℕ} {base : Fin nT → Tape}
    (hQc : Qc = Fintype.card N.Q)
    (hB : ActiveBase Qc steps P M t pi pw po base)
    {d9 : LitDesc nT} {ℓ9 : Lit}
    (h9 : LitDesc.Spec base tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4 d9 ℓ9)
    (inp₀ : Tape) (ys : List Bool) (hinp₀ : Parked inp₀) :
    (activeClauseTM N q si sw so b d9).HoareTime
      (EmitPred inp₀ (scratch base tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch base tmp tmp2 0)
        (ys ++ (Clause.encode
          (activeCondF N steps P t q pi si pw sw po so b ++ [ℓ9])
          ++ [true, false])))
      (clauseBudget 9 M) := by
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hB.hM
  have hf : List.Forall₂
      (LitDesc.Spec base tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4)
      (activeCondD N q si sw so b ++ [d9])
      (activeCondF N steps P t q pi si pw sw po so b ++ [ℓ9]) :=
    forall₂_append (activeCondD_spec N q si sw so b hQc hB)
      (.cons h9 .nil)
  exact emitClauseTM_hoareTime rA rB rC rD tmp tmp2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    hAM hBM hCM hDM hf
    (L := 9) (by simp [activeCondD])
    inp₀ ys hinp₀ hB.parked hB.hrA hB.hrB hB.hrC hB.hrD

/-- **`activeLeafTM` Hoare specification**: appends the encoded
    `activeClausesAtF` for the tuple. -/
theorem activeLeafTM_hoareTime (q : N.Q) (si sw so : Γ) (b : Bool)
    (wSymVal oSymVal : Γ) (mvI mvW mvO : Option Dir3)
    {Qc steps P M t pi pw po : ℕ} {base : Fin nT → Tape}
    (hQc : Qc = Fintype.card N.Q)
    (hB : ActiveBase Qc steps P M t pi pw po base)
    (haux2 : base auxReg2 = regTape 0)
    (hwSym : wSymVal = (if q = N.qhalt then sw else if pw = 0 then sw
      else ((N.δ b q si (fun _ => sw) so).2.1 0).toΓ))
    (hoSym : oSymVal = (if q = N.qhalt then so else if po = 0 then so
      else (N.δ b q si (fun _ => sw) so).2.2.1.toΓ))
    (hmvI : posMoveOpt pi mvI = (if q = N.qhalt then pi
      else posMove pi (N.δ b q si (fun _ => sw) so).2.2.2.1))
    (hmvW : posMoveOpt pw mvW = (if q = N.qhalt then pw
      else posMove pw ((N.δ b q si (fun _ => sw) so).2.2.2.2.1 0)))
    (hmvO : posMoveOpt po mvO = (if q = N.qhalt then po
      else posMove po (N.δ b q si (fun _ => sw) so).2.2.2.2.2))
    (inp₀ : Tape) (ys : List Bool) (hinp₀ : Parked inp₀) :
    (activeLeafTM N q si sw so b wSymVal oSymVal mvI mvW mvO).HoareTime
      (EmitPred inp₀ (scratch base tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch base tmp tmp2 0)
        (ys ++ CNF.encode
          (activeClausesAtF N steps P t q pi si pw sw po so b)))
      (activeLeafBudget M) := by
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hB.hM
  have htM : t + 1 < steps + 1 := by
    have := hB.ht
    omega
  -- The seven consequence literals.
  have hlit1 : LitDesc.Spec base tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4
      ⟨true, 0, .inl tPlusReg,
        .inr (stateIdx N (if q = N.qhalt then q
          else (N.δ b q si (fun _ => sw) so).1)), .inr 0, .inr 0⟩
      ⟨true, vStateF Qc steps P (t + 1)
        (stateIdx N (if q = N.qhalt then q
          else (N.δ b q si (fun _ => sw) so).1))⟩ := by
    subst hQc
    obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 0) (by omega) htM
      (lt_of_lt_of_le (stateIdx_lt N _) (le_max_left _ 3))
      (show 0 < P + 2 by omega) (show (0:ℕ) < 4 by omega) hB.hM
    exact ⟨t + 1, stateIdx N _, 0, 0, ⟨hB.htPlus, by decide, by decide⟩,
      rfl, rfl, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
  have hlit2 : LitDesc.Spec base tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4
      ⟨true, 2, .inl tPlusReg, .inr 0, .inl pos1Reg, .inr (symIdx si)⟩
      ⟨true, vCellF Qc steps P (t + 1) 0 pi (symIdx si)⟩ := by
    subst hQc
    obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega) htM
      (show 0 < max (Fintype.card N.Q) 3 by omega)
      (show pi < P + 2 from by have := hB.hpi; omega) (symIdx_lt si) hB.hM
    exact ⟨t + 1, 0, pi, symIdx si, ⟨hB.htPlus, by decide, by decide⟩, rfl,
      ⟨hB.hp1, by decide, by decide⟩, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
  have hlit3 : LitDesc.Spec base tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4
      ⟨true, 2, .inl tPlusReg, .inr 1, .inl pos2Reg, .inr (symIdx wSymVal)⟩
      ⟨true, vCellF Qc steps P (t + 1) 1 pw (symIdx wSymVal)⟩ := by
    subst hQc
    obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega) htM
      (show 1 < max (Fintype.card N.Q) 3 by omega)
      (show pw < P + 2 from by have := hB.hpw; omega) (symIdx_lt wSymVal)
      hB.hM
    exact ⟨t + 1, 1, pw, symIdx wSymVal, ⟨hB.htPlus, by decide, by decide⟩,
      rfl, ⟨hB.hp2, by decide, by decide⟩, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
  have hlit4 : LitDesc.Spec base tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4
      ⟨true, 2, .inl tPlusReg, .inr 2, .inl pos3Reg, .inr (symIdx oSymVal)⟩
      ⟨true, vCellF Qc steps P (t + 1) 2 po (symIdx oSymVal)⟩ := by
    subst hQc
    obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega) htM
      (show 2 < max (Fintype.card N.Q) 3 by omega)
      (show po < P + 2 from by have := hB.hpo; omega) (symIdx_lt oSymVal)
      hB.hM
    exact ⟨t + 1, 2, po, symIdx oSymVal, ⟨hB.htPlus, by decide, by decide⟩,
      rfl, ⟨hB.hp3, by decide, by decide⟩, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
  -- Head consequence literals (at the aux-updated bases).
  have hhead : ∀ (tp z : ℕ), tp < 3 → z ≤ P + 1 →
      LitDesc.Spec (Function.update base auxReg2 (regTape z)) tmp tmp2 M
        (steps + 1) (max Qc 3) (P + 2) 4
        ⟨true, 3, .inl tPlusReg, .inr tp, .inl auxReg2, .inr 0⟩
        ⟨true, vHeadF Qc steps P (t + 1) tp z⟩ := by
    intro tp z htp hz
    subst hQc
    obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 3) (by omega) htM
      (show tp < max (Fintype.card N.Q) 3 by omega)
      (show z < P + 2 by omega) (show (0:ℕ) < 4 by omega) hB.hM
    refine ⟨t + 1, tp, z, 0,
      ⟨by rw [Function.update_of_ne (by decide)]; exact hB.htPlus,
        by decide, by decide⟩,
      rfl, ⟨by rw [Function.update_self], by decide, by decide⟩, rfl, rfl,
      rfl, k0, k1, k2, k3, k4⟩
  subst hwSym hoSym
  -- Abbreviations for the emitted clause words.
  set cond : Clause := activeCondF N steps P t q pi si pw sw po so b
    with hcond
  set iH : ℕ := posMoveOpt pi mvI with hiH
  set wH : ℕ := posMoveOpt pw mvW with hwH
  set oH : ℕ := posMoveOpt po mvO with hoH
  have hiHle : iH ≤ P + 1 := posMoveOpt_le pi P mvI hB.hpi
  have hwHle : wH ≤ P + 1 := posMoveOpt_le pw P mvW hB.hpw
  have hoHle : oH ≤ P + 1 := posMoveOpt_le po P mvO hB.hpo
  have hPM : P + 2 ≤ M := by
    have hA1 : (1:ℕ) ≤ steps + 1 := by omega
    obtain ⟨_, _, hCM, _⟩ := radix_caps hA1 (by omega) (by omega)
      (by omega) hB.hM
    omega
  set base₅ : Fin nT → Tape := Function.update base auxReg2 (regTape iH)
    with hbase₅
  set base₇ : Fin nT → Tape := Function.update base auxReg2 (regTape wH)
    with hbase₇
  set base₉ : Fin nT → Tape := Function.update base auxReg2 (regTape oH)
    with hbase₉
  -- The emitted words.
  set w1 : List Bool := Clause.encode (cond ++
    [⟨true, vStateF Qc steps P (t + 1) (stateIdx N (if q = N.qhalt then q
      else (N.δ b q si (fun _ => sw) so).1))⟩]) ++ [true, false] with hw1
  set w2 : List Bool := Clause.encode (cond ++
    [⟨true, vCellF Qc steps P (t + 1) 0 pi (symIdx si)⟩]) ++ [true, false]
    with hw2
  set w3 : List Bool := Clause.encode (cond ++
    [⟨true, vCellF Qc steps P (t + 1) 1 pw
      (symIdx (if q = N.qhalt then sw else if pw = 0 then sw
        else ((N.δ b q si (fun _ => sw) so).2.1 0).toΓ))⟩]) ++ [true, false]
    with hw3
  set w4 : List Bool := Clause.encode (cond ++
    [⟨true, vCellF Qc steps P (t + 1) 2 po
      (symIdx (if q = N.qhalt then so else if po = 0 then so
        else (N.δ b q si (fun _ => sw) so).2.2.1.toΓ))⟩]) ++ [true, false]
    with hw4
  set w5 : List Bool := Clause.encode (cond ++
    [⟨true, vHeadF Qc steps P (t + 1) 0 iH⟩]) ++ [true, false] with hw5
  set w6 : List Bool := Clause.encode (cond ++
    [⟨true, vHeadF Qc steps P (t + 1) 1 wH⟩]) ++ [true, false] with hw6
  set w7 : List Bool := Clause.encode (cond ++
    [⟨true, vHeadF Qc steps P (t + 1) 2 oH⟩]) ++ [true, false] with hw7
  -- The four leading clauses.
  have h₁ := activeClauseTM_hoareTime N q si sw so b hQc hB hlit1 inp₀ ys
    hinp₀
  have h₂ := activeClauseTM_hoareTime N q si sw so b hQc hB hlit2 inp₀
    (ys ++ w1) hinp₀
  have h₃ := activeClauseTM_hoareTime N q si sw so b hQc hB hlit3 inp₀
    (ys ++ w1 ++ w2) hinp₀
  have h₄ := activeClauseTM_hoareTime N q si sw so b hQc hB hlit4 inp₀
    (ys ++ w1 ++ w2 ++ w3) hinp₀
  -- Stage 5: aux := iH.
  have h₅ : (setupPosTM pos1Reg mvI).HoareTime
      (EmitPred inp₀ (scratch base tmp tmp2 0) (ys ++ w1 ++ w2 ++ w3 ++ w4))
      (EmitPred inp₀ (scratch base₅ tmp tmp2 0) (ys ++ w1 ++ w2 ++ w3 ++ w4))
      (2 * opBudget M + 1) := by
    refine ((setupPosTM_hoareTime pos1Reg (by decide) mvI M pi 0
      (by have := hB.hpi; omega) (by omega) inp₀ (scratch base tmp tmp2 0) _
      hinp₀ (scratch_parked 0 hB.parked)
      (by rw [scratch_apply_ne (by decide) (by decide)]; exact hB.hp1)
      (by rw [scratch_apply_ne (by decide) (by decide)]; exact haux2)
      ).strengthen_post ?_)
    rintro inp work out ⟨g1, g2, g3⟩
    exact ⟨g1, by rw [g2, scratch_update_comm (by decide) (by decide)], g3⟩
  -- Stage 6: the input-head clause.
  have h₆ := activeClauseTM_hoareTime N q si sw so b hQc (hB.update_aux iH)
    (hhead 0 iH (by omega) hiHle) inp₀ (ys ++ w1 ++ w2 ++ w3 ++ w4) hinp₀
  -- Stage 7: aux := wH.
  have h₇ : (setupPosTM pos2Reg mvW).HoareTime
      (EmitPred inp₀ (scratch base₅ tmp tmp2 0)
        (ys ++ w1 ++ w2 ++ w3 ++ w4 ++ w5))
      (EmitPred inp₀ (scratch base₇ tmp tmp2 0)
        (ys ++ w1 ++ w2 ++ w3 ++ w4 ++ w5))
      (2 * opBudget M + 1) := by
    refine ((setupPosTM_hoareTime pos2Reg (by decide) mvW M pw iH
      (by have := hB.hpw; omega) (by omega) inp₀ (scratch base₅ tmp tmp2 0) _
      hinp₀ (scratch_parked 0 (hB.update_aux iH).parked)
      (by rw [scratch_apply_ne (by decide) (by decide), hbase₅,
        Function.update_of_ne (by decide)]; exact hB.hp2)
      (by rw [scratch_apply_ne (by decide) (by decide), hbase₅,
        Function.update_self])).strengthen_post ?_)
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, scratch_update_comm (by decide) (by decide), hbase₅,
      Function.update_idem]
  -- Stage 8: the work-head clause.
  have h₈ := activeClauseTM_hoareTime N q si sw so b hQc (hB.update_aux wH)
    (hhead 1 wH (by omega) hwHle) inp₀ (ys ++ w1 ++ w2 ++ w3 ++ w4 ++ w5)
    hinp₀
  -- Stage 9: aux := oH.
  have h₉ : (setupPosTM pos3Reg mvO).HoareTime
      (EmitPred inp₀ (scratch base₇ tmp tmp2 0)
        (ys ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6))
      (EmitPred inp₀ (scratch base₉ tmp tmp2 0)
        (ys ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6))
      (2 * opBudget M + 1) := by
    refine ((setupPosTM_hoareTime pos3Reg (by decide) mvO M po wH
      (by have := hB.hpo; omega) (by omega) inp₀ (scratch base₇ tmp tmp2 0) _
      hinp₀ (scratch_parked 0 (hB.update_aux wH).parked)
      (by rw [scratch_apply_ne (by decide) (by decide), hbase₇,
        Function.update_of_ne (by decide)]; exact hB.hp3)
      (by rw [scratch_apply_ne (by decide) (by decide), hbase₇,
        Function.update_self])).strengthen_post ?_)
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, scratch_update_comm (by decide) (by decide), hbase₇,
      Function.update_idem]
  -- Stage 10: the output-head clause.
  have h₁₀ := activeClauseTM_hoareTime N q si sw so b hQc (hB.update_aux oH)
    (hhead 2 oH (by omega) hoHle) inp₀
    (ys ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6) hinp₀
  -- Stage 11: aux := 0.
  have h₁₁ : (setConstTM auxReg2 0).HoareTime
      (EmitPred inp₀ (scratch base₉ tmp tmp2 0)
        (ys ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6 ++ w7))
      (EmitPred inp₀ (scratch base tmp tmp2 0)
        (ys ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6 ++ w7))
      (opBudget M) := by
    refine ((setConstTM_hoareTime auxReg2 0 oH inp₀
      (scratch base₉ tmp tmp2 0) _ hinp₀
      (scratch_parked 0 (hB.update_aux oH).parked)
      (by rw [scratch_apply_ne (by decide) (by decide), hbase₉,
        Function.update_self])).consequence (fun _ _ _ h => h) ?_
      (setConstTM_le_opBudget (show (0:ℕ) ≤ M by omega) (by omega)))
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, scratch_update_comm (by decide) (by decide), hbase₉,
      Function.update_idem,
      show regTape 0 = base auxReg2 from haux2.symm, Function.update_eq_self]
  -- Glue the eleven stages.
  have c₁₀₁₁ := seqTM_hoareTime _ _ h₁₀
    (emitPred_transition hinp₀ (scratch_parked 0 (hB.update_aux oH).parked) _)
    h₁₁
  have c₉ := seqTM_hoareTime _ _ h₉
    (emitPred_transition hinp₀ (scratch_parked 0 (hB.update_aux oH).parked) _)
    c₁₀₁₁
  have c₈ := seqTM_hoareTime _ _ h₈
    (emitPred_transition hinp₀ (scratch_parked 0 (hB.update_aux wH).parked) _)
    c₉
  have c₇ := seqTM_hoareTime _ _ h₇
    (emitPred_transition hinp₀ (scratch_parked 0 (hB.update_aux wH).parked) _)
    c₈
  have c₆ := seqTM_hoareTime _ _ h₆
    (emitPred_transition hinp₀ (scratch_parked 0 (hB.update_aux iH).parked) _)
    c₇
  have c₅ := seqTM_hoareTime _ _ h₅
    (emitPred_transition hinp₀ (scratch_parked 0 (hB.update_aux iH).parked) _)
    c₆
  have c₄ := seqTM_hoareTime _ _ h₄
    (emitPred_transition hinp₀ (scratch_parked 0 hB.parked) _) c₅
  have c₃ := seqTM_hoareTime _ _ h₃
    (emitPred_transition hinp₀ (scratch_parked 0 hB.parked) _) c₄
  have c₂ := seqTM_hoareTime _ _ h₂
    (emitPred_transition hinp₀ (scratch_parked 0 hB.parked) _) c₃
  have call := seqTM_hoareTime _ _ h₁
    (emitPred_transition hinp₀ (scratch_parked 0 hB.parked) _) c₂
  refine call.consequence (fun _ _ _ h => h) ?_ ?_
  · rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, g2, ?_⟩
    rw [show activeClausesAtF N steps P t q pi si pw sw po so b
        = [cond ++ [⟨true, vStateF Qc steps P (t + 1)
            (stateIdx N (if q = N.qhalt then q
              else (N.δ b q si (fun _ => sw) so).1))⟩],
           cond ++ [⟨true, vCellF Qc steps P (t + 1) 0 pi (symIdx si)⟩],
           cond ++ [⟨true, vCellF Qc steps P (t + 1) 1 pw
            (symIdx (if q = N.qhalt then sw else if pw = 0 then sw
              else ((N.δ b q si (fun _ => sw) so).2.1 0).toΓ))⟩],
           cond ++ [⟨true, vCellF Qc steps P (t + 1) 2 po
            (symIdx (if q = N.qhalt then so else if po = 0 then so
              else (N.δ b q si (fun _ => sw) so).2.2.1.toΓ))⟩],
           cond ++ [⟨true, vHeadF Qc steps P (t + 1) 0
            (if q = N.qhalt then pi
              else posMove pi (N.δ b q si (fun _ => sw) so).2.2.2.1)⟩],
           cond ++ [⟨true, vHeadF Qc steps P (t + 1) 1
            (if q = N.qhalt then pw
              else posMove pw ((N.δ b q si (fun _ => sw) so).2.2.2.2.1 0))⟩],
           cond ++ [⟨true, vHeadF Qc steps P (t + 1) 2
            (if q = N.qhalt then po
              else posMove po (N.δ b q si (fun _ => sw) so).2.2.2.2.2)⟩]]
      from by
        subst hQc
        rw [hcond]
        rfl]
    rw [← hmvI, ← hmvW, ← hmvO]
    rw [hw1, hw2, hw3, hw4, hw5, hw6, hw7] at g3
    simp only [CNF.encode_cons, CNF.encode_nil, List.append_nil,
      List.append_assoc] at g3 ⊢
    exact g3
  · rw [activeLeafBudget]
    omega


-- ════════════════════════════════════════════════════════════════════════
-- The finite unrolls: choice bit, output symbol
-- ════════════════════════════════════════════════════════════════════════

/-- The choice-bit unroll, with the position-zero flags static. -/
noncomputable def activeBLevelTM (q : N.Q) (si sw so : Γ)
    (pwZero poZero : Bool) : TM nT :=
  bigSeqTM ([true, false].map (fun b =>
    activeLeafTM N q si sw so b
      (if q = N.qhalt then sw else if pwZero then sw
        else ((N.δ b q si (fun _ => sw) so).2.1 0).toΓ)
      (if q = N.qhalt then so else if poZero then so
        else (N.δ b q si (fun _ => sw) so).2.2.1.toΓ)
      (if q = N.qhalt then none
        else some (N.δ b q si (fun _ => sw) so).2.2.2.1)
      (if q = N.qhalt then none
        else some ((N.δ b q si (fun _ => sw) so).2.2.2.2.1 0))
      (if q = N.qhalt then none
        else some (N.δ b q si (fun _ => sw) so).2.2.2.2.2)))

/-- Budget of the choice-bit unroll: two leaves. -/
def activeBLevelBudget (M : ℕ) : ℕ := 2 * (activeLeafBudget M + 1) + 1

/-- **`activeBLevelTM` Hoare specification.** -/
theorem activeBLevelTM_hoareTime (q : N.Q) (si sw so : Γ)
    (pwZero poZero : Bool)
    {Qc steps P M t pi pw po : ℕ} {base : Fin nT → Tape}
    (hQc : Qc = Fintype.card N.Q)
    (hB : ActiveBase Qc steps P M t pi pw po base)
    (haux2 : base auxReg2 = regTape 0)
    (hpwZ : pwZero = true → pw = 0) (hpwZ' : pwZero = false → pw ≠ 0)
    (hpoZ : poZero = true → po = 0) (hpoZ' : poZero = false → po ≠ 0)
    (inp₀ : Tape) (ys : List Bool) (hinp₀ : Parked inp₀) :
    (activeBLevelTM N q si sw so pwZero poZero).HoareTime
      (EmitPred inp₀ (scratch base tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch base tmp tmp2 0)
        (ys ++ [true, false].flatMap (fun b =>
          CNF.encode (activeClausesAtF N steps P t q pi si pw sw po so b))))
      (activeBLevelBudget M) := by
  have hleaf : ∀ b ∈ [true, false], ∀ ys',
      (activeLeafTM N q si sw so b
        (if q = N.qhalt then sw else if pwZero then sw
          else ((N.δ b q si (fun _ => sw) so).2.1 0).toΓ)
        (if q = N.qhalt then so else if poZero then so
          else (N.δ b q si (fun _ => sw) so).2.2.1.toΓ)
        (if q = N.qhalt then none
          else some (N.δ b q si (fun _ => sw) so).2.2.2.1)
        (if q = N.qhalt then none
          else some ((N.δ b q si (fun _ => sw) so).2.2.2.2.1 0))
        (if q = N.qhalt then none
          else some (N.δ b q si (fun _ => sw) so).2.2.2.2.2)).HoareTime
        (EmitPred inp₀ (scratch base tmp tmp2 0) ys')
        (EmitPred inp₀ (scratch base tmp tmp2 0)
          (ys' ++ CNF.encode
            (activeClausesAtF N steps P t q pi si pw sw po so b)))
        (activeLeafBudget M) := by
    intro b _ ys'
    refine activeLeafTM_hoareTime N q si sw so b _ _ _ _ _ hQc hB haux2
      ?_ ?_ ?_ ?_ ?_ inp₀ ys' hinp₀
    · by_cases hq : q = N.qhalt
      · rw [ite_eq_left hq, ite_eq_left hq]
      · rw [ite_eq_right hq, ite_eq_right hq]
        cases hz : pwZero with
        | true => rw [ite_eq_left rfl, ite_eq_left (hpwZ hz)]
        | false => rw [ite_eq_right (by simp), ite_eq_right (hpwZ' hz)]
    · by_cases hq : q = N.qhalt
      · rw [ite_eq_left hq, ite_eq_left hq]
      · rw [ite_eq_right hq, ite_eq_right hq]
        cases hz : poZero with
        | true => rw [ite_eq_left rfl, ite_eq_left (hpoZ hz)]
        | false => rw [ite_eq_right (by simp), ite_eq_right (hpoZ' hz)]
    · by_cases hq : q = N.qhalt
      · rw [ite_eq_left hq, ite_eq_left hq]; rfl
      · rw [ite_eq_right hq, ite_eq_right hq]; rfl
    · by_cases hq : q = N.qhalt
      · rw [ite_eq_left hq, ite_eq_left hq]; rfl
      · rw [ite_eq_right hq, ite_eq_right hq]; rfl
    · by_cases hq : q = N.qhalt
      · rw [ite_eq_left hq, ite_eq_left hq]; rfl
      · rw [ite_eq_right hq, ite_eq_right hq]; rfl
  have h := bigSeq_emit_hoareTime
    (fun b => activeLeafTM N q si sw so b
      (if q = N.qhalt then sw else if pwZero then sw
        else ((N.δ b q si (fun _ => sw) so).2.1 0).toΓ)
      (if q = N.qhalt then so else if poZero then so
        else (N.δ b q si (fun _ => sw) so).2.2.1.toΓ)
      (if q = N.qhalt then none
        else some (N.δ b q si (fun _ => sw) so).2.2.2.1)
      (if q = N.qhalt then none
        else some ((N.δ b q si (fun _ => sw) so).2.2.2.2.1 0))
      (if q = N.qhalt then none
        else some (N.δ b q si (fun _ => sw) so).2.2.2.2.2))
    (fun b => CNF.encode (activeClausesAtF N steps P t q pi si pw sw po so b))
    (activeLeafBudget M) inp₀ (scratch base tmp tmp2 0) hinp₀
    (scratch_parked 0 hB.parked) [true, false] hleaf ys
  exact h.mono_bound (by rw [activeBLevelBudget]; simp)

/-- The output-symbol unroll. -/
noncomputable def activeSoLevelTM (q : N.Q) (si sw : Γ)
    (pwZero poZero : Bool) : TM nT :=
  bigSeqTM (allSyms.map (fun so => activeBLevelTM N q si sw so pwZero poZero))

/-- Budget of the output-symbol unroll: four choice-bit levels. -/
def activeSoLevelBudget (M : ℕ) : ℕ := 4 * (activeBLevelBudget M + 1) + 1

/-- **`activeSoLevelTM` Hoare specification.** -/
theorem activeSoLevelTM_hoareTime (q : N.Q) (si sw : Γ)
    (pwZero poZero : Bool)
    {Qc steps P M t pi pw po : ℕ} {base : Fin nT → Tape}
    (hQc : Qc = Fintype.card N.Q)
    (hB : ActiveBase Qc steps P M t pi pw po base)
    (haux2 : base auxReg2 = regTape 0)
    (hpwZ : pwZero = true → pw = 0) (hpwZ' : pwZero = false → pw ≠ 0)
    (hpoZ : poZero = true → po = 0) (hpoZ' : poZero = false → po ≠ 0)
    (inp₀ : Tape) (ys : List Bool) (hinp₀ : Parked inp₀) :
    (activeSoLevelTM N q si sw pwZero poZero).HoareTime
      (EmitPred inp₀ (scratch base tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch base tmp tmp2 0)
        (ys ++ allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
          CNF.encode (activeClausesAtF N steps P t q pi si pw sw po so b)))))
      (activeSoLevelBudget M) := by
  have h := bigSeq_emit_hoareTime
    (fun so => activeBLevelTM N q si sw so pwZero poZero)
    (fun so => [true, false].flatMap (fun b =>
      CNF.encode (activeClausesAtF N steps P t q pi si pw sw po so b)))
    (activeBLevelBudget M) inp₀ (scratch base tmp tmp2 0) hinp₀
    (scratch_parked 0 hB.parked) allSyms
    (fun so _ ys' => activeBLevelTM_hoareTime N q si sw so pwZero poZero hQc
      hB haux2 hpwZ hpwZ' hpoZ hpoZ' inp₀ ys' hinp₀)
    ys
  exact h.mono_bound (by rw [activeSoLevelBudget]; simp [allSyms])


-- ════════════════════════════════════════════════════════════════════════
-- The output-position split and sweep
-- ════════════════════════════════════════════════════════════════════════

/-- The output-position block: the `po = 0` instance, then the sweep over
    `po = 1..P`. -/
noncomputable def activePoSplitTM (q : N.Q) (si sw : Γ) (pwZero : Bool) :
    TM nT :=
  seqTM (activeSoLevelTM N q si sw pwZero true)
    (seqTM (setConstTM pos3Reg 1)
      (seqTM (emitLoopTM (activeSoLevelTM N q si sw pwZero false)
          pos3Reg pos3Fuel)
        (setConstTM pos3Reg 0)))

/-- Budget of the output-position block: the `po = 0` instance plus the
    counter setup, the sweep loop, and the counter reset. -/
def activePoSplitBudget (M : ℕ) : ℕ :=
  activeSoLevelBudget M + 1
    + (opBudget M + 1
      + (loopBudget M (activeSoLevelBudget M) + 1 + opBudget M))

/-- **`activePoSplitTM` Hoare specification** (at `po = 0` boundary
    state). -/
theorem activePoSplitTM_hoareTime (q : N.Q) (si sw : Γ) (pwZero : Bool)
    {Qc steps P M t pi pw : ℕ} {base : Fin nT → Tape}
    (hQc : Qc = Fintype.card N.Q)
    (hB : ActiveBase Qc steps P M t pi pw 0 base)
    (haux2 : base auxReg2 = regTape 0)
    (hf3 : base pos3Fuel = regTape P)
    (hpwZ : pwZero = true → pw = 0) (hpwZ' : pwZero = false → pw ≠ 0)
    (inp₀ : Tape) (ys : List Bool) (hinp₀ : Parked inp₀) :
    (activePoSplitTM N q si sw pwZero).HoareTime
      (EmitPred inp₀ (scratch base tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch base tmp tmp2 0)
        (ys ++ (List.range (P + 1)).flatMap (fun po =>
          allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
            CNF.encode
              (activeClausesAtF N steps P t q pi si pw sw po so b))))))
      (activePoSplitBudget M) := by
  have hPM : P + 2 ≤ M := by
    have hA1 : (1:ℕ) ≤ steps + 1 := by omega
    obtain ⟨_, _, hCM, _⟩ := radix_caps hA1 (by omega) (by omega)
      (by omega) hB.hM
    omega
  -- Part 1: po = 0.
  have h₀ := activeSoLevelTM_hoareTime N q si sw pwZero true hQc hB haux2
    hpwZ hpwZ' (fun _ => rfl) (fun h => absurd h (by simp)) inp₀ ys hinp₀
  set ys₁ : List Bool := ys ++ allSyms.flatMap (fun so =>
    [true, false].flatMap (fun b =>
      CNF.encode (activeClausesAtF N steps P t q pi si pw sw 0 so b)))
    with hys₁
  -- Part 2: counter to 1.
  have h₁ : (setConstTM pos3Reg 1).HoareTime
      (EmitPred inp₀ (scratch base tmp tmp2 0) ys₁)
      (EmitPred inp₀
        (Function.update (scratch base tmp tmp2 0) pos3Reg (regTape 1)) ys₁)
      (opBudget M) :=
    ((setConstTM_hoareTime pos3Reg 1 0 inp₀ (scratch base tmp tmp2 0) ys₁
      hinp₀ (scratch_parked 0 hB.parked)
      (by rw [scratch_apply_ne (by decide) (by decide)]; exact hB.hp3)
      ).consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
      (setConstTM_le_opBudget (show (1:ℕ) ≤ M by omega) (show (0:ℕ) ≤ M by omega)))
  -- Part 3: the sweep over po = 1..P.
  have hbody : ∀ j, j < P →
      (activeSoLevelTM N q si sw pwZero false).HoareTime
        (EmitPred inp₀
          (Function.update
            (Function.update
              (Function.update (scratch base tmp tmp2 0) pos3Reg (regTape 1))
              pos3Reg (regTape (1 + j))) pos3Fuel ⟨j + 2, regCells P⟩)
          (ys₁ ++ (List.range j).flatMap (fun j' =>
            allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
              CNF.encode (activeClausesAtF N steps P t q pi si pw sw (1 + j')
                so b))))))
        (EmitPred inp₀
          (Function.update
            (Function.update
              (Function.update (scratch base tmp tmp2 0) pos3Reg (regTape 1))
              pos3Reg (regTape (1 + j))) pos3Fuel ⟨j + 2, regCells P⟩)
          (ys₁ ++ (List.range (j + 1)).flatMap (fun j' =>
            allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
              CNF.encode (activeClausesAtF N steps P t q pi si pw sw (1 + j')
                so b))))))
        (activeSoLevelBudget M) := by
    intro j hj
    set base' : Fin nT → Tape :=
      Function.update (Function.update base pos3Reg (regTape (1 + j))) pos3Fuel
        ⟨j + 2, regCells P⟩ with hbase'
    have hstate : Function.update
        (Function.update
          (Function.update (scratch base tmp tmp2 0) pos3Reg (regTape 1))
          pos3Reg (regTape (1 + j))) pos3Fuel ⟨j + 2, regCells P⟩
        = scratch base' tmp tmp2 0 := by
      rw [Function.update_idem, scratch_update_comm (by decide) (by decide),
        scratch_update_comm (by decide) (by decide)]
    have hB' : ActiveBase Qc steps P M t pi pw (1 + j) base' :=
      ⟨hB.hM, hB.ht, hB.hpi, hB.hpw, by omega,
       parked_update (parked_update hB.parked (parked_regTape _))
         (parked_regCells (by omega)),
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hrA,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hrB,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hrC,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hrD,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.htReg,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.htPlus,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hp1,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hp2,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_self]⟩
    have hso := activeSoLevelTM_hoareTime N q si sw pwZero false hQc hB'
      (by rw [hbase', Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact haux2)
      hpwZ hpwZ' (fun h => absurd h (by simp)) (fun _ => by omega)
      inp₀
      (ys₁ ++ (List.range j).flatMap (fun j' =>
        allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
          CNF.encode (activeClausesAtF N steps P t q pi si pw sw (1 + j')
            so b)))))
      hinp₀
    rw [hstate]
    refine hso.strengthen_post ?_
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, g2, ?_⟩
    rw [flatMap_range_succ, ← List.append_assoc]
    exact g3
  have hloop := emitLoopFrom_hoareTime
    (activeSoLevelTM N q si sw pwZero false) pos3Reg pos3Fuel
    (by decide) 1 P M (activeSoLevelBudget M) (by omega)
    (fun j' => allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
      CNF.encode (activeClausesAtF N steps P t q pi si pw sw (1 + j') so b))))
    inp₀ (Function.update (scratch base tmp tmp2 0) pos3Reg (regTape 1)) ys₁
    hinp₀ (parked_update (scratch_parked 0 hB.parked) (parked_regTape _))
    (by rw [Function.update_of_ne (by decide),
      scratch_apply_ne (by decide) (by decide)]; exact hf3)
    (by rw [Function.update_self])
    hbody
  -- Part 4: counter back to 0.
  have h₃ : (setConstTM pos3Reg 0).HoareTime
      (EmitPred inp₀
        (Function.update
          (Function.update (scratch base tmp tmp2 0) pos3Reg (regTape 1))
          pos3Reg (regTape (1 + P)))
        (ys₁ ++ (List.range P).flatMap (fun j' =>
          allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
            CNF.encode (activeClausesAtF N steps P t q pi si pw sw (1 + j')
              so b))))))
      (EmitPred inp₀ (scratch base tmp tmp2 0)
        (ys₁ ++ (List.range P).flatMap (fun j' =>
          allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
            CNF.encode (activeClausesAtF N steps P t q pi si pw sw (1 + j')
              so b))))))
      (opBudget M) := by
    refine ((setConstTM_hoareTime pos3Reg 0 (1 + P) inp₀
      (Function.update
        (Function.update (scratch base tmp tmp2 0) pos3Reg (regTape 1)) pos3Reg
        (regTape (1 + P))) _ hinp₀
      (parked_update (parked_update (scratch_parked 0 hB.parked)
        (parked_regTape _)) (parked_regTape _))
      (by rw [Function.update_self])).consequence
      (fun _ _ _ h => h) ?_
      (setConstTM_le_opBudget (show (0:ℕ) ≤ M by omega) (show 1 + P ≤ M by omega)))
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, Function.update_idem, Function.update_idem,
      show regTape 0 = scratch base tmp tmp2 0 pos3Reg from by
        rw [scratch_apply_ne (by decide) (by decide)]; exact hB.hp3.symm,
      Function.update_eq_self]
  -- Glue.
  have h₂₃ := seqTM_hoareTime _ (setConstTM pos3Reg 0)
    (hloop.mono_bound (loop_le_loopBudget (show P ≤ M by omega)))
    (emitPred_transition hinp₀
      (parked_update (parked_update (scratch_parked 0 hB.parked)
        (parked_regTape _)) (parked_regTape _)) _) h₃
  have h₁₂₃ := seqTM_hoareTime (setConstTM pos3Reg 1) _ h₁
    (emitPred_transition hinp₀
      (parked_update (scratch_parked 0 hB.parked) (parked_regTape _)) _) h₂₃
  have hall := seqTM_hoareTime (activeSoLevelTM N q si sw pwZero true) _ h₀
    (emitPred_transition hinp₀ (scratch_parked 0 hB.parked) _) h₁₂₃
  refine hall.consequence (fun _ _ _ h => h) ?_
    (by rw [activePoSplitBudget])
  rintro inp work out ⟨g1, g2, g3⟩
  refine ⟨g1, g2, ?_⟩
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  rw [show (List.range P).flatMap (fun a => allSyms.flatMap (fun so =>
      [true, false].flatMap (fun b =>
        CNF.encode (activeClausesAtF N steps P t q pi si pw sw a.succ so b))))
    = (List.range P).flatMap (fun j' => allSyms.flatMap (fun so =>
      [true, false].flatMap (fun b =>
        CNF.encode (activeClausesAtF N steps P t q pi si pw sw (1 + j')
          so b)))) from
    flatMap_congr fun j _ => by
      rw [show Nat.succ j = 1 + j from by omega]]
  rw [hys₁] at g3
  rw [← List.append_assoc]
  exact g3


-- ════════════════════════════════════════════════════════════════════════
-- The work-symbol unroll, work-position split, input-symbol unroll
-- ════════════════════════════════════════════════════════════════════════

/-- The work-symbol unroll. -/
noncomputable def activeSwLevelTM (q : N.Q) (si : Γ) (pwZero : Bool) :
    TM nT :=
  bigSeqTM (allSyms.map (fun sw => activePoSplitTM N q si sw pwZero))

/-- Budget of the work-symbol unroll: four output-position blocks. -/
def activeSwLevelBudget (M : ℕ) : ℕ := 4 * (activePoSplitBudget M + 1) + 1

/-- **`activeSwLevelTM` Hoare specification.** -/
theorem activeSwLevelTM_hoareTime (q : N.Q) (si : Γ) (pwZero : Bool)
    {Qc steps P M t pi pw : ℕ} {base : Fin nT → Tape}
    (hQc : Qc = Fintype.card N.Q)
    (hB : ActiveBase Qc steps P M t pi pw 0 base)
    (haux2 : base auxReg2 = regTape 0)
    (hf3 : base pos3Fuel = regTape P)
    (hpwZ : pwZero = true → pw = 0) (hpwZ' : pwZero = false → pw ≠ 0)
    (inp₀ : Tape) (ys : List Bool) (hinp₀ : Parked inp₀) :
    (activeSwLevelTM N q si pwZero).HoareTime
      (EmitPred inp₀ (scratch base tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch base tmp tmp2 0)
        (ys ++ allSyms.flatMap (fun sw =>
          (List.range (P + 1)).flatMap (fun po =>
            allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
              CNF.encode
                (activeClausesAtF N steps P t q pi si pw sw po so b)))))))
      (activeSwLevelBudget M) := by
  have h := bigSeq_emit_hoareTime
    (fun sw => activePoSplitTM N q si sw pwZero)
    (fun sw => (List.range (P + 1)).flatMap (fun po =>
      allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
        CNF.encode (activeClausesAtF N steps P t q pi si pw sw po so b)))))
    (activePoSplitBudget M) inp₀ (scratch base tmp tmp2 0) hinp₀
    (scratch_parked 0 hB.parked) allSyms
    (fun sw _ ys' => activePoSplitTM_hoareTime N q si sw pwZero hQc hB haux2
      hf3 hpwZ hpwZ' inp₀ ys' hinp₀)
    ys
  exact h.mono_bound (by rw [activeSwLevelBudget]; simp [allSyms])

/-- The work-position block: the `pw = 0` instance, then the sweep over
    `pw = 1..P`. -/
noncomputable def activePwSplitTM (q : N.Q) (si : Γ) : TM nT :=
  seqTM (activeSwLevelTM N q si true)
    (seqTM (setConstTM pos2Reg 1)
      (seqTM (emitLoopTM (activeSwLevelTM N q si false) pos2Reg pos2Fuel)
        (setConstTM pos2Reg 0)))

/-- Budget of the work-position block: the `pw = 0` instance plus the
    counter setup, the sweep loop, and the counter reset. -/
def activePwSplitBudget (M : ℕ) : ℕ :=
  activeSwLevelBudget M + 1
    + (opBudget M + 1
      + (loopBudget M (activeSwLevelBudget M) + 1 + opBudget M))

/-- **`activePwSplitTM` Hoare specification** (at `pw = po = 0` boundary
    state). -/
theorem activePwSplitTM_hoareTime (q : N.Q) (si : Γ)
    {Qc steps P M t pi : ℕ} {base : Fin nT → Tape}
    (hQc : Qc = Fintype.card N.Q)
    (hB : ActiveBase Qc steps P M t pi 0 0 base)
    (haux2 : base auxReg2 = regTape 0)
    (hf2 : base pos2Fuel = regTape P) (hf3 : base pos3Fuel = regTape P)
    (inp₀ : Tape) (ys : List Bool) (hinp₀ : Parked inp₀) :
    (activePwSplitTM N q si).HoareTime
      (EmitPred inp₀ (scratch base tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch base tmp tmp2 0)
        (ys ++ (List.range (P + 1)).flatMap (fun pw =>
          allSyms.flatMap (fun sw =>
            (List.range (P + 1)).flatMap (fun po =>
              allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
                CNF.encode
                  (activeClausesAtF N steps P t q pi si pw sw po so b))))))))
      (activePwSplitBudget M) := by
  have hPM : P + 2 ≤ M := by
    have hA1 : (1:ℕ) ≤ steps + 1 := by omega
    obtain ⟨_, _, hCM, _⟩ := radix_caps hA1 (by omega) (by omega)
      (by omega) hB.hM
    omega
  -- Part 1: pw = 0.
  have h₀ := activeSwLevelTM_hoareTime N q si true hQc hB haux2 hf3
    (fun _ => rfl) (fun h => absurd h (by simp)) inp₀ ys hinp₀
  set ys₁ : List Bool := ys ++ allSyms.flatMap (fun sw =>
    (List.range (P + 1)).flatMap (fun po =>
      allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
        CNF.encode (activeClausesAtF N steps P t q pi si 0 sw po so b)))))
    with hys₁
  -- Part 2: counter to 1.
  have h₁ : (setConstTM pos2Reg 1).HoareTime
      (EmitPred inp₀ (scratch base tmp tmp2 0) ys₁)
      (EmitPred inp₀
        (Function.update (scratch base tmp tmp2 0) pos2Reg (regTape 1)) ys₁)
      (opBudget M) :=
    ((setConstTM_hoareTime pos2Reg 1 0 inp₀ (scratch base tmp tmp2 0) ys₁
      hinp₀ (scratch_parked 0 hB.parked)
      (by rw [scratch_apply_ne (by decide) (by decide)]; exact hB.hp2)
      ).consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
      (setConstTM_le_opBudget (show (1:ℕ) ≤ M by omega) (show (0:ℕ) ≤ M by omega)))
  -- Part 3: the sweep over pw = 1..P.
  have hbody : ∀ j, j < P →
      (activeSwLevelTM N q si false).HoareTime
        (EmitPred inp₀
          (Function.update
            (Function.update
              (Function.update (scratch base tmp tmp2 0) pos2Reg (regTape 1))
              pos2Reg (regTape (1 + j))) pos2Fuel ⟨j + 2, regCells P⟩)
          (ys₁ ++ (List.range j).flatMap (fun j' =>
            allSyms.flatMap (fun sw =>
              (List.range (P + 1)).flatMap (fun po =>
                allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
                  CNF.encode (activeClausesAtF N steps P t q pi si (1 + j')
                    sw po so b))))))))
        (EmitPred inp₀
          (Function.update
            (Function.update
              (Function.update (scratch base tmp tmp2 0) pos2Reg (regTape 1))
              pos2Reg (regTape (1 + j))) pos2Fuel ⟨j + 2, regCells P⟩)
          (ys₁ ++ (List.range (j + 1)).flatMap (fun j' =>
            allSyms.flatMap (fun sw =>
              (List.range (P + 1)).flatMap (fun po =>
                allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
                  CNF.encode (activeClausesAtF N steps P t q pi si (1 + j')
                    sw po so b))))))))
        (activeSwLevelBudget M) := by
    intro j hj
    set base' : Fin nT → Tape :=
      Function.update (Function.update base pos2Reg (regTape (1 + j))) pos2Fuel
        ⟨j + 2, regCells P⟩ with hbase'
    have hstate : Function.update
        (Function.update
          (Function.update (scratch base tmp tmp2 0) pos2Reg (regTape 1))
          pos2Reg (regTape (1 + j))) pos2Fuel ⟨j + 2, regCells P⟩
        = scratch base' tmp tmp2 0 := by
      rw [Function.update_idem, scratch_update_comm (by decide) (by decide),
        scratch_update_comm (by decide) (by decide)]
    have hB' : ActiveBase Qc steps P M t pi (1 + j) 0 base' :=
      ⟨hB.hM, hB.ht, hB.hpi, by omega, by omega,
       parked_update (parked_update hB.parked (parked_regTape _))
         (parked_regCells (by omega)),
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hrA,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hrB,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hrC,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hrD,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.htReg,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.htPlus,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hp1,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_self],
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hp3⟩
    have hsw := activeSwLevelTM_hoareTime N q si false hQc hB'
      (by rw [hbase', Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact haux2)
      (by rw [hbase', Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hf3)
      (fun h => absurd h (by simp)) (fun _ => by omega)
      inp₀
      (ys₁ ++ (List.range j).flatMap (fun j' =>
        allSyms.flatMap (fun sw =>
          (List.range (P + 1)).flatMap (fun po =>
            allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
              CNF.encode (activeClausesAtF N steps P t q pi si (1 + j')
                sw po so b)))))))
      hinp₀
    rw [hstate]
    refine hsw.strengthen_post ?_
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, g2, ?_⟩
    rw [flatMap_range_succ, ← List.append_assoc]
    exact g3
  have hloop := emitLoopFrom_hoareTime (activeSwLevelTM N q si false)
    pos2Reg pos2Fuel (by decide) 1 P M (activeSwLevelBudget M) (by omega)
    (fun j' => allSyms.flatMap (fun sw =>
      (List.range (P + 1)).flatMap (fun po =>
        allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
          CNF.encode (activeClausesAtF N steps P t q pi si (1 + j')
            sw po so b))))))
    inp₀ (Function.update (scratch base tmp tmp2 0) pos2Reg (regTape 1)) ys₁
    hinp₀ (parked_update (scratch_parked 0 hB.parked) (parked_regTape _))
    (by rw [Function.update_of_ne (by decide),
      scratch_apply_ne (by decide) (by decide)]; exact hf2)
    (by rw [Function.update_self])
    hbody
  -- Part 4: counter back to 0.
  have h₃ : (setConstTM pos2Reg 0).HoareTime
      (EmitPred inp₀
        (Function.update
          (Function.update (scratch base tmp tmp2 0) pos2Reg (regTape 1))
          pos2Reg (regTape (1 + P)))
        (ys₁ ++ (List.range P).flatMap (fun j' =>
          allSyms.flatMap (fun sw =>
            (List.range (P + 1)).flatMap (fun po =>
              allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
                CNF.encode (activeClausesAtF N steps P t q pi si (1 + j')
                  sw po so b))))))))
      (EmitPred inp₀ (scratch base tmp tmp2 0)
        (ys₁ ++ (List.range P).flatMap (fun j' =>
          allSyms.flatMap (fun sw =>
            (List.range (P + 1)).flatMap (fun po =>
              allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
                CNF.encode (activeClausesAtF N steps P t q pi si (1 + j')
                  sw po so b))))))))
      (opBudget M) := by
    refine ((setConstTM_hoareTime pos2Reg 0 (1 + P) inp₀
      (Function.update
        (Function.update (scratch base tmp tmp2 0) pos2Reg (regTape 1)) pos2Reg
        (regTape (1 + P))) _ hinp₀
      (parked_update (parked_update (scratch_parked 0 hB.parked)
        (parked_regTape _)) (parked_regTape _))
      (by rw [Function.update_self])).consequence
      (fun _ _ _ h => h) ?_
      (setConstTM_le_opBudget (show (0:ℕ) ≤ M by omega) (show 1 + P ≤ M by omega)))
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, Function.update_idem, Function.update_idem,
      show regTape 0 = scratch base tmp tmp2 0 pos2Reg from by
        rw [scratch_apply_ne (by decide) (by decide)]; exact hB.hp2.symm,
      Function.update_eq_self]
  -- Glue.
  have h₂₃ := seqTM_hoareTime _ (setConstTM pos2Reg 0)
    (hloop.mono_bound (loop_le_loopBudget (show P ≤ M by omega)))
    (emitPred_transition hinp₀
      (parked_update (parked_update (scratch_parked 0 hB.parked)
        (parked_regTape _)) (parked_regTape _)) _) h₃
  have h₁₂₃ := seqTM_hoareTime (setConstTM pos2Reg 1) _ h₁
    (emitPred_transition hinp₀
      (parked_update (scratch_parked 0 hB.parked) (parked_regTape _)) _) h₂₃
  have hall := seqTM_hoareTime (activeSwLevelTM N q si true) _ h₀
    (emitPred_transition hinp₀ (scratch_parked 0 hB.parked) _) h₁₂₃
  refine hall.consequence (fun _ _ _ h => h) ?_
    (by rw [activePwSplitBudget])
  rintro inp work out ⟨g1, g2, g3⟩
  refine ⟨g1, g2, ?_⟩
  rw [flatMap_range_split P (fun pw => allSyms.flatMap (fun sw =>
    (List.range (P + 1)).flatMap (fun po =>
      allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
        CNF.encode (activeClausesAtF N steps P t q pi si pw sw po so b))))))]
  rw [hys₁] at g3
  rw [← List.append_assoc]
  exact g3

/-- The input-symbol unroll. -/
noncomputable def activeSiLevelTM (q : N.Q) : TM nT :=
  bigSeqTM (allSyms.map (fun si => activePwSplitTM N q si))

/-- Budget of the input-symbol unroll: four work-position blocks. -/
def activeSiLevelBudget (M : ℕ) : ℕ := 4 * (activePwSplitBudget M + 1) + 1

/-- **`activeSiLevelTM` Hoare specification.** -/
theorem activeSiLevelTM_hoareTime (q : N.Q)
    {Qc steps P M t pi : ℕ} {base : Fin nT → Tape}
    (hQc : Qc = Fintype.card N.Q)
    (hB : ActiveBase Qc steps P M t pi 0 0 base)
    (haux2 : base auxReg2 = regTape 0)
    (hf2 : base pos2Fuel = regTape P) (hf3 : base pos3Fuel = regTape P)
    (inp₀ : Tape) (ys : List Bool) (hinp₀ : Parked inp₀) :
    (activeSiLevelTM N q).HoareTime
      (EmitPred inp₀ (scratch base tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch base tmp tmp2 0)
        (ys ++ allSyms.flatMap (fun si =>
          (List.range (P + 1)).flatMap (fun pw =>
            allSyms.flatMap (fun sw =>
              (List.range (P + 1)).flatMap (fun po =>
                allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
                  CNF.encode
                    (activeClausesAtF N steps P t q pi si pw sw po so
                      b)))))))))
      (activeSiLevelBudget M) := by
  have h := bigSeq_emit_hoareTime
    (fun si => activePwSplitTM N q si)
    (fun si => (List.range (P + 1)).flatMap (fun pw =>
      allSyms.flatMap (fun sw =>
        (List.range (P + 1)).flatMap (fun po =>
          allSyms.flatMap (fun so => [true, false].flatMap (fun b =>
            CNF.encode (activeClausesAtF N steps P t q pi si pw sw po so
              b)))))))
    (activePwSplitBudget M) inp₀ (scratch base tmp tmp2 0) hinp₀
    (scratch_parked 0 hB.parked) allSyms
    (fun si _ ys' => activePwSplitTM_hoareTime N q si hQc hB haux2 hf2 hf3
      inp₀ ys' hinp₀)
    ys
  exact h.mono_bound (by rw [activeSiLevelBudget]; simp [allSyms])


-- ════════════════════════════════════════════════════════════════════════
-- The input-position loop, state unroll, row body, and the family
-- ════════════════════════════════════════════════════════════════════════

/-- The input-position sweep for one machine state. -/
noncomputable def activePiLoopTM (q : N.Q) : TM nT :=
  seqTM (emitLoopTM (activeSiLevelTM N q) pos1Reg pos1Fuel)
    (setConstTM pos1Reg 0)

/-- Budget of the input-position sweep: the loop plus the counter reset. -/
def activePiLoopBudget (M : ℕ) : ℕ :=
  loopBudget M (activeSiLevelBudget M) + 1 + opBudget M

set_option maxHeartbeats 4000000 in
/-- **`activePiLoopTM` Hoare specification** (at the row boundary state). -/
theorem activePiLoopTM_hoareTime (q : N.Q)
    {Qc steps P M t : ℕ} {base : Fin nT → Tape}
    (hQc : Qc = Fintype.card N.Q)
    (hB : ActiveBase Qc steps P M t 0 0 0 base)
    (haux2 : base auxReg2 = regTape 0)
    (hf1 : base pos1Fuel = regTape (P + 1))
    (hf2 : base pos2Fuel = regTape P) (hf3 : base pos3Fuel = regTape P)
    (inp₀ : Tape) (ys : List Bool) (hinp₀ : Parked inp₀) :
    (activePiLoopTM N q).HoareTime
      (EmitPred inp₀ (scratch base tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch base tmp tmp2 0)
        (ys ++ (List.range (P + 1)).flatMap (fun pi =>
          allSyms.flatMap (fun si =>
            (List.range (P + 1)).flatMap (fun pw =>
              allSyms.flatMap (fun sw =>
                (List.range (P + 1)).flatMap (fun po =>
                  allSyms.flatMap (fun so =>
                    [true, false].flatMap (fun b =>
                      CNF.encode (activeClausesAtF N steps P t q pi si pw sw
                        po so b))))))))))
      (activePiLoopBudget M) := by
  have hPM : P + 2 ≤ M := by
    have hA1 : (1:ℕ) ≤ steps + 1 := by omega
    obtain ⟨_, _, hCM, _⟩ := radix_caps hA1 (by omega) (by omega)
      (by omega) hB.hM
    omega
  have hbody : ∀ i, i < P + 1 → (activeSiLevelTM N q).HoareTime
      (EmitPred inp₀
        (Function.update
          (Function.update (scratch base tmp tmp2 0) pos1Reg (regTape i))
          pos1Fuel ⟨i + 2, regCells (P + 1)⟩)
        (ys ++ (List.range i).flatMap (fun pi =>
          allSyms.flatMap (fun si =>
            (List.range (P + 1)).flatMap (fun pw =>
              allSyms.flatMap (fun sw =>
                (List.range (P + 1)).flatMap (fun po =>
                  allSyms.flatMap (fun so =>
                    [true, false].flatMap (fun b =>
                      CNF.encode (activeClausesAtF N steps P t q pi si pw sw
                        po so b))))))))))
      (EmitPred inp₀
        (Function.update
          (Function.update (scratch base tmp tmp2 0) pos1Reg (regTape i))
          pos1Fuel ⟨i + 2, regCells (P + 1)⟩)
        (ys ++ (List.range (i + 1)).flatMap (fun pi =>
          allSyms.flatMap (fun si =>
            (List.range (P + 1)).flatMap (fun pw =>
              allSyms.flatMap (fun sw =>
                (List.range (P + 1)).flatMap (fun po =>
                  allSyms.flatMap (fun so =>
                    [true, false].flatMap (fun b =>
                      CNF.encode (activeClausesAtF N steps P t q pi si pw sw
                        po so b))))))))))
      (activeSiLevelBudget M) := by
    intro i hi
    set base' : Fin nT → Tape :=
      Function.update (Function.update base pos1Reg (regTape i)) pos1Fuel
        ⟨i + 2, regCells (P + 1)⟩ with hbase'
    have hstate : Function.update
        (Function.update (scratch base tmp tmp2 0) pos1Reg (regTape i)) pos1Fuel
        ⟨i + 2, regCells (P + 1)⟩ = scratch base' tmp tmp2 0 := by
      rw [scratch_update_comm (by decide) (by decide),
        scratch_update_comm (by decide) (by decide)]
    have hB' : ActiveBase Qc steps P M t i 0 0 base' :=
      ⟨hB.hM, hB.ht, by omega, by omega, by omega,
       parked_update (parked_update hB.parked (parked_regTape _))
         (parked_regCells (by omega)),
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hrA,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hrB,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hrC,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hrD,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.htReg,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.htPlus,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_self],
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hp2,
       by rw [hbase', Function.update_of_ne (by decide),
         Function.update_of_ne (by decide)]; exact hB.hp3⟩
    have hsi := activeSiLevelTM_hoareTime N q hQc hB'
      (by rw [hbase', Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact haux2)
      (by rw [hbase', Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hf2)
      (by rw [hbase', Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hf3)
      inp₀
      (ys ++ (List.range i).flatMap (fun pi =>
        allSyms.flatMap (fun si =>
          (List.range (P + 1)).flatMap (fun pw =>
            allSyms.flatMap (fun sw =>
              (List.range (P + 1)).flatMap (fun po =>
                allSyms.flatMap (fun so =>
                  [true, false].flatMap (fun b =>
                    CNF.encode (activeClausesAtF N steps P t q pi si pw sw
                      po so b)))))))))
      hinp₀
    rw [hstate]
    refine hsi.consequence (fun _ _ _ h => h) ?_ (le_refl _)
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, g2, ?_⟩
    rw [flatMap_range_succ, ← List.append_assoc]
    exact g3
  have hloop := emitLoop_hoareTime (activeSiLevelTM N q) pos1Reg pos1Fuel
    (by decide) (P + 1) M (activeSiLevelBudget M) (by omega)
    (fun pi => allSyms.flatMap (fun si =>
      (List.range (P + 1)).flatMap (fun pw =>
        allSyms.flatMap (fun sw =>
          (List.range (P + 1)).flatMap (fun po =>
            allSyms.flatMap (fun so =>
              [true, false].flatMap (fun b =>
                CNF.encode (activeClausesAtF N steps P t q pi si pw sw
                  po so b))))))))
    inp₀ (scratch base tmp tmp2 0) ys hinp₀ (scratch_parked 0 hB.parked)
    (by rw [scratch_apply_ne (by decide) (by decide)]; exact hf1)
    (by rw [scratch_apply_ne (by decide) (by decide)]; exact hB.hp1)
    hbody
  have hset : (setConstTM pos1Reg 0).HoareTime
      (EmitPred inp₀
        (Function.update (scratch base tmp tmp2 0) pos1Reg (regTape (P + 1)))
        (ys ++ (List.range (P + 1)).flatMap (fun pi =>
          allSyms.flatMap (fun si =>
            (List.range (P + 1)).flatMap (fun pw =>
              allSyms.flatMap (fun sw =>
                (List.range (P + 1)).flatMap (fun po =>
                  allSyms.flatMap (fun so =>
                    [true, false].flatMap (fun b =>
                      CNF.encode (activeClausesAtF N steps P t q pi si pw sw
                        po so b))))))))))
      (EmitPred inp₀ (scratch base tmp tmp2 0)
        (ys ++ (List.range (P + 1)).flatMap (fun pi =>
          allSyms.flatMap (fun si =>
            (List.range (P + 1)).flatMap (fun pw =>
              allSyms.flatMap (fun sw =>
                (List.range (P + 1)).flatMap (fun po =>
                  allSyms.flatMap (fun so =>
                    [true, false].flatMap (fun b =>
                      CNF.encode (activeClausesAtF N steps P t q pi si pw sw
                        po so b))))))))))
      (opBudget M) := by
    refine ((setConstTM_hoareTime pos1Reg 0 (P + 1) inp₀
      (Function.update (scratch base tmp tmp2 0) pos1Reg (regTape (P + 1))) _
      hinp₀ (parked_update (scratch_parked 0 hB.parked) (parked_regTape _))
      (by rw [Function.update_self])).consequence (fun _ _ _ h => h) ?_
      (setConstTM_le_opBudget (show (0:ℕ) ≤ M by omega) (show P + 1 ≤ M by omega)))
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, Function.update_idem,
      show regTape 0 = scratch base tmp tmp2 0 pos1Reg from by
        rw [scratch_apply_ne (by decide) (by decide)]; exact hB.hp1.symm,
      Function.update_eq_self]
  have hseq := seqTM_hoareTime _ (setConstTM pos1Reg 0)
    (hloop.mono_bound (loop_le_loopBudget (show P + 1 ≤ M by omega)))
    (emitPred_transition hinp₀
      (parked_update (scratch_parked 0 hB.parked) (parked_regTape _)) _) hset
  exact hseq.mono_bound (by rw [activePiLoopBudget])

/-- The machine-state unroll. -/
noncomputable def activeQLevelTM : TM nT :=
  bigSeqTM ((Finset.univ : Finset N.Q).toList.map (fun q =>
    activePiLoopTM N q))

/-- Budget of the machine-state unroll: one input-position sweep per state. -/
def activeQLevelBudget (N : NTM 1) (M : ℕ) : ℕ :=
  Fintype.card N.Q * (activePiLoopBudget M + 1) + 1

set_option maxHeartbeats 4000000 in
/-- **`activeQLevelTM` Hoare specification.** -/
theorem activeQLevelTM_hoareTime
    {Qc steps P M t : ℕ} {base : Fin nT → Tape}
    (hQc : Qc = Fintype.card N.Q)
    (hB : ActiveBase Qc steps P M t 0 0 0 base)
    (haux2 : base auxReg2 = regTape 0)
    (hf1 : base pos1Fuel = regTape (P + 1))
    (hf2 : base pos2Fuel = regTape P) (hf3 : base pos3Fuel = regTape P)
    (inp₀ : Tape) (ys : List Bool) (hinp₀ : Parked inp₀) :
    (activeQLevelTM N).HoareTime
      (EmitPred inp₀ (scratch base tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch base tmp tmp2 0)
        (ys ++ (Finset.univ : Finset N.Q).toList.flatMap (fun q =>
          (List.range (P + 1)).flatMap (fun pi =>
            allSyms.flatMap (fun si =>
              (List.range (P + 1)).flatMap (fun pw =>
                allSyms.flatMap (fun sw =>
                  (List.range (P + 1)).flatMap (fun po =>
                    allSyms.flatMap (fun so =>
                      [true, false].flatMap (fun b =>
                        CNF.encode (activeClausesAtF N steps P t q pi si pw
                          sw po so b)))))))))))
      (activeQLevelBudget N M) := by
  have h := bigSeq_emit_hoareTime
    (fun q => activePiLoopTM N q)
    (fun q => (List.range (P + 1)).flatMap (fun pi =>
      allSyms.flatMap (fun si =>
        (List.range (P + 1)).flatMap (fun pw =>
          allSyms.flatMap (fun sw =>
            (List.range (P + 1)).flatMap (fun po =>
              allSyms.flatMap (fun so =>
                [true, false].flatMap (fun b =>
                  CNF.encode (activeClausesAtF N steps P t q pi si pw sw
                    po so b)))))))))
    (activePiLoopBudget M) inp₀ (scratch base tmp tmp2 0) hinp₀
    (scratch_parked 0 hB.parked) (Finset.univ : Finset N.Q).toList
    (fun q _ ys' => activePiLoopTM_hoareTime N q hQc hB haux2 hf1 hf2 hf3
      inp₀ ys' hinp₀)
    ys
  refine h.mono_bound ?_
  have hcard : (Finset.univ : Finset N.Q).toList.length
      = Fintype.card N.Q := by
    rw [Finset.length_toList, Finset.card_univ]
  rw [activeQLevelBudget, hcard]

/-- The active row body: bump the successor-row register, then the state
    unroll. -/
noncomputable def activeRowTM : TM nT :=
  seqTM (incRegTM tPlusReg) (activeQLevelTM N)

/-- Budget of the row body: the register bump plus the state unroll. -/
def activeRowBudget (N : NTM 1) (M : ℕ) : ℕ :=
  opBudget M + 1 + activeQLevelBudget N M

/-- **The active-family emitter**: loop the row body over rows
    `0..steps-1`. -/
noncomputable def emitActiveTM : TM nT := emitLoopTM (activeRowTM N) tReg tFuel

set_option maxHeartbeats 4000000 in
/-- **`activeRowTM` Hoare specification** (at row `i < steps`; the
    successor-row register enters at `i` and leaves at `i + 1`). -/
theorem activeRowTM_hoareTime (Qc steps P M i : ℕ)
    (hQc : Qc = Fintype.card N.Q)
    (hM : 4 * (steps + 1) * (max Qc 3) * (P + 2) * 4 ≤ M)
    (hi : i < steps)
    (inp₀ : Tape) (V : Fin nT → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hV : ∀ j, Parked (V j))
    (hVrA : V rA = regTape (steps + 1)) (hVrB : V rB = regTape (max Qc 3))
    (hVrC : V rC = regTape (P + 2)) (hVrD : V rD = regTape 4)
    (hVt : V tReg = regTape i) (hVtp : V tPlusReg = regTape i)
    (hVp1 : V pos1Reg = regTape 0) (hVp2 : V pos2Reg = regTape 0)
    (hVp3 : V pos3Reg = regTape 0) (hVaux2 : V auxReg2 = regTape 0)
    (hVf1 : V pos1Fuel = regTape (P + 1))
    (hVf2 : V pos2Fuel = regTape P) (hVf3 : V pos3Fuel = regTape P) :
    (activeRowTM N).HoareTime
      (EmitPred inp₀ (scratch V tmp tmp2 0) ys)
      (EmitPred inp₀
        (scratch (Function.update V tPlusReg (regTape (i + 1))) tmp tmp2 0)
        (ys ++ (Finset.univ : Finset N.Q).toList.flatMap (fun q =>
          (List.range (P + 1)).flatMap (fun pi =>
            allSyms.flatMap (fun si =>
              (List.range (P + 1)).flatMap (fun pw =>
                allSyms.flatMap (fun sw =>
                  (List.range (P + 1)).flatMap (fun po =>
                    allSyms.flatMap (fun so =>
                      [true, false].flatMap (fun b =>
                        CNF.encode (activeClausesAtF N steps P i q pi si pw
                          sw po so b)))))))))))
      (activeRowBudget N M) := by
  set V₁ : Fin nT → Tape := Function.update V tPlusReg (regTape (i + 1))
    with hV₁
  have hV₁P : ∀ j, Parked (V₁ j) := parked_update hV (parked_regTape _)
  have hinc : (incRegTM tPlusReg).HoareTime
      (EmitPred inp₀ (scratch V tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch V₁ tmp tmp2 0) ys) (opBudget M) := by
    refine ((incRegTM_hoareTime tPlusReg i inp₀ (scratch V tmp tmp2 0) ys
      hinp₀ (fun l _ => scratch_parked 0 hV l)
      (by rw [scratch_apply_ne (by decide) (by decide)]; exact hVtp)
      ).consequence (fun _ _ _ h => h) ?_
      (incRegTM_le_opBudget (by
        have hA1 : (1:ℕ) ≤ steps + 1 := by omega
        obtain ⟨hAM, _, _, _⟩ := radix_caps hA1 (by omega) (by omega)
          (by omega) hM
        omega)))
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, scratch_update_comm (by decide) (by decide)]
  have hB₁ : ActiveBase Qc steps P M i 0 0 0 V₁ :=
    ⟨hM, hi, by omega, by omega, by omega, hV₁P,
     by rw [hV₁, Function.update_of_ne (by decide)]; exact hVrA,
     by rw [hV₁, Function.update_of_ne (by decide)]; exact hVrB,
     by rw [hV₁, Function.update_of_ne (by decide)]; exact hVrC,
     by rw [hV₁, Function.update_of_ne (by decide)]; exact hVrD,
     by rw [hV₁, Function.update_of_ne (by decide)]; exact hVt,
     by rw [hV₁, Function.update_self],
     by rw [hV₁, Function.update_of_ne (by decide)]; exact hVp1,
     by rw [hV₁, Function.update_of_ne (by decide)]; exact hVp2,
     by rw [hV₁, Function.update_of_ne (by decide)]; exact hVp3⟩
  have hq := activeQLevelTM_hoareTime N hQc hB₁
    (by rw [hV₁, Function.update_of_ne (by decide)]; exact hVaux2)
    (by rw [hV₁, Function.update_of_ne (by decide)]; exact hVf1)
    (by rw [hV₁, Function.update_of_ne (by decide)]; exact hVf2)
    (by rw [hV₁, Function.update_of_ne (by decide)]; exact hVf3)
    inp₀ ys hinp₀
  have hseq := seqTM_hoareTime (incRegTM tPlusReg) (activeQLevelTM N) hinc
    (emitPred_transition hinp₀ (scratch_parked 0 hV₁P) _) hq
  exact hseq.mono_bound (by rw [activeRowBudget])


set_option maxHeartbeats 4000000 in
/-- **`emitActiveTM` Hoare specification**: appends the encoded active
    transition family, leaving row counter and successor-row register at
    `steps`. -/
theorem emitActiveTM_hoareTime (Qc steps P M : ℕ)
    (hQc : Qc = Fintype.card N.Q)
    (hM : 4 * (steps + 1) * (max Qc 3) * (P + 2) * 4 ≤ M)
    (inp₀ : Tape) (work₀ : Fin nT → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hrA : work₀ rA = regTape (steps + 1))
    (hrB : work₀ rB = regTape (max Qc 3))
    (hrC : work₀ rC = regTape (P + 2))
    (hrD : work₀ rD = regTape 4)
    (htReg : work₀ tReg = regTape 0)
    (htFuel : work₀ tFuel = regTape steps)
    (htp : work₀ tPlusReg = regTape 0)
    (hp1 : work₀ pos1Reg = regTape 0)
    (hp2 : work₀ pos2Reg = regTape 0)
    (hp3 : work₀ pos3Reg = regTape 0)
    (haux2 : work₀ auxReg2 = regTape 0)
    (hf1 : work₀ pos1Fuel = regTape (P + 1))
    (hf2 : work₀ pos2Fuel = regTape P)
    (hf3 : work₀ pos3Fuel = regTape P) :
    (emitActiveTM N).HoareTime
      (EmitPred inp₀ (scratch work₀ tmp tmp2 0) ys)
      (EmitPred inp₀
        (scratch
          (Function.update (Function.update work₀ tReg (regTape steps)) tPlusReg
            (regTape steps)) tmp tmp2 0)
        (ys ++ CNF.encode (activeTransitionClausesF N steps P)))
      (loopBudget M (activeRowBudget N M)) := by
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hM
  set u : ℕ → Fin nT → Tape := fun i =>
    Function.update (Function.update (scratch work₀ tmp tmp2 0) tReg (regTape i))
      tPlusReg (regTape i) with hu
  have huP : ∀ i j, Parked (u i j) := fun i =>
    parked_update (parked_update (scratch_parked 0 hwork₀) (parked_regTape _))
      (parked_regTape _)
  have hbody : ∀ i, i < steps → (activeRowTM N).HoareTime
      (EmitPred inp₀ (Function.update (u i) tFuel ⟨i + 2, regCells steps⟩)
        (ys ++ (List.range i).flatMap (fun t =>
          (Finset.univ : Finset N.Q).toList.flatMap (fun q =>
            (List.range (P + 1)).flatMap (fun pi =>
              allSyms.flatMap (fun si =>
                (List.range (P + 1)).flatMap (fun pw =>
                  allSyms.flatMap (fun sw =>
                    (List.range (P + 1)).flatMap (fun po =>
                      allSyms.flatMap (fun so =>
                        [true, false].flatMap (fun b =>
                          CNF.encode (activeClausesAtF N steps P t q pi si
                            pw sw po so b))))))))))))
      (EmitPred inp₀
        (Function.update (Function.update (u (i + 1)) tReg (regTape i)) tFuel
          ⟨i + 2, regCells steps⟩)
        (ys ++ (List.range (i + 1)).flatMap (fun t =>
          (Finset.univ : Finset N.Q).toList.flatMap (fun q =>
            (List.range (P + 1)).flatMap (fun pi =>
              allSyms.flatMap (fun si =>
                (List.range (P + 1)).flatMap (fun pw =>
                  allSyms.flatMap (fun sw =>
                    (List.range (P + 1)).flatMap (fun po =>
                      allSyms.flatMap (fun so =>
                        [true, false].flatMap (fun b =>
                          CNF.encode (activeClausesAtF N steps P t q pi si
                            pw sw po so b))))))))))))
      (activeRowBudget N M) := by
    intro i hi
    set base : Fin nT → Tape :=
      Function.update
        (Function.update (Function.update work₀ tReg (regTape i)) tPlusReg
          (regTape i)) tFuel ⟨i + 2, regCells steps⟩ with hbase
    have hstate : Function.update (u i) tFuel ⟨i + 2, regCells steps⟩
        = scratch base tmp tmp2 0 := by
      rw [hu]
      show Function.update (Function.update (Function.update
        (scratch work₀ tmp tmp2 0) tReg (regTape i)) tPlusReg (regTape i)) tFuel
        ⟨i + 2, regCells steps⟩ = _
      rw [scratch_update_comm (by decide) (by decide),
        scratch_update_comm (by decide) (by decide),
        scratch_update_comm (by decide) (by decide)]
    have hbaseP : ∀ l, Parked (base l) :=
      parked_update (parked_update (parked_update hwork₀ (parked_regTape _))
        (parked_regTape _)) (parked_regCells (by omega))
    have hrow := activeRowTM_hoareTime N Qc steps P M i hQc hM hi inp₀ base
      (ys ++ (List.range i).flatMap (fun t =>
        (Finset.univ : Finset N.Q).toList.flatMap (fun q =>
          (List.range (P + 1)).flatMap (fun pi =>
            allSyms.flatMap (fun si =>
              (List.range (P + 1)).flatMap (fun pw =>
                allSyms.flatMap (fun sw =>
                  (List.range (P + 1)).flatMap (fun po =>
                    allSyms.flatMap (fun so =>
                      [true, false].flatMap (fun b =>
                        CNF.encode (activeClausesAtF N steps P t q pi si
                          pw sw po so b)))))))))))
      hinp₀ hbaseP
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hrA)
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hrB)
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hrC)
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hrD)
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_self])
      (by rw [hbase, Function.update_of_ne (by decide), Function.update_self])
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hp1)
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hp2)
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hp3)
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact haux2)
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hf1)
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hf2)
      (by rw [hbase, Function.update_of_ne (by decide),
          Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hf3)
    rw [hstate]
    refine hrow.consequence (fun _ _ _ h => h) ?_ (le_refl _)
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, ?_⟩
    · rw [g2, hu]
      show scratch (Function.update base tPlusReg (regTape (i + 1))) tmp tmp2 0
        = Function.update (Function.update (Function.update (Function.update
            (scratch work₀ tmp tmp2 0) tReg (regTape (i + 1))) tPlusReg
            (regTape (i + 1))) tReg (regTape i)) tFuel ⟨i + 2, regCells steps⟩
      rw [hbase,
        show Function.update (Function.update (Function.update
          (Function.update work₀ tReg (regTape i)) tPlusReg (regTape i)) tFuel
          ⟨i + 2, regCells steps⟩) tPlusReg (regTape (i + 1))
        = Function.update (Function.update (Function.update work₀ tReg
            (regTape i)) tPlusReg (regTape (i + 1))) tFuel
            ⟨i + 2, regCells steps⟩ from by
          rw [Function.update_comm (show tFuel ≠ tPlusReg by decide),
            Function.update_idem]]
      rw [show Function.update (Function.update (Function.update
          (Function.update (scratch work₀ tmp tmp2 0) tReg (regTape (i + 1)))
          tPlusReg (regTape (i + 1))) tReg (regTape i)) tFuel
          ⟨i + 2, regCells steps⟩
        = Function.update (Function.update (Function.update
            (scratch work₀ tmp tmp2 0) tReg (regTape i)) tPlusReg
            (regTape (i + 1))) tFuel ⟨i + 2, regCells steps⟩ from by
          rw [Function.update_comm (show tPlusReg ≠ tReg by decide),
            Function.update_idem,
            Function.update_comm (show tReg ≠ tPlusReg by decide)]]
      rw [scratch_update_comm (by decide) (by decide),
        scratch_update_comm (by decide) (by decide),
        scratch_update_comm (by decide) (by decide)]
    · rw [flatMap_range_succ, ← List.append_assoc]
      exact g3
  have hloop := emitLoopGen_hoareTime (activeRowTM N) tReg tFuel (by decide)
    steps M (activeRowBudget N M) (fun i => i)
    (fun i hi => by show i ≤ M; omega)
    (fun t => (Finset.univ : Finset N.Q).toList.flatMap (fun q =>
      (List.range (P + 1)).flatMap (fun pi =>
        allSyms.flatMap (fun si =>
          (List.range (P + 1)).flatMap (fun pw =>
            allSyms.flatMap (fun sw =>
              (List.range (P + 1)).flatMap (fun po =>
                allSyms.flatMap (fun so =>
                  [true, false].flatMap (fun b =>
                    CNF.encode (activeClausesAtF N steps P t q pi si pw sw
                      po so b))))))))))
    inp₀ u ys hinp₀ huP
    (fun i => by
      rw [hu]
      show Function.update _ tPlusReg _ tFuel = _
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        scratch_apply_ne (by decide) (by decide)]
      exact htFuel)
    (fun i => by
      rw [hu]
      show Function.update _ tPlusReg _ tReg = _
      rw [Function.update_of_ne (by decide), Function.update_self])
    hbody
  have hpre : ∀ inp work out,
      EmitPred inp₀ (scratch work₀ tmp tmp2 0) ys inp work out →
      EmitPred inp₀ (u 0) ys inp work out := by
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, hu]
    show scratch work₀ tmp tmp2 0
      = Function.update (Function.update (scratch work₀ tmp tmp2 0) tReg
          (regTape 0)) tPlusReg (regTape 0)
    rw [show regTape 0 = scratch work₀ tmp tmp2 0 tReg from by
        rw [scratch_apply_ne (by decide) (by decide)]; exact htReg.symm,
      Function.update_eq_self,
      show scratch work₀ tmp tmp2 0 tReg = regTape 0 from by
        rw [scratch_apply_ne (by decide) (by decide)]; exact htReg]
    rw [show regTape 0 = scratch work₀ tmp tmp2 0 tPlusReg from by
        rw [scratch_apply_ne (by decide) (by decide)]; exact htp.symm,
      Function.update_eq_self]
  refine (hloop.mono_bound (loop_le_loopBudget (by omega))).consequence
    hpre ?_ (le_refl _)
  rintro inp work out ⟨g1, g2, g3⟩
  refine ⟨g1, ?_, ?_⟩
  · rw [g2, hu]
    show Function.update (Function.update (scratch work₀ tmp tmp2 0) tReg
        (regTape steps)) tPlusReg (regTape steps) = _
    rw [scratch_update_comm (by decide) (by decide),
      scratch_update_comm (by decide) (by decide)]
  · rw [show activeTransitionClausesF N steps P
      = (List.range steps).flatMap (fun t =>
          (Finset.univ : Finset N.Q).toList.flatMap (fun q =>
            (List.range (P + 1)).flatMap (fun pi =>
              allSyms.flatMap (fun si =>
                (List.range (P + 1)).flatMap (fun pw =>
                  allSyms.flatMap (fun sw =>
                    (List.range (P + 1)).flatMap (fun po =>
                      allSyms.flatMap (fun so =>
                        [true, false].flatMap (fun b =>
                          activeClausesAtF N steps P t q pi si pw sw po so
                            b))))))))) from rfl]
    simp only [CNF.encode_flatMap]
    exact g3

end ActiveContext

end SAT

end Complexity
