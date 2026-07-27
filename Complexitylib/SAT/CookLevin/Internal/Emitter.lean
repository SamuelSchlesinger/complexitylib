/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.CookLevin
public import Complexitylib.Models.TuringMachine.Registers.DecReg

/-!
# The reduction emitter: clause and CNF machines

Machinery for emitting encoded CNF formulas whose variables are mixed-radix
numerals (`Tableau.flatVar`): literal *descriptors* name a sign, a top digit,
and four digit sources (registers or constants); `emitClauseTM` emits one
clause from a descriptor list; `emitCNFTM` folds clause emitters over a
formula. Each machine's Hoare specification appends exactly the
`CNF.encode`-image of the denoted formula to the output accumulator.

The family drivers (one per `tableauCNFFlat` clause family) instantiate
these with the concrete descriptor lists mirroring each family's
definition.
-/

@[expose] public section

namespace Complexity

namespace SAT

open TM

/-- The encoded word of one literal inside a clause (`Clause.encode_cons'`). -/
def Lit.word (ℓ : Lit) : List Bool :=
  [ℓ.sign, ℓ.sign] ++ List.replicate (2 * ℓ.var) true ++ [false, true]

/-- Prepending a literal to a clause prepends its encoded word (`Lit.word`)
    to the clause encoding. -/
theorem Clause.encode_cons_word (ℓ : Lit) (ℓs : Clause) :
    Clause.encode (ℓ :: ℓs) = ℓ.word ++ Clause.encode ℓs :=
  Clause.encode_cons' ℓ ℓs

/-- A mapped clause encodes as the concatenation of its literal words. -/
theorem Clause.encode_map {α : Type _} (g : α → Lit) (l : List α) :
    Clause.encode (l.map g) = l.flatMap (fun a => (g a).word) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, Clause.encode_cons_word, ih, List.flatMap_cons]

/-- A mapped CNF encodes as the concatenation of its clause words. -/
theorem CNF.encode_map {α : Type _} (g : α → Clause) (l : List α) :
    CNF.encode (l.map g)
      = l.flatMap (fun a => Clause.encode (g a) ++ [true, false]) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, CNF.encode_cons, ih, List.flatMap_cons,
      List.append_assoc]

/-- **Literal descriptor**: the machine-level recipe for one literal — a
    sign, the hardwired top digit, and the four mixed-radix digit sources. -/
structure LitDesc (n : ℕ) where
  /-- The literal's sign: `true` for a positive literal, `false` for negated. -/
  sign : Bool
  /-- The hardwired top (most significant) mixed-radix digit of the variable. -/
  tag : ℕ
  /-- Source of the first mixed-radix digit below the tag (radix `A`). -/
  sa : DigitSrc n
  /-- Source of the second mixed-radix digit below the tag (radix `B`). -/
  sb : DigitSrc n
  /-- Source of the third mixed-radix digit below the tag (radix `C`). -/
  sc : DigitSrc n
  /-- Source of the fourth (least significant) mixed-radix digit (radix `D`). -/
  sd : DigitSrc n

variable {n : ℕ}

/-- The emitting machine of one descriptor. -/
def LitDesc.tm (rA rB rC rD tmp tmp2 : Fin n) (desc : LitDesc n) : TM n :=
  emitVarLitTM rA rB rC rD tmp tmp2 desc.sign desc.tag desc.sa desc.sb
    desc.sc desc.sd

/-- **Descriptor denotation**: `desc` denotes the literal `ℓ` over the work
    tapes `work₀` with radices `A B C D`, all intermediate numeral values
    capped by `M`. -/
def LitDesc.Spec (work₀ : Fin n → Tape) (tmp tmp2 : Fin n) (M A B C D : ℕ)
    (desc : LitDesc n) (ℓ : Lit) : Prop :=
  ∃ a b c d : ℕ,
    DigitSrcSpec work₀ tmp tmp2 desc.sa a ∧ DigitSrcSpec work₀ tmp tmp2 desc.sb b ∧
    DigitSrcSpec work₀ tmp tmp2 desc.sc c ∧ DigitSrcSpec work₀ tmp tmp2 desc.sd d ∧
    ℓ.sign = desc.sign ∧
    ℓ.var = (((desc.tag * A + a) * B + b) * C + c) * D + d ∧
    desc.tag ≤ M ∧ desc.tag * A + a ≤ M ∧ (desc.tag * A + a) * B + b ≤ M ∧
    ((desc.tag * A + a) * B + b) * C + c ≤ M ∧ ℓ.var ≤ M

/-- Denoted variables are capped. -/
theorem LitDesc.Spec.var_le {work₀ : Fin n → Tape} {tmp tmp2 : Fin n}
    {M A B C D : ℕ} {desc : LitDesc n} {ℓ : Lit}
    (h : desc.Spec work₀ tmp tmp2 M A B C D ℓ) : ℓ.var ≤ M := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h
  exact h

section Context

variable (rA rB rC rD tmp tmp2 : Fin n)

/-- **Per-descriptor emission.** A denoting descriptor's machine appends the
    literal's encoded word, moving the scratches to the literal's variable. -/
theorem LitDesc.Spec.emit
    (hAt : rA ≠ tmp) (hAt2 : rA ≠ tmp2) (hBt : rB ≠ tmp) (hBt2 : rB ≠ tmp2)
    (hCt : rC ≠ tmp) (hCt2 : rC ≠ tmp2) (hDt : rD ≠ tmp) (hDt2 : rD ≠ tmp2)
    (htt2 : tmp ≠ tmp2)
    {M A B C D : ℕ} (hA : A ≤ M) (hB : B ≤ M) (hC : C ≤ M) (hD : D ≤ M)
    {desc : LitDesc n} {ℓ : Lit} {work₀ : Fin n → Tape}
    (hspec : desc.Spec work₀ tmp tmp2 M A B C D ℓ)
    (z : ℕ) (hz : z ≤ M)
    (inp₀ : Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hrA : work₀ rA = regTape A) (hrB : work₀ rB = regTape B)
    (hrC : work₀ rC = regTape C) (hrD : work₀ rD = regTape D) :
    (desc.tm rA rB rC rD tmp tmp2).HoareTime
      (EmitPred inp₀ (scratch work₀ tmp tmp2 z) ys)
      (EmitPred inp₀ (scratch work₀ tmp tmp2 ℓ.var) (ys ++ ℓ.word))
      (emitVarBudget M) := by
  obtain ⟨a, b, c, d, hsa, hsb, hsc, hsd, hsign, hvar, htag, h1, h2, h3, h4⟩ :=
    hspec
  have h := emitVarLitTM_hoareTime_scratch rA rB rC rD tmp tmp2 desc.sign desc.tag
    desc.sa desc.sb desc.sc desc.sd hAt hAt2 hBt hBt2 hCt hCt2 hDt hDt2 htt2
    M A B C D a b c d z hA hB hC hD htag hz h1 h2 h3
    (by rw [← hvar]; exact h4)
    inp₀ work₀ ys hinp₀ hwork₀ hrA hrB hrC hrD hsa hsb hsc hsd
  rw [LitDesc.tm]
  rw [Lit.word, hsign, hvar]
  exact h

/-- **Chained literal emission.** A descriptor list denoting the clause `cl`
    appends `Clause.encode cl`, scratches ending at the last variable
    (or staying at `z` for the empty clause). -/
theorem emitLits_hoareTime
    (hAt : rA ≠ tmp) (hAt2 : rA ≠ tmp2) (hBt : rB ≠ tmp) (hBt2 : rB ≠ tmp2)
    (hCt : rC ≠ tmp) (hCt2 : rC ≠ tmp2) (hDt : rD ≠ tmp) (hDt2 : rD ≠ tmp2)
    (htt2 : tmp ≠ tmp2)
    {M A B C D : ℕ} (hA : A ≤ M) (hB : B ≤ M) (hC : C ≤ M) (hD : D ≤ M)
    (inp₀ : Tape) (hinp₀ : Parked inp₀) :
    ∀ {descs : List (LitDesc n)} {cl : Clause} {work₀ : Fin n → Tape},
    List.Forall₂ (LitDesc.Spec work₀ tmp tmp2 M A B C D) descs cl →
    ∀ (z : ℕ), z ≤ M →
    ∀ (ys : List Bool),
    (∀ i, Parked (work₀ i)) →
    work₀ rA = regTape A → work₀ rB = regTape B →
    work₀ rC = regTape C → work₀ rD = regTape D →
    (bigSeqTM (descs.map (LitDesc.tm rA rB rC rD tmp tmp2))).HoareTime
      (EmitPred inp₀ (scratch work₀ tmp tmp2 z) ys)
      (EmitPred inp₀
        (scratch work₀ tmp tmp2 (cl.foldl (fun _ ℓ => ℓ.var) z))
        (ys ++ Clause.encode cl))
      (descs.length * (emitVarBudget M + 1) + 1) := by
  intro descs cl work₀ hf
  induction hf with
  | nil =>
    intro z hz ys hwork₀ hrA hrB hrC hrD
    have hskip := skipTM_hoareTime inp₀ (scratch work₀ tmp tmp2 z) ys hinp₀
      (scratch_parked z hwork₀)
    refine hskip.consequence (fun _ _ _ h => h) ?_ (by omega)
    rintro inp work out ⟨g1, g2, g3⟩
    exact ⟨g1, by rw [g2, List.foldl_nil],
      by rw [Clause.encode_nil, List.append_nil]; exact g3⟩
  | @cons desc ℓ descs' cl' hhead htail ih =>
    intro z hz ys hwork₀ hrA hrB hrC hrD
    have hd := hhead.emit rA rB rC rD tmp tmp2 hAt hAt2 hBt hBt2 hCt hCt2
      hDt hDt2 htt2 hA hB hC hD z hz inp₀ ys hinp₀ hwork₀ hrA hrB hrC hrD
    have hrest := ih ℓ.var hhead.var_le (ys ++ ℓ.word) hwork₀ hrA hrB hrC hrD
    have hseq := seqTM_hoareTime (desc.tm rA rB rC rD tmp tmp2)
      (bigSeqTM (descs'.map (LitDesc.tm rA rB rC rD tmp tmp2))) hd
      (emitPred_transition hinp₀ (scratch_parked _ hwork₀) _) hrest
    refine hseq.consequence (fun _ _ _ h => h) ?_ ?_
    · rintro inp work out ⟨g1, g2, g3⟩
      refine ⟨g1, by rw [g2, List.foldl_cons], ?_⟩
      rwa [Clause.encode_cons_word, ← List.append_assoc]
    · have hmul : (desc :: descs').length * (emitVarBudget M + 1)
          = descs'.length * (emitVarBudget M + 1) + (emitVarBudget M + 1) := by
        rw [List.length_cons]
        exact Nat.succ_mul ..
      simp only [List.length_cons] at hmul ⊢
      omega

/-- Denoted clause variables are capped, hence so is the scratch fold. -/
theorem foldl_var_le {work₀ : Fin n → Tape} {tmp tmp2 : Fin n}
    {M A B C D : ℕ} :
    ∀ {descs : List (LitDesc n)} {cl : Clause},
    List.Forall₂ (LitDesc.Spec work₀ tmp tmp2 M A B C D) descs cl →
    ∀ z, z ≤ M → cl.foldl (fun _ ℓ => ℓ.var) z ≤ M := by
  intro descs cl hf
  induction hf with
  | nil => intro z hz; exact hz
  | @cons desc ℓ descs' cl' hhead _ ih =>
    intro z _
    rw [List.foldl_cons]
    exact ih ℓ.var hhead.var_le

-- ════════════════════════════════════════════════════════════════════════
-- emitClauseTM: one clause, separator, scratch reset
-- ════════════════════════════════════════════════════════════════════════

/-- **Emit one clause**: the literals, the clause separator `[1,0]`, and a
    scratch reset (so clause emitters compose at the scratch-`0` state). -/
def emitClauseTM (descs : List (LitDesc n)) : TM n :=
  seqTM (bigSeqTM (descs.map (LitDesc.tm rA rB rC rD tmp tmp2)))
    (seqTM (emitBitsTM [true, false]) (resetScratchTM tmp tmp2))

/-- Time budget of a clause emitter with at most `L` literals. -/
def clauseBudget (L M : ℕ) : ℕ :=
  L * (emitVarBudget M + 1) + 2 * opBudget M + 6

/-- **`emitClauseTM` Hoare specification**: appends
    `Clause.encode cl ++ [true, false]`, scratches `0` to `0`. -/
theorem emitClauseTM_hoareTime
    (hAt : rA ≠ tmp) (hAt2 : rA ≠ tmp2) (hBt : rB ≠ tmp) (hBt2 : rB ≠ tmp2)
    (hCt : rC ≠ tmp) (hCt2 : rC ≠ tmp2) (hDt : rD ≠ tmp) (hDt2 : rD ≠ tmp2)
    (htt2 : tmp ≠ tmp2)
    {M A B C D : ℕ} (hA : A ≤ M) (hB : B ≤ M) (hC : C ≤ M) (hD : D ≤ M)
    {descs : List (LitDesc n)} {cl : Clause} {work₀ : Fin n → Tape}
    (hf : List.Forall₂ (LitDesc.Spec work₀ tmp tmp2 M A B C D) descs cl)
    {L : ℕ} (hL : descs.length ≤ L)
    (inp₀ : Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hrA : work₀ rA = regTape A) (hrB : work₀ rB = regTape B)
    (hrC : work₀ rC = regTape C) (hrD : work₀ rD = regTape D) :
    (emitClauseTM rA rB rC rD tmp tmp2 descs).HoareTime
      (EmitPred inp₀ (scratch work₀ tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch work₀ tmp tmp2 0)
        (ys ++ (Clause.encode cl ++ [true, false])))
      (clauseBudget L M) := by
  have hlits := emitLits_hoareTime rA rB rC rD tmp tmp2 hAt hAt2 hBt hBt2
    hCt hCt2 hDt hDt2 htt2 hA hB hC hD inp₀ hinp₀ hf 0 (by omega) ys
    hwork₀ hrA hrB hrC hrD
  set zend : ℕ := cl.foldl (fun _ ℓ => ℓ.var) 0 with hzend
  have hzendM : zend ≤ M := foldl_var_le hf 0 (by omega)
  have hsep : (emitBitsTM [true, false] : TM n).HoareTime
      (EmitPred inp₀ (scratch work₀ tmp tmp2 zend) (ys ++ Clause.encode cl))
      (EmitPred inp₀ (scratch work₀ tmp tmp2 zend)
        (ys ++ Clause.encode cl ++ [true, false]))
      2 :=
    emitBitsTM_hoareTime [true, false] inp₀ (scratch work₀ tmp tmp2 zend)
      (ys ++ Clause.encode cl) hinp₀ (scratch_parked zend hwork₀)
  have hreset := resetScratchTM_hoareTime tmp tmp2 htt2 M zend hzendM inp₀
    work₀ (ys ++ Clause.encode cl ++ [true, false]) hinp₀ hwork₀
  have htail := seqTM_hoareTime (emitBitsTM [true, false])
    (resetScratchTM tmp tmp2) hsep
    (emitPred_transition hinp₀ (scratch_parked zend hwork₀) _) hreset
  have hseq := seqTM_hoareTime
    (bigSeqTM (descs.map (LitDesc.tm rA rB rC rD tmp tmp2)))
    (seqTM (emitBitsTM [true, false]) (resetScratchTM tmp tmp2)) hlits
    (emitPred_transition hinp₀ (scratch_parked zend hwork₀) _) htail
  refine hseq.consequence (fun _ _ _ h => h) ?_ ?_
  · rintro inp work out ⟨g1, g2, g3⟩
    exact ⟨g1, g2, by rwa [← List.append_assoc]⟩
  · rw [clauseBudget]
    have : descs.length * (emitVarBudget M + 1) ≤ L * (emitVarBudget M + 1) :=
      Nat.mul_le_mul_right _ hL
    omega

-- ════════════════════════════════════════════════════════════════════════
-- emitCNFTM: a list of clauses
-- ════════════════════════════════════════════════════════════════════════

/-- **Emit a CNF**: fold clause emitters. -/
def emitCNFTM (clss : List (List (LitDesc n))) : TM n :=
  bigSeqTM (clss.map (emitClauseTM rA rB rC rD tmp tmp2))

/-- Time budget of a CNF emitter: `K` clauses of at most `L` literals. -/
def cnfBudget (K L M : ℕ) : ℕ := K * (clauseBudget L M + 1) + 1

/-- **`emitCNFTM` Hoare specification**: appends `CNF.encode φ`, scratches
    `0` to `0`. -/
theorem emitCNFTM_hoareTime
    (hAt : rA ≠ tmp) (hAt2 : rA ≠ tmp2) (hBt : rB ≠ tmp) (hBt2 : rB ≠ tmp2)
    (hCt : rC ≠ tmp) (hCt2 : rC ≠ tmp2) (hDt : rD ≠ tmp) (hDt2 : rD ≠ tmp2)
    (htt2 : tmp ≠ tmp2)
    {M A B C D : ℕ} (hA : A ≤ M) (hB : B ≤ M) (hC : C ≤ M) (hD : D ≤ M)
    (inp₀ : Tape) (hinp₀ : Parked inp₀) :
    ∀ {clss : List (List (LitDesc n))} {φ : CNF} {work₀ : Fin n → Tape},
    List.Forall₂
      (fun descs cl =>
        List.Forall₂ (LitDesc.Spec work₀ tmp tmp2 M A B C D) descs cl)
      clss φ →
    ∀ {L : ℕ}, (∀ descs ∈ clss, descs.length ≤ L) →
    ∀ (ys : List Bool),
    (∀ i, Parked (work₀ i)) →
    work₀ rA = regTape A → work₀ rB = regTape B →
    work₀ rC = regTape C → work₀ rD = regTape D →
    (emitCNFTM rA rB rC rD tmp tmp2 clss).HoareTime
      (EmitPred inp₀ (scratch work₀ tmp tmp2 0) ys)
      (EmitPred inp₀ (scratch work₀ tmp tmp2 0) (ys ++ CNF.encode φ))
      (cnfBudget clss.length L M) := by
  intro clss φ work₀ hf
  induction hf with
  | nil =>
    intro L hL ys hwork₀ hrA hrB hrC hrD
    have hskip := skipTM_hoareTime inp₀ (scratch work₀ tmp tmp2 0) ys hinp₀
      (scratch_parked 0 hwork₀)
    refine hskip.consequence (fun _ _ _ h => h) ?_
      (by rw [cnfBudget]; omega)
    rintro inp work out ⟨g1, g2, g3⟩
    exact ⟨g1, g2, by rw [CNF.encode_nil, List.append_nil]; exact g3⟩
  | @cons descs cl clss' φ' hhead htail ih =>
    intro L hL ys hwork₀ hrA hrB hrC hrD
    have hcl := emitClauseTM_hoareTime rA rB rC rD tmp tmp2 hAt hAt2 hBt hBt2
      hCt hCt2 hDt hDt2 htt2 hA hB hC hD hhead
      (hL descs List.mem_cons_self) inp₀ ys hinp₀ hwork₀ hrA hrB hrC hrD
    have hrest := ih (fun ds hds => hL ds (List.mem_cons_of_mem _ hds))
      (ys ++ (Clause.encode cl ++ [true, false])) hwork₀ hrA hrB hrC hrD
    have hseq := seqTM_hoareTime (emitClauseTM rA rB rC rD tmp tmp2 descs)
      (emitCNFTM rA rB rC rD tmp tmp2 clss') hcl
      (emitPred_transition hinp₀ (scratch_parked 0 hwork₀) _) hrest
    refine hseq.consequence (fun _ _ _ h => h) ?_ ?_
    · rintro inp work out ⟨g1, g2, g3⟩
      refine ⟨g1, g2, ?_⟩
      rw [CNF.encode_cons]
      simpa [List.append_assoc] using g3
    · rw [cnfBudget, cnfBudget]
      have hmul : (clss'.length + 1) * (clauseBudget L M + 1)
          = clss'.length * (clauseBudget L M + 1) + (clauseBudget L M + 1) :=
        Nat.succ_mul ..
      simp only [List.length_cons]
      omega

end Context

end SAT

end Complexity
