/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.Certificate.Defs

/-!
# Soundness, completeness, and length of existential-SO certificates

Induct along the existential prefix. Each decoded table supplies one semantic
relation; conversely, its characteristic function supplies a certificate block.
At the matrix, acceptance requires that no certificate bits remain.
-/

public section

namespace Complexity.DescriptiveComplexity.SOFormula

private theorem matrix_accepts {V : Vocabulary} (A : DecFinStruct V)
    {rctx : List Nat} {n : Nat} (φ : SOFormula V rctx n) (h : φ.IsFOMatrix)
    (σ : Env A.card n) (ρ : DecREnv A.card rctx) (bits : List Bool) :
    (bits.isEmpty && φ.evalMatrixB A h σ ρ) = true ↔
      bits = [] ∧ φ.Sat A.toFinStruct σ ρ.toREnv := by
  simp only [Bool.and_eq_true, List.isEmpty_iff, evalMatrixB_eq_sat]

theorem checkCertificate_sound_internal {V : Vocabulary} (A : DecFinStruct V)
    {rctx : List Nat} {n : Nat} (φ : SOFormula V rctx n) :
    ∀ (h : φ.IsExistSO) (σ : Env A.card n) (ρ : DecREnv A.card rctx) (bits : List Bool),
      φ.checkCertificate A h σ ρ bits = true →
        bits.length = DecREnv.encodingLength A.card φ.witnessArities ∧
          φ.Sat A.toFinStruct σ ρ.toREnv := by
  induction φ with
  | soExist k φ ih =>
    intro h σ ρ bits haccept
    simp only [checkCertificate] at haccept
    cases hd : DecREnv.decode A.card [k] (bits.take (A.card ^ k)) with
    | none => simp [hd] at haccept
    | some τ =>
      rw [hd] at haccept
      obtain ⟨hlen, hsat⟩ := ih h σ (ρ.cons (τ 0)) (bits.drop (A.card ^ k)) haccept
      have hblock := congrArg List.length ((DecREnv.decode_eq_some_iff _ τ).mp hd)
      simp only [DecREnv.encode_length, DecREnv.encodingLength_cons,
        DecREnv.encodingLength_nil, Nat.add_zero, List.length_take] at hblock
      constructor
      · simp only [witnessArities, DecREnv.encodingLength_cons, List.length_drop] at *
        omega
      · exact ⟨fun args => τ 0 args = true,
          (DecREnv.toREnv_cons (τ 0) ρ ▸ hsat)⟩
  | soAll k φ ih => intro h; exact h.elim
  | relApp i args | soRelApp r args | eq a b | neg φ ih | conj φ ψ ihφ ihψ
  | disj φ ψ ihφ ihψ | exist φ ih | all φ ih =>
    intro h σ ρ bits haccept
    obtain ⟨rfl, hsat⟩ := (matrix_accepts A _ h σ ρ bits).mp haccept
    exact ⟨rfl, hsat⟩

theorem checkCertificate_complete_internal {V : Vocabulary} (A : DecFinStruct V)
    {rctx : List Nat} {n : Nat} (φ : SOFormula V rctx n) :
    ∀ (h : φ.IsExistSO) (σ : Env A.card n) (ρ : DecREnv A.card rctx),
      φ.Sat A.toFinStruct σ ρ.toREnv →
        ∃ bits, φ.checkCertificate A h σ ρ bits = true := by
  classical
  induction φ with
  | soExist k φ ih =>
    intro h σ ρ hsat
    obtain ⟨S, hS⟩ := hsat
    let table : (Fin k → Fin A.card) → Bool := fun args => decide (S args)
    have ht : (fun args => table args = true) = S := by
      funext args
      simp [table]
    have hbody : φ.Sat A.toFinStruct σ (ρ.cons table).toREnv := by
      rw [DecREnv.toREnv_cons, ht]
      exact hS
    obtain ⟨rest, hrest⟩ := ih h σ (ρ.cons table) hbody
    let τ : DecREnv A.card [k] := (DecREnv.empty A.card).cons table
    have hlen : τ.encode.length = A.card ^ k := by simp
    refine ⟨τ.encode ++ rest, ?_⟩
    simp only [checkCertificate, List.take_left' hlen, List.drop_left' hlen,
      DecREnv.decode_encode]
    exact hrest
  | soAll k φ ih => intro h; exact h.elim
  | relApp i args | soRelApp r args | eq a b | neg φ ih | conj φ ψ ihφ ihψ
  | disj φ ψ ihφ ihψ | exist φ ih | all φ ih =>
    intro h σ ρ hsat
    exact ⟨[], (matrix_accepts A _ h σ ρ []).mpr ⟨rfl, hsat⟩⟩

end Complexity.DescriptiveComplexity.SOFormula
