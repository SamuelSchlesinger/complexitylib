/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.CSPVerifier
public import Complexitylib.Classes.PCP.Internal.ConstraintGraph

/-!
# Proofs as assignments

The proof a PCP verifier reads is an assignment written out: one fixed-width
block per vertex. This module sets up that correspondence — how to cut a proof
into blocks, how to write an assignment as a proof, and that the two are
inverse.

## Main definitions

- `Complexity.blockOf` — the block a proof carries at a vertex
- `Complexity.proofOf` — the proof an assignment writes

## Main results

- `Complexity.blockOf_proofOf` — reading back what was written
- `Complexity.answers_posVal` — the verifier reads exactly the two endpoint
  blocks
- `Complexity.AlgCSP.Models` — an algorithmic graph agrees with a real one
- `Complexity.AlgCSP.Models.sat_of_satisfiable` — completeness transfers
-/

@[expose] public section

namespace Complexity

/-- The block a proof carries at a vertex, when symbols occupy `w` bits. -/
def blockOf (w : ℕ) (π : List Bool) (v : ℕ) : List Bool := (π.drop (v * w)).take w

/-- The proof an assignment writes: the blocks of the first `n` vertices, one
after another. -/
def proofOf (n : ℕ) (f : ℕ → List Bool) : List Bool := (List.range n).flatMap f

theorem length_proofOf {w : ℕ} {f : ℕ → List Bool} (hf : ∀ i, (f i).length = w) :
    ∀ n, (proofOf n f).length = n * w := by
  intro n
  induction n with
  | zero => simp [proofOf]
  | succ n ih =>
      rw [proofOf, List.range_succ, List.flatMap_append, List.length_append]
      rw [proofOf] at ih
      rw [ih]
      simp [hf n]
      ring

/-- **Reading back what was written.** -/
theorem blockOf_proofOf {w : ℕ} {f : ℕ → List Bool} (hf : ∀ i, (f i).length = w) :
    ∀ (n v : ℕ), v < n → blockOf w (proofOf n f) v = f v := by
  intro n
  induction n with
  | zero => intro v hv; omega
  | succ n ih =>
      intro v hv
      have hsplit : proofOf (n + 1) f = proofOf n f ++ f n := by
        rw [proofOf, proofOf, List.range_succ, List.flatMap_append]
        simp
      have hlen : (proofOf n f).length = n * w := length_proofOf hf n
      rcases Nat.lt_or_ge v n with hlt | hge
      · have hvw : v * w + w ≤ n * w := by
          have : (v + 1) * w ≤ n * w := Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul, Nat.one_mul] at this
          omega
        rw [blockOf, hsplit, List.drop_append_of_le_length (by omega),
          List.take_append_of_le_length (by rw [List.length_drop, hlen]; omega)]
        exact ih v hlt
      · have hvn : v = n := by omega
        subst hvn
        rw [blockOf, hsplit, show v * w = (proofOf v f).length from hlen.symm,
          List.drop_left, List.take_of_length_le (by rw [hf])]

theorem length_blockOf {w : ℕ} {π : List Bool} {v : ℕ} (h : (v + 1) * w ≤ π.length) :
    (blockOf w π v).length = w := by
  rw [blockOf, List.length_take, List.length_drop]
  have : v * w + w ≤ π.length := by
    rw [Nat.add_mul, Nat.one_mul] at h
    omega
  omega

theorem getElem_blockOf {w : ℕ} {π : List Bool} {v j : ℕ} (h : (v + 1) * w ≤ π.length)
    (hj : j < w) :
    (blockOf w π v)[j]'(by rw [length_blockOf h]; exact hj) = π.getD (v * w + j) false := by
  have hlt : v * w + j < π.length := by
    rw [Nat.add_mul, Nat.one_mul] at h
    omega
  simp only [blockOf]
  rw [List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hlt]
  rfl

/-- **The verifier reads exactly the two endpoint blocks.** -/
theorem answers_posVal (A : AlgCSP) (x π : List Bool) (e : ℕ)
    (h0 : (A.vert false x e + 1) * A.width ≤ π.length)
    (h1 : (A.vert true x e + 1) * A.width ≤ π.length) :
    PCPVerifier.answers π ((List.range (2 * A.width)).map (A.posVal x e))
      = blockOf A.width π (A.vert false x e) ++ blockOf A.width π (A.vert true x e) := by
  have hb0 : (blockOf A.width π (A.vert false x e)).length = A.width := length_blockOf h0
  have hb1 : (blockOf A.width π (A.vert true x e)).length = A.width := length_blockOf h1
  refine List.ext_getElem ?_ fun j hj1 hj2 => ?_
  · rw [PCPVerifier.answers, List.length_map, List.length_map, List.length_range,
      List.length_append, hb0, hb1]
    ring
  · have hj : j < 2 * A.width := by
      rw [PCPVerifier.answers, List.length_map, List.length_map, List.length_range] at hj1
      exact hj1
    have hans : PCPVerifier.answers π ((List.range (2 * A.width)).map (A.posVal x e))
        = ((List.range (2 * A.width)).map (A.posVal x e)).map (fun i => π.getD i false) :=
      rfl
    simp only [hans]
    rw [List.getElem_map, List.getElem_map, List.getElem_range]
    by_cases hlow : j < A.width
    · rw [List.getElem_append_left (by rw [hb0]; exact hlow), getElem_blockOf h0 hlow,
        AlgCSP.posVal, ite_eq_left hlow]
      simp [hlow]
    · have hge : (blockOf A.width π (A.vert false x e)).length ≤ j := by
        rw [hb0]; omega
      rw [List.getElem_append_right hge]
      simp only [hb0]
      rw [getElem_blockOf h1 (by omega), AlgCSP.posVal, ite_eq_right hlow]
      simp [hlow]

/-! ### Padding a proof -/

theorem answers_append_false (π : List Bool) (k : ℕ) (ps : List ℕ) :
    PCPVerifier.answers π ps
      = PCPVerifier.answers (π ++ List.replicate k false) ps := by
  have hget : ∀ i, π.getD i false = (π ++ List.replicate k false).getD i false := by
    intro i
    by_cases hi : i < π.length
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem (by rw [List.length_append]; omega),
        List.getElem_append_left hi]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      by_cases hi2 : i < (π ++ List.replicate k false).length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2,
          List.getElem_append_right (by omega)]
        simp
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  show ps.map (fun i => π.getD i false) = ps.map _
  exact List.map_congr_left fun i _ => hget i

/-! ### Agreement with a real constraint graph -/

namespace AlgCSP

/-- An algorithmic graph agrees with a real one: same edges, same endpoints,
and the constraint means the same thing once symbols are decoded. -/
structure Models (A : AlgCSP) {α : Type} (G : List Bool → ConstraintGraph α)
    (enc : α → List Bool) (dec : List Bool → α) : Prop where
  /-- The edge counts agree. -/
  numEdges_eq : ∀ x, A.numEdges x = (G x).numEdges
  /-- The first endpoint agrees. -/
  tail_eq : ∀ (x : List Bool) (e : ℕ) (he : e < (G x).numEdges),
    A.vert false x e = ((G x).tail ⟨e, he⟩).val
  /-- The second endpoint agrees. -/
  head_eq : ∀ (x : List Bool) (e : ℕ) (he : e < (G x).numEdges),
    A.vert true x e = ((G x).head ⟨e, he⟩).val
  /-- Symbols occupy exactly the block width. -/
  length_enc : ∀ s : α, (enc s).length = A.width
  /-- Decoding inverts encoding. -/
  dec_enc : ∀ s : α, dec (enc s) = s
  /-- The constraint agrees on blocks. -/
  ok_iff : ∀ (x : List Bool) (e : ℕ) (he : e < (G x).numEdges) (u v : List Bool),
    u.length = A.width → v.length = A.width →
      (pair (pair x (List.replicate e true)) (u ++ v) ∈ A.ok
        ↔ (G x).rel ⟨e, he⟩ (dec u) (dec v) = true)

variable {A : AlgCSP} {α : Type} [Inhabited α] {G : List Bool → ConstraintGraph α}
  {enc : α → List Bool} {dec : List Bool → α}

/-- The proof an assignment writes. -/
def assignProof (enc : α → List Bool)
    (n : ℕ) (a : Fin n → α) : List Bool :=
  proofOf n (fun v => if h : v < n then enc (a ⟨v, h⟩) else enc default)

theorem length_assignProof (hM : A.Models G enc dec) (n : ℕ) (a : Fin n → α) :
    (assignProof enc n a).length = n * A.width := by
  refine length_proofOf (w := A.width) (fun i => ?_) n
  by_cases h : i < n <;> simp [h, hM.length_enc]

theorem blockOf_assignProof (hM : A.Models G enc dec) {n : ℕ} (a : Fin n → α)
    {v : ℕ} (hv : v < n) :
    blockOf A.width (assignProof enc n a) v = enc (a ⟨v, hv⟩) := by
  have := blockOf_proofOf (w := A.width)
    (f := fun v => if h : v < n then enc (a ⟨v, h⟩) else enc default)
    (fun i => by by_cases h : i < n <;> simp [h, hM.length_enc]) n v hv
  rw [assignProof, this]
  rw [dite_eq_left hv]

/-- **Completeness transfers.** A satisfying assignment writes a proof the
verifier accepts on every edge. -/
theorem Models.sat_of_satisfiable (hM : A.Models G enc dec) (x : List Bool)
    (h : (G x).Satisfiable) :
    ∃ π : List Bool, ∀ e < A.numEdges x, A.Sat x π e := by
  obtain ⟨a, ha⟩ := h
  refine ⟨assignProof enc (G x).numVerts a, ?_⟩
  intro e he
  rw [hM.numEdges_eq] at he
  set π := assignProof enc (G x).numVerts a with hπ
  have hlen : π.length = (G x).numVerts * A.width := length_assignProof hM _ a
  have h0 : A.vert false x e = ((G x).tail ⟨e, he⟩).val := hM.tail_eq x e he
  have h1 : A.vert true x e = ((G x).head ⟨e, he⟩).val := hM.head_eq x e he
  have hb0 : (A.vert false x e + 1) * A.width ≤ π.length := by
    rw [hlen, h0]
    exact Nat.mul_le_mul_right _ ((G x).tail ⟨e, he⟩).isLt
  have hb1 : (A.vert true x e + 1) * A.width ≤ π.length := by
    rw [hlen, h1]
    exact Nat.mul_le_mul_right _ ((G x).head ⟨e, he⟩).isLt
  have hv0 : blockOf A.width π (A.vert false x e) = enc (a ((G x).tail ⟨e, he⟩)) := by
    rw [h0, blockOf_assignProof hM a ((G x).tail ⟨e, he⟩).isLt]
  have hv1 : blockOf A.width π (A.vert true x e) = enc (a ((G x).head ⟨e, he⟩)) := by
    rw [h1, blockOf_assignProof hM a ((G x).head ⟨e, he⟩).isLt]
  show pair (pair x (List.replicate e true))
    (PCPVerifier.answers π ((List.range (2 * A.width)).map (A.posVal x e))) ∈ A.ok
  rw [answers_posVal A x π e hb0 hb1, hv0, hv1,
    hM.ok_iff x e he _ _ (hM.length_enc _) (hM.length_enc _), hM.dec_enc, hM.dec_enc]
  exact ha ⟨e, he⟩

theorem card_filter_range_eq {n : ℕ} (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range n).filter P).card
      = (Finset.univ.filter (fun i : Fin n => P i.val)).card := by
  refine Finset.card_bij (fun i hi => (⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩
    : Fin n)) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hi).2
  · intro i hi j hj hij
    exact congrArg Fin.val hij
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact ⟨b.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr b.isLt, hb⟩, rfl⟩

omit [Inhabited α] in
open Classical in
/-- **Soundness transfers.** No proof satisfies more than a `1 - gap` fraction
of the edges. -/
theorem Models.card_sat_le [Fintype α] [Nonempty α] (hM : A.Models G enc dec)
    (x : List Bool) {gap : ℚ} (hgap : gap ≤ (G x).unsatVal) (π : List Bool) :
    (((Finset.range (A.numEdges x)).filter (A.Sat x π)).card : ℚ)
      ≤ (1 - gap) * A.numEdges x := by
  classical
  set π' := π ++ List.replicate ((G x).numVerts * A.width) false with hπ'
  have hlen : (G x).numVerts * A.width ≤ π'.length := by
    rw [hπ', List.length_append, List.length_replicate]
    omega
  set a : (G x).Assignment := fun v => dec (blockOf A.width π' v.val) with ha
  have hstep : ∀ (e : Fin (G x).numEdges),
      A.Sat x π e.val ↔ (G x).satisfies a e = true := by
    intro e
    have h0 : A.vert false x e.val = ((G x).tail e).val := hM.tail_eq x e.val e.isLt
    have h1 : A.vert true x e.val = ((G x).head e).val := hM.head_eq x e.val e.isLt
    have hb0 : (A.vert false x e.val + 1) * A.width ≤ π'.length := by
      refine le_trans (Nat.mul_le_mul_right _ ?_) hlen
      rw [h0]
      exact ((G x).tail e).isLt
    have hb1 : (A.vert true x e.val + 1) * A.width ≤ π'.length := by
      refine le_trans (Nat.mul_le_mul_right _ ?_) hlen
      rw [h1]
      exact ((G x).head e).isLt
    show pair (pair x (List.replicate e.val true))
      (PCPVerifier.answers π ((List.range (2 * A.width)).map (A.posVal x e.val))) ∈ A.ok ↔ _
    rw [answers_append_false π ((G x).numVerts * A.width), ← hπ',
      answers_posVal A x π' e.val hb0 hb1,
      hM.ok_iff x e.val e.isLt _ _ (length_blockOf hb0) (length_blockOf hb1)]
    rw [ConstraintGraph.satisfies, ha, h0, h1]
  have hcard : ((Finset.range (A.numEdges x)).filter (A.Sat x π)).card
      = (Finset.univ.filter
          (fun e : Fin (G x).numEdges => (G x).satisfies a e = true)).card := by
    rw [hM.numEdges_eq, card_filter_range_eq]
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hstep e
  have hunsat : (G x).unsatEdges a
      = Finset.univ.filter (fun e : Fin (G x).numEdges => ¬ ((G x).satisfies a e = true)) := by
    ext e
    simp [ConstraintGraph.unsatEdges, ConstraintGraph.Satisfies]
  have hsplit : (Finset.univ.filter
      (fun e : Fin (G x).numEdges => (G x).satisfies a e = true)).card
      + ((G x).unsatEdges a).card = (G x).numEdges := by
    rw [hunsat]
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (G x).numEdges)))
      (p := fun e => (G x).satisfies a e = true)
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h
  rw [hcard, hM.numEdges_eq]
  rcases Nat.eq_zero_or_pos (G x).numEdges with h0 | hpos
  · have hIE : IsEmpty (Fin (G x).numEdges) := ⟨fun e => absurd e.isLt (by omega)⟩
    have hempty : (Finset.univ.filter
        (fun e : Fin (G x).numEdges => (G x).satisfies a e = true)).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.eq_empty_of_isEmpty _)
    rw [hempty, h0]
    simp
  · have hNQ : (0 : ℚ) < ((G x).numEdges : ℚ) := by exact_mod_cast hpos
    have hfrac : gap ≤ ((((G x).unsatEdges a).card : ℚ)) / ((G x).numEdges : ℚ) :=
      le_trans hgap ((G x).unsatVal_le a)
    have hge : gap * ((G x).numEdges : ℚ) ≤ (((G x).unsatEdges a).card : ℚ) := by
      rw [le_div_iff₀ hNQ] at hfrac
      exact hfrac
    have hs : ((Finset.univ.filter
        (fun e : Fin (G x).numEdges => (G x).satisfies a e = true)).card : ℚ)
        + ((((G x).unsatEdges a).card : ℚ)) = ((G x).numEdges : ℚ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hsplit
    linarith

end AlgCSP

end Complexity
