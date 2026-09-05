/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.TesterCore
public import Complexitylib.Classes.PCP.Internal.LocalTest
public import Complexitylib.Classes.PCP.Internal.RegCSP

/-!
# Dinur's composition: alphabet reduction

The powering step leaves a constraint graph over an enormous (though constant)
alphabet. Composition brings the alphabet back down to a fixed one, at the cost
of a constant factor in the unsatisfiability value that does *not* depend on the
alphabet being reduced. That independence is what lets the powering step's gain
win.

The construction: every vertex of the outer graph gets a block of positions
holding the **Hadamard encoding** of its label; every dart gets a proof for the
assembled tester of `TesterCore`, whose input tables are the encodings at its
two ends and whose constraint is the dart's relation, spelled out on encoded
pairs. The tester's reads make a `MultiTest`, and `LocalTest` turns it into a
binary constraint graph over the fixed alphabet `Alpha ReadIdx`.

Soundness decodes an assignment of the composed graph to one of the outer graph
by nearest codeword at every vertex. Whenever the decoded assignment violates a
dart, that dart's tester rejects on a `1/32` fraction of its random strings —
otherwise the tester's own soundness would produce a satisfying pair whose
encodings are close to both blocks, and closeness to a codeword pins the
decoded labels down. Each rejecting string costs one of the `22` edges it owns.

## Main definitions

- `Complexity.ReadIdx` — the tester's `22` reads
- `Complexity.RegCSP.compose` — the composed `MultiTest`
- `Complexity.RegCSP.decodeAssign` — decoding an assignment of the composed
  graph

## Main results

- `Complexity.RegCSP.le_unsatVal_compose` — the value drops by at most `704`
- `Complexity.RegCSP.satisfiable_compose` — satisfiability is preserved
-/

@[expose] public section

namespace Complexity

open BooleanAnalysis

/-! ### The reads -/

/-- The tester's reads, by check: linearity of `F` (three), linearity of `G`
(three), consistency (six), the constraint (four), and the two input tables
(three each: the input coordinate and two self-correction reads). -/
inductive ReadIdx
  | f1x | f1y | f1s
  | g2x | g2y | g2s
  | c3cQ | c3tQ | c3cX | c3xX | c3cY | c3yY
  | k4qG | k4tG | k4cF | k4lF
  | i5r | i5c | i5b
  | i6r | i6c | i6b
  deriving DecidableEq

open ReadIdx in
/-- All twenty-two reads, in declaration order. -/
instance : Fintype ReadIdx where
  elems := ⟨↑([f1x, f1y, f1s, g2x, g2y, g2s, c3cQ, c3tQ, c3cX, c3xX, c3cY, c3yY,
      k4qG, k4tG, k4cF, k4lF, i5r, i5c, i5b, i6r, i6c, i6b] : List ReadIdx), by decide⟩
  complete := fun x => by cases x <;> decide

theorem card_readIdx : Fintype.card ReadIdx = 22 := rfl

instance : Nonempty ReadIdx := ⟨ReadIdx.f1x⟩

/-- The reads are numbered by their own enumeration: there are twenty-two of
them, so this is a lookup on a bounded key. -/
noncomputable instance : NumEnc ReadIdx := NumEnc.ofFintype _

/-! ### Signs and bits -/

theorem chi_eq_chi_iff (u v : ZMod 2) : chi u = chi v ↔ u = v := by
  constructor
  · intro h
    have h' := signBit_chi u
    rw [h, signBit_chi] at h'
    exact h'.symm
  · intro h
    rw [h]

theorem signBit_signOf_mul {m : ℕ} (F : Cube m → ZMod 2) (u v : Cube m) :
    signBit (signOf F u * signOf F v) = F u + F v := by
  show signBit (chi (F u) * chi (F v)) = _
  rw [← BooleanAnalysis.Internal.chi_add, signBit_chi]

theorem signOf_mul_eq_iff {m : ℕ} (F : Cube m → ZMod 2) (u v w : Cube m) :
    signOf F u * signOf F v = signOf F w ↔ F u + F v = F w := by
  show chi (F u) * chi (F v) = chi (F w) ↔ _
  rw [← BooleanAnalysis.Internal.chi_add, chi_eq_chi_iff]

/-! ### The checks as a formula on the bits read -/

namespace Tester

variable {B : ℕ}

/-- The tester's verdict as a formula on the bits it read. -/
noncomputable def bitFormula (S : Finset (Cube (kOf B))) (z : Cube (ROf B))
    (rd : ReadIdx → ZMod 2) : Prop :=
  rd .f1x + rd .f1y = rd .f1s
    ∧ rd .g2x + rd .g2y = rd .g2s
    ∧ rd .c3cQ + rd .c3tQ = (rd .c3cX + rd .c3xX) * (rd .c3cY + rd .c3yY)
    ∧ (rd .k4qG + rd .k4tG) + (rd .k4cF + rd .k4lF)
        + (QuadConstraint.combine (oneHotSystem S) (leftBlock (blk4 z))).const = 0
    ∧ rd .i5c + rd .i5b = rd .i5r
    ∧ rd .i6c + rd .i6b = rd .i6r

noncomputable instance (S : Finset (Cube (kOf B))) (z : Cube (ROf B))
    (rd : ReadIdx → ZMod 2) : Decidable (bitFormula S z rd) := by
  unfold bitFormula
  infer_instance

/-- The bits the tester reads from the four tables. -/
noncomputable def readsOf (Tt Th : Cube B → ZMod 2) (F : Cube (nOf B) → ZMod 2)
    (G : Cube (nOf B * nOf B) → ZMod 2) (S : Finset (Cube (kOf B))) (z : Cube (ROf B)) :
    ReadIdx → ZMod 2
  | .f1x => F (leftBlock (blk1 z))
  | .f1y => F (rightBlock (blk1 z))
  | .f1s => F (leftBlock (blk1 z) + rightBlock (blk1 z))
  | .g2x => G (leftBlock (blk2 z))
  | .g2y => G (rightBlock (blk2 z))
  | .g2s => G (leftBlock (blk2 z) + rightBlock (blk2 z))
  | .c3cQ => G (cQ (blk3 z))
  | .c3tQ => G (tensor (qX (blk3 z)) (qY (blk3 z)) + cQ (blk3 z))
  | .c3cX => F (cX (blk3 z))
  | .c3xX => F (qX (blk3 z) + cX (blk3 z))
  | .c3cY => F (cY (blk3 z))
  | .c3yY => F (qY (blk3 z) + cY (blk3 z))
  | .k4qG => G (rightBlock (rightBlock (blk4 z)))
  | .k4tG => G ((QuadConstraint.combine (oneHotSystem S) (leftBlock (blk4 z))).quad
      + rightBlock (rightBlock (blk4 z)))
  | .k4cF => F (leftBlock (rightBlock (blk4 z)))
  | .k4lF => F ((QuadConstraint.combine (oneHotSystem S) (leftBlock (blk4 z))).lin
      + leftBlock (rightBlock (blk4 z)))
  | .i5r => Tt (leftBlock (blk5 z))
  | .i5c => F (rightBlock (blk5 z))
  | .i5b => F (basisVec (inTail B (leftBlock (blk5 z))) + rightBlock (blk5 z))
  | .i6r => Th (leftBlock (blk6 z))
  | .i6c => F (rightBlock (blk6 z))
  | .i6b => F (basisVec (inHead B (leftBlock (blk6 z))) + rightBlock (blk6 z))

/-- **The verdict is the formula on the reads.** -/
theorem allChecks_iff (S : Finset (Cube (kOf B))) (Tt Th : Cube B → ZMod 2)
    (F : Cube (nOf B) → ZMod 2) (G : Cube (nOf B * nOf B) → ZMod 2) (z : Cube (ROf B)) :
    AllChecks S Tt Th F G z ↔ bitFormula S z (readsOf Tt Th F G S z) := by
  unfold AllChecks bitFormula LinCheck TesterAccepts ConstraintAccepts CoordAccepts
  simp only [readsOf, signOf_mul_eq_iff, signBit_signOf_mul]

end Tester

/-! ### The composition -/

namespace RegCSP

open Tester

variable {β : Type} {B : ℕ} (enc : β → Cube B)

/-- A bit table on `Cube B`, as a vector indexed by `Fin (2 ^ B)`. -/
noncomputable def vecOf (t : Cube B → ZMod 2) : Cube (2 ^ B) := fun m => t ((candIdx B).symm m)

/-- The tester's input variables for a pair of labels: the two encodings. -/
noncomputable def inputVec (σ τ : β) : Cube (kOf B) :=
  Fin.append (vecOf (hadamard (enc σ))) (vecOf (hadamard (enc τ)))

theorem tailPart_of_leftBlock (σ τ : β) (a : Cube (nOf B))
    (h : leftBlock a = inputVec enc σ τ) : tailPart a = hadamard (enc σ) := by
  funext r
  have hr : tailPart a r = leftBlock (leftBlock a) (candIdx B r) := rfl
  rw [hr, h]
  show (Fin.append (vecOf (hadamard (enc σ))) (vecOf (hadamard (enc τ))))
    (Fin.castAdd _ (candIdx B r)) = _
  rw [Fin.append_left]
  show hadamard (enc σ) ((candIdx B).symm (candIdx B r)) = _
  rw [Equiv.symm_apply_apply]

theorem headPart_of_leftBlock (σ τ : β) (a : Cube (nOf B))
    (h : leftBlock a = inputVec enc σ τ) : headPart a = hadamard (enc τ) := by
  funext r
  have hr : headPart a r = leftBlock a (Fin.natAdd (2 ^ B) (candIdx B r)) := rfl
  rw [hr, h]
  show (Fin.append (vecOf (hadamard (enc σ))) (vecOf (hadamard (enc τ))))
    (Fin.natAdd _ (candIdx B r)) = _
  rw [Fin.append_right]
  show hadamard (enc τ) ((candIdx B).symm (candIdx B r)) = _
  rw [Equiv.symm_apply_apply]

variable [Fintype β] [DecidableEq β] [Nonempty β] (R : RegCSP β)
  [NumEnc R.graph.V] [NumEnc R.graph.D]

/-- The satisfying set of a dart: the encoded pairs its relation accepts. -/
noncomputable def satSet (p : R.Dart) : Finset (Cube (kOf B)) :=
  (Finset.univ.filter fun st : β × β => R.rel p.1 p.2 st.1 st.2 = true).image
    fun st => inputVec enc st.1 st.2

omit [DecidableEq β] [Nonempty β] [NumEnc R.graph.V] [NumEnc R.graph.D] in
theorem mem_satSet_iff (p : R.Dart) (w : Cube (kOf B)) :
    w ∈ R.satSet enc p ↔ ∃ σ τ, R.rel p.1 p.2 σ τ = true ∧ inputVec enc σ τ = w := by
  simp only [satSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.exists]

/-- The positions of the composed proof: an encoding block per vertex, and a
linear and a quadratic table per dart. -/
abbrev Pos : Type :=
  (R.graph.V × Cube B) ⊕ ((R.Dart × Cube (nOf B)) ⊕ (R.Dart × Cube (nOf B * nOf B)))

/-- **The composed test**: for each dart, the assembled tester on the encodings
at its ends and its own proof tables. -/
noncomputable def compose : MultiTest (R.Pos (B := B)) R.Dart ReadIdx where
  R := ROf B
  pos := fun p z i =>
    match i with
    | .f1x => Sum.inr (Sum.inl (p, leftBlock (blk1 z)))
    | .f1y => Sum.inr (Sum.inl (p, rightBlock (blk1 z)))
    | .f1s => Sum.inr (Sum.inl (p, leftBlock (blk1 z) + rightBlock (blk1 z)))
    | .g2x => Sum.inr (Sum.inr (p, leftBlock (blk2 z)))
    | .g2y => Sum.inr (Sum.inr (p, rightBlock (blk2 z)))
    | .g2s => Sum.inr (Sum.inr (p, leftBlock (blk2 z) + rightBlock (blk2 z)))
    | .c3cQ => Sum.inr (Sum.inr (p, cQ (blk3 z)))
    | .c3tQ => Sum.inr (Sum.inr (p, tensor (qX (blk3 z)) (qY (blk3 z)) + cQ (blk3 z)))
    | .c3cX => Sum.inr (Sum.inl (p, cX (blk3 z)))
    | .c3xX => Sum.inr (Sum.inl (p, qX (blk3 z) + cX (blk3 z)))
    | .c3cY => Sum.inr (Sum.inl (p, cY (blk3 z)))
    | .c3yY => Sum.inr (Sum.inl (p, qY (blk3 z) + cY (blk3 z)))
    | .k4qG => Sum.inr (Sum.inr (p, rightBlock (rightBlock (blk4 z))))
    | .k4tG => Sum.inr (Sum.inr (p,
        (QuadConstraint.combine (oneHotSystem (R.satSet enc p)) (leftBlock (blk4 z))).quad
          + rightBlock (rightBlock (blk4 z))))
    | .k4cF => Sum.inr (Sum.inl (p, leftBlock (rightBlock (blk4 z))))
    | .k4lF => Sum.inr (Sum.inl (p,
        (QuadConstraint.combine (oneHotSystem (R.satSet enc p)) (leftBlock (blk4 z))).lin
          + leftBlock (rightBlock (blk4 z))))
    | .i5r => Sum.inl (p.1, leftBlock (blk5 z))
    | .i5c => Sum.inr (Sum.inl (p, rightBlock (blk5 z)))
    | .i5b => Sum.inr (Sum.inl (p, basisVec (inTail B (leftBlock (blk5 z))) + rightBlock (blk5 z)))
    | .i6r => Sum.inl (R.graph.nbr p.1 p.2, leftBlock (blk6 z))
    | .i6c => Sum.inr (Sum.inl (p, rightBlock (blk6 z)))
    | .i6b => Sum.inr (Sum.inl (p, basisVec (inHead B (leftBlock (blk6 z))) + rightBlock (blk6 z)))
  check := fun p z rd => decide (bitFormula (R.satSet enc p) z rd)

/-- The encoding block at a dart's tail, as the tester's first input table. -/
noncomputable def tailTable (T : MultiTest.Table (R.Pos (B := B))) (p : R.Dart) :
    Cube B → ZMod 2 := fun r => T (Sum.inl (p.1, r))
/-- The encoding block at a dart's head, as the tester's second input table. -/
noncomputable def headTable (T : MultiTest.Table (R.Pos (B := B))) (p : R.Dart) :
    Cube B → ZMod 2 := fun r => T (Sum.inl (R.graph.nbr p.1 p.2, r))
/-- A dart's linear proof table. -/
noncomputable def linTable (T : MultiTest.Table (R.Pos (B := B))) (p : R.Dart) :
    Cube (nOf B) → ZMod 2 := fun x => T (Sum.inr (Sum.inl (p, x)))
/-- A dart's quadratic proof table. -/
noncomputable def quadTable (T : MultiTest.Table (R.Pos (B := B))) (p : R.Dart) :
    Cube (nOf B * nOf B) → ZMod 2 := fun y => T (Sum.inr (Sum.inr (p, y)))

omit [DecidableEq β] [Nonempty β] [NumEnc R.graph.V] [NumEnc R.graph.D] in
/-- **The composed test runs the tester.** -/
theorem accepts_compose_iff (T : MultiTest.Table (R.Pos (B := B))) (p : R.Dart)
    (z : Cube (ROf B)) :
    (R.compose enc).accepts T p z = true
      ↔ AllChecks (R.satSet enc p) (R.tailTable T p) (R.headTable T p) (R.linTable T p)
          (R.quadTable T p) z := by
  rw [allChecks_iff]
  show decide (bitFormula (R.satSet enc p) z fun i => T ((R.compose enc).pos p z i)) = true ↔ _
  rw [decide_eq_true_iff]
  have hreads : (fun i => T ((R.compose enc).pos p z i))
      = readsOf (R.tailTable T p) (R.headTable T p) (R.linTable T p) (R.quadTable T p)
          (R.satSet enc p) z := by
    funext i
    cases i <;> rfl
  rw [hreads]

/-! ### Soundness -/

/-- Decoding an assignment of the composed graph: nearest codeword at each
vertex. -/
noncomputable def decodeAssign (A : (R.compose enc).toGraph.Assignment) : R.Assignment :=
  fun v => decodeLabel enc fun r => (R.compose enc).tableOf A (Sum.inl (v, r))

omit [DecidableEq β] in
/-- **A violated dart rejects a `1/32` fraction of its random strings.** -/
theorem card_rejects_ge (henc : Function.Injective enc)
    (A : (R.compose enc).toGraph.Assignment) (p : R.Dart)
    (hp : ¬ R.Satisfies (R.decodeAssign enc A) p) :
    2 ^ ROf B ≤ 32 * ((R.compose enc).rejects ((R.compose enc).tableOf A) p).card := by
  classical
  by_contra hlt
  push Not at hlt
  set T := (R.compose enc).tableOf A with hT
  have hprob : 1 - 1 / 32 < Pr[AllChecks (R.satSet enc p) (R.tailTable T p) (R.headTable T p)
      (R.linTable T p) (R.quadTable T p)] := by
    have hacc : Pr[fun z : Cube (ROf B) => (R.compose enc).accepts T p z = true]
        = 1 - (((R.compose enc).rejects T p).card : ℝ) / 2 ^ ROf B :=
      (R.compose enc).prob_accepts_eq T p
    have heq : (fun z : Cube (ROf B) => (R.compose enc).accepts T p z = true)
        = AllChecks (R.satSet enc p) (R.tailTable T p) (R.headTable T p)
          (R.linTable T p) (R.quadTable T p) := by
      funext z
      exact propext (R.accepts_compose_iff enc T p z)
    rw [heq] at hacc
    rw [hacc]
    have hlt' : (32 : ℝ) * ((R.compose enc).rejects T p).card < 2 ^ ROf B := by
      exact_mod_cast hlt
    have hpos : (0 : ℝ) < 2 ^ ROf B := by positivity
    rw [sub_lt_sub_iff_left, div_lt_iff₀ hpos]
    linarith
  obtain ⟨a, hsys, hdt, hdh⟩ := Tester.sound _ _ _ _ _ hprob
  have hmem := mem_of_sat_oneHotSystem _ a hsys
  rw [mem_satSet_iff] at hmem
  obtain ⟨σ, τ, hrel, heq⟩ := hmem
  have htail := tailPart_of_leftBlock enc σ τ a heq.symm
  have hhead := headPart_of_leftBlock enc σ τ a heq.symm
  rw [htail] at hdt
  rw [hhead] at hdh
  have hdt' : bitDist (R.tailTable T p) (hadamard (enc σ)) < 1 / 4 := by linarith
  have hdh' : bitDist (R.headTable T p) (hadamard (enc τ)) < 1 / 4 := by linarith
  have hσ : R.decodeAssign enc A p.1 = σ := decodeLabel_eq enc henc _ σ hdt'
  have hτ : R.decodeAssign enc A (R.graph.nbr p.1 p.2) = τ := decodeLabel_eq enc henc _ τ hdh'
  apply hp
  show R.rel p.1 p.2 (R.decodeAssign enc A p.1) (R.decodeAssign enc A (R.graph.nbr p.1 p.2)) = true
  rw [hσ, hτ]
  exact hrel

omit [DecidableEq β] in
/-- **Soundness of composition**, per assignment: the composed graph's violated
fraction is at least the decoded assignment's, divided by `704 = 32 · 22`. -/
theorem unsatFrac_compose_ge (henc : Function.Injective enc)
    (A : (R.compose enc).toGraph.Assignment) :
    R.unsatFrac (R.decodeAssign enc A) / 704 ≤ (R.compose enc).toGraph.unsatFrac A := by
  classical
  refine le_trans ?_ ((R.compose enc).unsatFrac_toGraph_ge A)
  rw [card_readIdx]
  set T := (R.compose enc).tableOf A
  have hsum : ((R.unsatDarts (R.decodeAssign enc A)).card : ℚ) * 2 ^ ROf B
      ≤ 32 * ∑ p : R.Dart, (((R.compose enc).rejects T p).card : ℚ) := by
    have h1 : ∑ p ∈ R.unsatDarts (R.decodeAssign enc A), ((2 : ℚ) ^ ROf B)
        ≤ ∑ p ∈ R.unsatDarts (R.decodeAssign enc A),
          32 * (((R.compose enc).rejects T p).card : ℚ) := by
      refine Finset.sum_le_sum fun p hp => ?_
      rw [mem_unsatDarts] at hp
      exact_mod_cast R.card_rejects_ge enc henc A p hp
    have h2 : ∑ p ∈ R.unsatDarts (R.decodeAssign enc A),
          32 * (((R.compose enc).rejects T p).card : ℚ)
        ≤ ∑ p : R.Dart, 32 * (((R.compose enc).rejects T p).card : ℚ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun p _ _ => by positivity
    rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h1
    rw [← Finset.mul_sum, ← Finset.mul_sum] at h2
    linarith
  have hE : (Fintype.card R.Dart : ℚ) = ((R.graph.order * R.graph.deg : ℕ) : ℚ) := by
    rw [R.card_dart]
  rw [RegCSP.unsatFrac, hE]
  rcases Nat.eq_zero_or_pos (R.graph.order * R.graph.deg) with h0 | h0
  · rw [h0]
    simp
  · have hE' : (0 : ℚ) < ((R.graph.order * R.graph.deg : ℕ) : ℚ) := by exact_mod_cast h0
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have key := mul_le_mul_of_nonneg_right hsum
      (by positivity : (0 : ℚ) ≤ 22 * ((R.graph.order * R.graph.deg : ℕ) : ℚ))
    have key' : ((R.unsatDarts (R.decodeAssign enc A)).card : ℚ) * 2 ^ (R.compose enc).R
        * (22 * ((R.graph.order * R.graph.deg : ℕ) : ℚ))
        ≤ (32 * ∑ p : R.Dart, (((R.compose enc).rejects T p).card : ℚ))
          * (22 * ((R.graph.order * R.graph.deg : ℕ) : ℚ)) := key
    push_cast at key' ⊢
    linarith [key']

omit [DecidableEq β] in
/-- **Soundness of composition.** -/
theorem le_unsatVal_compose (henc : Function.Injective enc) :
    R.unsatVal / 704 ≤ (R.compose enc).toGraph.unsatVal := by
  refine ConstraintGraph.le_unsatVal fun A => ?_
  refine le_trans ?_ (R.unsatFrac_compose_ge enc henc A)
  have := R.unsatVal_le (R.decodeAssign enc A)
  linarith

/-! ### Completeness -/

/-- The honest proof of a satisfying assignment: encodings at the vertices, and
for each dart the Hadamard tables of the one-hot extension of its encoded pair.
-/
noncomputable def honestTable (σ : R.Assignment) : MultiTest.Table (R.Pos (B := B))
  | Sum.inl (v, r) => hadamard (enc (σ v)) r
  | Sum.inr (Sum.inl (p, x)) =>
      hadamard (oneHotExtend (inputVec enc (σ p.1) (σ (R.graph.nbr p.1 p.2)))) x
  | Sum.inr (Sum.inr (p, y)) =>
      hadamard (tensorAssign (oneHotExtend (inputVec enc (σ p.1) (σ (R.graph.nbr p.1 p.2))))) y

omit [DecidableEq β] [Nonempty β] in
/-- **Completeness of composition.** -/
theorem satisfiable_compose (h : R.Satisfiable) : (R.compose enc).toGraph.Satisfiable := by
  obtain ⟨σ, hσ⟩ := h
  refine (R.compose enc).satisfiable_toGraph (R.honestTable enc σ) fun p z => ?_
  erw [accepts_compose_iff]
  set a := oneHotExtend (inputVec enc (σ p.1) (σ (R.graph.nbr p.1 p.2))) with ha
  have hleft : leftBlock a = inputVec enc (σ p.1) (σ (R.graph.nbr p.1 p.2)) :=
    leftBlock_oneHotExtend _
  have htail : R.tailTable (R.honestTable enc σ) p = tailPart a := by
    rw [tailPart_of_leftBlock enc _ _ a hleft]
    rfl
  have hhead : R.headTable (R.honestTable enc σ) p = headPart a := by
    rw [headPart_of_leftBlock enc _ _ a hleft]
    rfl
  have hlin : R.linTable (R.honestTable enc σ) p = hadamard a := rfl
  have hquad : R.quadTable (R.honestTable enc σ) p = hadamard (tensorAssign a) := rfl
  rw [htail, hhead, hlin, hquad]
  refine Tester.complete _ a (sat_oneHotSystem_extend _ _ ?_) z
  rw [mem_satSet_iff]
  exact ⟨σ p.1, σ (R.graph.nbr p.1 p.2), hσ p, rfl⟩

end RegCSP

end Complexity
