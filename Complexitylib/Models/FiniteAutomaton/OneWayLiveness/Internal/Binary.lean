/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Binary.Defs
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.NFABridge
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Encoding

/-!
# Correctness and state cost of the binary liveness scanner

Descending column order lets a countdown retain the selected target vertex.
The codeword transition relation is exactly the relation being encoded.
The arbitrary-word-encoding lower bound then applies with no state loss.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton.BinaryLiveness

open State

lemma evalFrom_seek_bits (n : ℕ) (i : Fin (n + 1)) (bits : List Bool) :
    (machine n).evalFrom {seek i} (bits.map Letter.bit) = {seek i} := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simpa only [List.map_cons, NFA.evalFrom_cons, NFA.stepSet_singleton,
      machine, rules] using ih

lemma evalFrom_carry_bits (n : ℕ) (i : Fin (n + 1)) (bits : List Bool) :
    (machine n).evalFrom {carry i} (bits.map Letter.bit) = {carry i} := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simpa only [List.map_cons, NFA.evalFrom_cons, NFA.stepSet_singleton,
      machine, rules] using ih

lemma columnWord_succ (bits : ℕ → Bool) (k : ℕ) :
    columnWord bits (k + 1) = Letter.bit (bits k) :: columnWord bits k := by
  simp [columnWord, List.range_succ]

lemma evalFrom_empty (n : ℕ) (w : List Letter) :
    (machine n).evalFrom ∅ w = ∅ := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa using ih

lemma evalFrom_scan_columns (n k : ℕ) (hk : k ≤ n) (bits : ℕ → Bool) :
    (machine n).evalFrom {scan ⟨k, by lia⟩} (columnWord bits (k + 1)) =
      {q | ∃ j : Fin (n + 1), q = carry j ∧ j.val ≤ k ∧ bits j.val = true} := by
  induction k with
  | zero =>
    rw [columnWord_succ]
    change (machine n).evalFrom {scan (0 : Fin (n + 1))} [Letter.bit (bits 0)] = _
    rw [NFA.evalFrom_singleton, NFA.stepSet_singleton]
    change (∅ ∪ (if bits 0 then {carry (0 : Fin (n + 1))} else ∅)) = _
    rw [Set.empty_union]
    ext q
    cases q with
    | seek i => cases bits 0 <;> simp
    | scan i => cases bits 0 <;> simp
    | carry i =>
      by_cases hi : i = 0
      · subst i
        simp
      · cases bits 0 <;> simp [hi]
  | succ k ih =>
    rw [columnWord_succ, NFA.evalFrom_cons, NFA.stepSet_singleton]
    change (machine n).evalFrom
      ((if hi : k + 1 = 0 then ∅ else {scan ⟨k + 1 - 1, by lia⟩}) ∪
        (if bits (k + 1) then {carry ⟨k + 1, by lia⟩} else ∅)) _ = _
    simp only [Nat.succ_ne_zero, dite_false,
      Nat.add_sub_cancel, NFA.evalFrom_union]
    rw [ih (by lia)]
    split_ifs with hb
    · rw [show columnWord bits (k + 1) =
          (((List.range (k + 1)).reverse.map bits).map Letter.bit) from rfl,
        evalFrom_carry_bits]
      ext q
      cases q <;> simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff,
        State.carry.injEq, reduceCtorEq, exists_eq_left', false_and, exists_false, or_false]
      case carry i =>
        simp only [Fin.ext_iff]
        constructor
        · rintro (⟨hi, hbi⟩ | hi)
          · exact ⟨by lia, hbi⟩
          · exact ⟨by lia, by simpa only [hi] using hb⟩
        · rintro ⟨hi, hbi⟩
          by_cases hik : i.val ≤ k
          · exact Or.inl ⟨hik, hbi⟩
          · exact Or.inr (by lia)
    · rw [evalFrom_empty]
      ext q
      cases q <;> simp only [Set.union_empty, Set.mem_ofPred_eq,
        State.carry.injEq, reduceCtorEq, exists_eq_left', false_and, exists_false]
      case carry i =>
        constructor
        · rintro ⟨hi, hbi⟩
          exact ⟨by lia, hbi⟩
        · rintro ⟨hi, hbi⟩
          have hne : i.val ≠ k + 1 := by intro he; exact hb (he ▸ hbi)
          exact ⟨by lia, hbi⟩

lemma evalFrom_seek_row (n : ℕ) (i : Fin (n + 1)) (bits : ℕ → Bool) :
    (machine n).evalFrom {seek i} (rowWord n bits) =
      if _hi : i.val = 0 then
        {q | ∃ j : Fin (n + 1), q = carry j ∧ bits j.val = true}
      else {seek ⟨i.val - 1, by lia⟩} := by
  rw [rowWord, NFA.evalFrom_cons, NFA.stepSet_singleton]
  change (machine n).evalFrom
    (if hi : i.val = 0 then {scan (Fin.last n)} else {seek ⟨i.val - 1, by lia⟩}) _ = _
  split_ifs with hi
  · change (machine n).evalFrom {scan ⟨n, Nat.lt_succ_self n⟩} _ = _
    rw [evalFrom_scan_columns n n le_rfl]
    ext q
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨j, hq, _, hb⟩
      exact ⟨j, hq, hb⟩
    · rintro ⟨j, hq, hb⟩
      exact ⟨j, hq, by have := j.isLt; lia, hb⟩
  · exact evalFrom_seek_bits n _ _

lemma evalFrom_carry_row (n : ℕ) (i : Fin (n + 1)) (bits : ℕ → Bool) :
    (machine n).evalFrom {carry i} (rowWord n bits) = {carry i} := by
  rw [rowWord, NFA.evalFrom_cons, NFA.stepSet_singleton]
  exact evalFrom_carry_bits n i _

lemma evalFrom_carry_rows_stop (n : ℕ) (i : Fin (n + 1)) (rows : List (ℕ → Bool)) :
    (machine n).evalFrom {carry i} (rows.flatMap (rowWord n) ++ [Letter.stop]) =
      {seek i} := by
  induction rows with
  | nil => simp [machine, rules]
  | cons b rows ih =>
    rw [List.flatMap_cons, List.append_assoc, NFA.evalFrom_append, evalFrom_carry_row]
    exact ih

lemma evalFrom_row_selection (n : ℕ) (bits : ℕ → Bool) (rows : List (ℕ → Bool)) :
    (machine n).evalFrom {q | ∃ j, q = carry j ∧ bits j.val = true}
        (rows.flatMap (rowWord n) ++ [Letter.stop]) =
      {q | ∃ j, q = seek j ∧ bits j.val = true} := by
  ext q
  rw [NFA.mem_evalFrom_iff_exists]
  constructor
  · rintro ⟨r, ⟨j, rfl, hb⟩, hq⟩
    rw [evalFrom_carry_rows_stop] at hq
    exact ⟨j, hq, hb⟩
  · rintro ⟨j, rfl, hb⟩
    refine ⟨carry j, ⟨j, rfl, hb⟩, ?_⟩
    rw [evalFrom_carry_rows_stop]
    rfl

lemma evalFrom_seek_rows_stop (n : ℕ) (i : Fin (n + 1)) (rows : List (ℕ → Bool)) :
    (machine n).evalFrom {seek i} (rows.flatMap (rowWord n) ++ [Letter.stop]) =
      {q | ∃ j, q = seek j ∧ rowAt rows i.val j.val = true} := by
  induction rows generalizing i with
  | nil =>
    ext q
    simp [machine, rules, rowAt]
  | cons bits rows ih =>
    rw [List.flatMap_cons, List.append_assoc, NFA.evalFrom_append, evalFrom_seek_row]
    split_ifs with hi
    · rw [evalFrom_row_selection]
      simp only [rowAt, hi, List.getElem?_cons_zero, Option.getD_some]
    · rw [ih]
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hi
      simp only [rowAt, hk, Nat.succ_sub_one, List.getElem?_cons_succ]

lemma rowAt_relationRows {n : ℕ} (R : BRel (Fin (n + 1))) (i j : Fin (n + 1)) :
    rowAt (relationRows R) i.val j.val = true ↔ R.holds i j := by
  classical
  simp only [rowAt, relationRows, List.getElem?_ofFn]
  simp only [i.isLt, dite_true, Option.getD_some, j.isLt, decide_eq_true_eq]

lemma evalFrom_seek_code {n : ℕ} (R : BRel (Fin (n + 1))) (i : Fin (n + 1)) :
    (machine n).evalFrom {seek i} (code R) =
      {q | ∃ j, q = seek j ∧ R.holds i j} := by
  rw [code, evalFrom_seek_rows_stop]
  ext q
  simp only [Set.mem_ofPred_eq, rowAt_relationRows]

lemma evalFrom_image_code {n : ℕ} (R : BRel (Fin (n + 1))) (S : Set (Fin (n + 1))) :
    (machine n).evalFrom (seek '' S) (code R) =
      seek '' (livenessNFA (n + 1)).stepSet S R := by
  ext q
  rw [NFA.mem_evalFrom_iff_exists]
  constructor
  · rintro ⟨r, ⟨i, hi, rfl⟩, hq⟩
    rw [evalFrom_seek_code] at hq
    obtain ⟨j, rfl, hj⟩ := hq
    exact ⟨j, NFA.mem_stepSet.mpr ⟨i, hi, hj⟩, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨i, hi, hij⟩ := NFA.mem_stepSet.mp hj
    refine ⟨seek i, ⟨i, hi, rfl⟩, ?_⟩
    rw [evalFrom_seek_code]
    exact ⟨j, rfl, hij⟩

lemma evalFrom_encode {n : ℕ} (w : List (BRel (Fin (n + 1)))) (S : Set (Fin (n + 1))) :
    (machine n).evalFrom (seek '' S) (w.flatMap code) =
      seek '' (livenessNFA (n + 1)).evalFrom S w := by
  induction w generalizing S with
  | nil => rfl
  | cons R w ih =>
    rw [List.flatMap_cons, NFA.evalFrom_append, evalFrom_image_code, ih, NFA.evalFrom_cons]

lemma machine_accepts_code {n : ℕ} (w : List (BRel (Fin (n + 1)))) :
    w.flatMap code ∈ (machine n).accepts ↔ w ∈ oneWayLiveness (n + 1) := by
  rw [← livenessNFA_accepts_proof]
  change (∃ q ∈ Set.range seek,
    q ∈ (machine n).evalFrom (Set.range seek) (w.flatMap code)) ↔
      ∃ j ∈ (Set.univ : Set (Fin (n + 1))),
        j ∈ (livenessNFA (n + 1)).evalFrom Set.univ w
  have he := evalFrom_encode w (Set.univ : Set (Fin (n + 1)))
  rw [Set.image_univ] at he
  rw [he]
  constructor
  · rintro ⟨q, _, j, hj, _⟩
    exact ⟨j, Set.mem_univ _, hj⟩
  · rintro ⟨j, _, hj⟩
    exact ⟨seek j, ⟨j, rfl⟩, j, hj, rfl⟩

lemma evalFrom_binary_letter {Q : Type} (M : NFA Letter Q) (q : Q) (a : Letter) :
    (binaryMachine M).evalFrom {(q, none)} (letterBits a) = boundary (M.step q a) := by
  cases a <;> simp [letterBits, binaryMachine, binaryRules, decode]

lemma evalFrom_binary_boundary_letter {Q : Type} (M : NFA Letter Q) (S : Set Q)
    (a : Letter) :
    (binaryMachine M).evalFrom (boundary S) (letterBits a) =
      boundary (M.stepSet S a) := by
  ext ⟨q, b⟩
  rw [NFA.mem_evalFrom_iff_exists]
  constructor
  · rintro ⟨⟨r, c⟩, ⟨hr, rfl⟩, hp⟩
    rw [evalFrom_binary_letter] at hp
    exact ⟨NFA.mem_stepSet.mpr ⟨r, hr, hp.1⟩, hp.2⟩
  · rintro ⟨hq, rfl⟩
    obtain ⟨r, hr, hqr⟩ := NFA.mem_stepSet.mp hq
    refine ⟨(r, none), ⟨hr, rfl⟩, ?_⟩
    rw [evalFrom_binary_letter]
    exact ⟨hqr, rfl⟩

lemma evalFrom_binary_encode {Q : Type} (M : NFA Letter Q) (S : Set Q) (w : List Letter) :
    (binaryMachine M).evalFrom (boundary S) (w.flatMap letterBits) =
      boundary (M.evalFrom S w) := by
  induction w generalizing S with
  | nil => rfl
  | cons a w ih =>
    rw [List.flatMap_cons, NFA.evalFrom_append, evalFrom_binary_boundary_letter, ih,
      NFA.evalFrom_cons]

lemma binaryMachine_accepts_encode {Q : Type} (M : NFA Letter Q) (w : List Letter) :
    w.flatMap letterBits ∈ (binaryMachine M).accepts ↔ w ∈ M.accepts := by
  change (∃ p ∈ boundary M.accept,
    p ∈ (binaryMachine M).evalFrom (boundary M.start) (w.flatMap letterBits)) ↔ _
  rw [evalFrom_binary_encode, NFA.mem_accepts]
  constructor
  · rintro ⟨⟨q, b⟩, hq, hr⟩
    exact ⟨q, hq.1, hr.1⟩
  · rintro ⟨q, hq, hr⟩
    exact ⟨(q, none), ⟨hq, rfl⟩, ⟨hr, rfl⟩⟩

lemma binary_liveness_accepts_code {n : ℕ} (w : List (BRel (Fin (n + 1)))) :
    w.flatMap binaryCode ∈ (binaryMachine (machine n)).accepts ↔
      w ∈ oneWayLiveness (n + 1) := by
  have hw : w.flatMap binaryCode = (w.flatMap code).flatMap letterBits := by
    rw [List.flatMap_assoc]
    rfl
  rw [hw, binaryMachine_accepts_encode, machine_accepts_code]

lemma card_binary_state (n : ℕ) :
    Fintype.card (State n × Option Bool) = 9 * (n + 1) := by
  let e : State n ≃ Fin (n + 1) ⊕ Fin (n + 1) ⊕ Fin (n + 1) :=
    { toFun := fun q => match q with
        | seek i => .inl i
        | scan i => .inr (.inl i)
        | carry i => .inr (.inr i)
      invFun := fun q => match q with
        | .inl i => seek i
        | .inr (.inl i) => scan i
        | .inr (.inr i) => carry i
      left_inv := by intro q; cases q <;> rfl
      right_inv := by intro q; rcases q with i | (i | i) <;> rfl }
  rw [Fintype.card_prod, Fintype.card_congr e]
  simp [Fintype.card_option]
  ring

lemma binary_state_lower_bound (n : ℕ) (positive : Bool) (s : ℕ) (D : DMachine Bool s)
    (hD : D.Recognizes positive (binaryMachine (machine (n + 1))).accepts) :
    2 ^ (n / 31) ≤ 4 * (s + if positive then 2 else 1) ^ 2 := by
  have hb := encoded_oneWayLiveness_lower_bound (n + 1 + 1) (by lia)
    binaryCode positive s D (fun w => (hD _).trans (binary_liveness_accepts_code w))
  have hn : n + 1 + 1 - 2 = n := by lia
  simpa only [hn] using hb

end Complexity.FiniteAutomaton.BinaryLiveness
