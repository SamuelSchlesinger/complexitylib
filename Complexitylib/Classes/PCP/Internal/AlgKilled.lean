/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.AlgPreRot
public import Complexitylib.Classes.PCP.Internal.AlgWalk

/-!
# The killed walk, as an algorithm

The walk length and the killing denominator are constants of a round, so the
walk is a constant-depth unrolling of the preprocessed rotation map, and the
stopping index is chosen by a constant-depth chain of comparisons.

## Main definitions

- `Complexity.selectAt` — choose among constantly many functions by a unary key
- `Complexity.walkFn` — the vertex a walk reaches after a constant number of
  steps

## Main results

- `Complexity.walkFn_mem_FP`, `Complexity.walkFn_eq` — it is an `FP` function,
  and it computes `ConstraintGraph.walkNum`
-/

@[expose] public section

namespace Complexity

variable {α : Type} [Fintype α] [DecidableEq α]

namespace ConstraintGraph

variable (G : ConstraintGraph α) (E : ExpanderFamily)

omit [Fintype α] [DecidableEq α] in
/-- Every code in a cloud is below twice the edge count. -/
theorem mem_cloudCodes_lt {u : Fin G.numVerts} {c : ℕ} (h : c ∈ G.cloudCodes u) :
    c < 2 * G.numEdges := by
  obtain ⟨p, _, rfl⟩ := (G.mem_cloudCodes).mp h
  exact halfCode_lt G p

omit [Fintype α] in
/-- **The rotation map keeps a vertex number in range.** -/
theorem preRotNum_fst_lt {v : ℕ} (hv : v < 2 * G.numEdges) (d : ℕ) :
    (G.preRotNum E v d).1 < 2 * G.numEdges := by
  classical
  have horder : (G.reduce E).graph.order = 2 * G.numEdges := by
    rw [graph_reduce, order_reduceGraph]
  rw [preRotNum]
  split
  · exact hv
  · split
    · simp only
      split <;> omega
    · split
      · simp only
        rw [cloudStepN]
        split
        · split
          · rw [cloudStepNum]
            split
            · simp only
              exact G.mem_cloudCodes_lt (Finset.orderEmbOfFin_mem _ _ _)
            · exact hv
          · exact hv
        · exact hv
      · simp only
        rw [expStepN]
        split
        · split
          · rw [← horder]
            exact Fin.isLt _
          · exact hv
        · exact hv

omit [Fintype α] in
/-- **A walk stays in range.** -/
theorem walkNum_lt {v : ℕ} (hv : v < 2 * G.numEdges) (s : ℕ) :
    ∀ k, G.walkNum E s k v < 2 * G.numEdges := by
  intro k
  induction k with
  | zero => exact hv
  | succ k ih => exact G.preRotNum_fst_lt E ih _

omit [Fintype α] in
/-- **The preprocessed graph has `2 + 2 · deg` darts at a vertex.** -/
theorem preDeg_eq : G.preDeg E = 2 + 2 * E.degree := by
  rw [preDeg, NumEnc.card_eq_fintype_card]
  show Fintype.card (Unit ⊕ (Option (Fin E.degree) ⊕ Fin E.degree)) = _
  simp
  omega

omit [Fintype α] in
theorem preDeg_pos : 0 < G.preDeg E := by rw [G.preDeg_eq E]; omega

end ConstraintGraph

/-! ### Choosing by a unary key -/

/-- Choose among `n + 1` functions by a unary key. -/
noncomputable def selectAt (f : ℕ → List Bool → List Bool) (key : List Bool → List Bool) :
    ℕ → List Bool → List Bool
  | 0, z => f 0 z
  | n + 1, z =>
      ifEqLen (key z) (List.replicate (n + 1) true) (f (n + 1) z) (selectAt f key n z)

theorem selectAt_mem_FP {f : ℕ → List Bool → List Bool} {key : List Bool → List Bool}
    (hf : ∀ k, f k ∈ FP) (hkey : key ∈ FP) : ∀ n, selectAt f key n ∈ FP := by
  intro n
  induction n with
  | zero => exact hf 0
  | succ n ih =>
      refine mem_FP_of_eq (ifEqLen_mem_FP hkey
        (constFn_mem_FP (List.replicate (n + 1) true)) (hf (n + 1)) ih) fun w => ?_
      rw [selectAt]

theorem selectAt_eq {f : ℕ → List Bool → List Bool} {key : List Bool → List Bool}
    {z : List Bool} {m : ℕ} (hkey : key z = List.replicate m true) :
    ∀ {n : ℕ}, m ≤ n → selectAt f key n z = f m z := by
  intro n
  induction n with
  | zero =>
      intro h
      rw [selectAt, Nat.le_zero.mp h]
  | succ n ih =>
      intro h
      rw [selectAt]
      by_cases hm : m = n + 1
      · subst hm
        rw [ifEqLen_pos (by simp [hkey])]
      · rw [ifEqLen_neg (by
          rw [hkey, List.length_replicate, List.length_replicate]
          exact hm), ih (by omega)]

/-! ### Walking -/

variable (F : FinBase) (pol : Polynomial ℕ)

/-- The vertex a walk reaches after `k` steps, on
`pair (graph) (pair (unary vertex) (unary steps))`. -/
noncomputable def walkFn (deg P : ℕ) : ℕ → List Bool → List Bool
  | 0, w => pairFst (pairSnd w)
  | k + 1, w =>
      pairFst (preRotFn F pol deg
        (pair (pairFst w)
          (pair (walkFn deg P k w)
            (modC P (divC (P ^ k) (pairSnd (pairSnd w)))))))

theorem walkFn_mem_FP (deg P : ℕ) : ∀ k, walkFn F pol deg P k ∈ FP := by
  intro k
  induction k with
  | zero =>
      refine mem_FP_of_eq (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP)
        fun w => ?_
      rw [Function.comp_apply, walkFn]
  | succ k ih =>
      have hs : (fun w : List Bool => pairSnd (pairSnd w)) ∈ FP :=
        mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
      have h := mem_FP_comp (Cobham.pairFn_mem_FP Cobham.fstBlock_mem_FP
        (Cobham.pairFn_mem_FP ih (modC_mem_FP (divC_mem_FP hs (P ^ k)) P)))
        (mem_FP_comp (preRotFn_mem_FP F pol deg) Cobham.fstBlock_mem_FP)
      refine mem_FP_of_eq h fun w => ?_
      simp only [Function.comp_apply]
      rw [walkFn]

/-- **The walk algorithm computes the walk.** -/
theorem walkFn_eq (hd : 1 < F.deg) (G : ConstraintGraph α) (v s : ℕ)
    (hv : v < 2 * G.numEdges)
    (hpc : ∀ u : Fin G.numVerts,
      F.fitLevel hd (G.cloudList u).length ≤ pol.eval (G.cloudList u).length)
    (hpe : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges)) :
    ∀ k, walkFn F pol (F.toFamily hd).degree (G.preDeg (F.toFamily hd)) k
        (pair (encGraph G) (pair (List.replicate v true) (List.replicate s true)))
      = List.replicate (G.walkNum (F.toFamily hd) s k v) true := by
  have hPpos : 0 < G.preDeg (F.toFamily hd) := G.preDeg_pos _
  intro k
  induction k with
  | zero =>
      rw [walkFn, pairSnd_pair, pairFst_pair]
      rfl
  | succ k ih =>
      have hdig : modC (G.preDeg (F.toFamily hd))
          (divC (G.preDeg (F.toFamily hd) ^ k) (List.replicate s true))
          = List.replicate ((s / G.preDeg (F.toFamily hd) ^ k)
            % G.preDeg (F.toFamily hd)) true := by
        rw [divC_eq (Nat.pow_pos hPpos), List.length_replicate,
          modC_eq hPpos, List.length_replicate]
      have hdlt : (s / G.preDeg (F.toFamily hd) ^ k) % G.preDeg (F.toFamily hd)
          < 2 + 2 * (F.toFamily hd).degree := by
        rw [← G.preDeg_eq (F.toFamily hd)]
        exact Nat.mod_lt _ hPpos
      rw [walkFn, pairFst_pair, pairSnd_pair, pairSnd_pair, ih, hdig,
        preRotFn_eq G F pol hd _ _ (G.walkNum_lt _ hv s k) hdlt hpc hpe,
        pairFst_pair, ConstraintGraph.walkNum]

/-! ### Where the walk stops -/

theorem findIdx_map {β γ : Type} (f : β → γ) (p : γ → Bool) (l : List β) :
    (l.map f).findIdx p = l.findIdx (fun x => p (f x)) := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.map_cons, List.findIdx_cons, List.findIdx_cons, ih]

/-- The first zero digit at or after `i`, among the next `n` digits. -/
def stopFromNum (q c : ℕ) : ℕ → ℕ → ℕ
  | i, 0 => i
  | i, n + 1 => if (c / q ^ i) % q = 0 then i else stopFromNum q c (i + 1) n

theorem stopFromNum_eq_findIdx (q c : ℕ) : ∀ (n i : ℕ), stopFromNum q c i n
    = i + (List.finRange n).findIdx (fun j : Fin n => (c / q ^ (i + j.val)) % q == 0) := by
  intro n
  induction n with
  | zero =>
      intro i
      rw [stopFromNum, List.finRange_zero, List.findIdx_nil, Nat.add_zero]
  | succ n ih =>
      intro i
      rw [stopFromNum, List.finRange_succ, List.findIdx_cons, findIdx_map]
      by_cases h : (c / q ^ i) % q = 0
      · rw [ite_eq_left h]
        simp [h]
      · rw [ite_eq_right h, ih (i + 1)]
        have hcond : ((c / q ^ (i + (0 : Fin (n + 1)).val)) % q == 0) = false := by
          simpa using h
        rw [hcond]
        have hbody : (List.finRange n).findIdx
            (fun x : Fin n => (c / q ^ (i + (Fin.succ x).val)) % q == 0)
            = (List.finRange n).findIdx
              (fun j : Fin n => (c / q ^ (i + 1 + j.val)) % q == 0) := by
          refine findIdx_congr fun x _ => ?_
          rw [Fin.val_succ, show i + (x.val + 1) = i + 1 + x.val by omega]
        rw [hbody]
        simp only [Bool.false_eq_true, ite_false]
        omega

theorem stopAtNum_eq_stopFromNum (T q c : ℕ) : stopAtNum T q c = stopFromNum q c 0 T := by
  rw [stopFromNum_eq_findIdx, stopAtNum, Nat.zero_add]
  exact (findIdx_congr fun j _ => by rw [Nat.zero_add]).symm

/-- Where the walk stops, from a unary reading `co` of the coins. -/
noncomputable def stopFn (q : ℕ) (co : List Bool → List Bool) :
    ℕ → ℕ → List Bool → List Bool
  | i, 0, _ => List.replicate i true
  | i, n + 1, z =>
      ifEqLen (modC q (divC (q ^ i) (co z))) [] (List.replicate i true)
        (stopFn q co (i + 1) n z)

theorem stopFn_mem_FP {q : ℕ} {co : List Bool → List Bool} (hco : co ∈ FP) :
    ∀ (n i : ℕ), stopFn q co i n ∈ FP := by
  intro n
  induction n with
  | zero => exact fun i => constFn_mem_FP _
  | succ n ih =>
      intro i
      refine mem_FP_of_eq (ifEqLen_mem_FP (modC_mem_FP (divC_mem_FP hco (q ^ i)) q)
        (constFn_mem_FP []) (constFn_mem_FP (List.replicate i true)) (ih (i + 1))) fun w => ?_
      rw [stopFn]

/-- **The stopping algorithm finds the stopping index.** -/
theorem stopFn_eq {q : ℕ} (hq : 0 < q) {co : List Bool → List Bool} {z : List Bool} {c : ℕ}
    (hco : co z = List.replicate c true) :
    ∀ (n i : ℕ), stopFn q co i n z = List.replicate (stopFromNum q c i n) true := by
  intro n
  induction n with
  | zero => intro i; rw [stopFn, stopFromNum]
  | succ n ih =>
      intro i
      have hdig : modC q (divC (q ^ i) (co z)) = List.replicate ((c / q ^ i) % q) true := by
        rw [hco, divC_eq (Nat.pow_pos hq), List.length_replicate, modC_eq hq,
          List.length_replicate]
      rw [stopFn, hdig, stopFromNum]
      by_cases h : (c / q ^ i) % q = 0
      · rw [ite_eq_left h, ifEqLen_pos (by simp [h])]
      · rw [ite_eq_right h, ifEqLen_neg (by simpa using h), ih (i + 1)]

/-! ### The dart the walk comes back by -/

/-- The label the walk's `i`-th step points back along. -/
noncomputable def backFn (deg P i : ℕ) (w : List Bool) : List Bool :=
  pairSnd (preRotFn F pol deg
    (pair (pairFst w)
      (pair (walkFn F pol deg P i w)
        (modC P (divC (P ^ i) (pairSnd (pairSnd w)))))))

theorem backFn_mem_FP (deg P i : ℕ) : backFn F pol deg P i ∈ FP := by
  have hs : (fun w : List Bool => pairSnd (pairSnd w)) ∈ FP :=
    mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  have h := mem_FP_comp (Cobham.pairFn_mem_FP Cobham.fstBlock_mem_FP
    (Cobham.pairFn_mem_FP (walkFn_mem_FP F pol deg P i)
      (modC_mem_FP (divC_mem_FP hs (P ^ i)) P)))
    (mem_FP_comp (preRotFn_mem_FP F pol deg) Cobham.sndBlock_mem_FP)
  refine mem_FP_of_eq h fun w => ?_
  simp only [Function.comp_apply]
  rw [backFn]

variable {F pol} in
/-- **The back-label algorithm reads the label off the rotation map.** -/
theorem backFn_eq (hd : 1 < F.deg) (G : ConstraintGraph α) (v s i : ℕ)
    (hv : v < 2 * G.numEdges)
    (hpc : ∀ u : Fin G.numVerts,
      F.fitLevel hd (G.cloudList u).length ≤ pol.eval (G.cloudList u).length)
    (hpe : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges)) :
    backFn F pol (F.toFamily hd).degree (G.preDeg (F.toFamily hd)) i
        (pair (encGraph G) (pair (List.replicate v true) (List.replicate s true)))
      = List.replicate (G.preRotNum (F.toFamily hd) (G.walkNum (F.toFamily hd) s i v)
          ((s / G.preDeg (F.toFamily hd) ^ i) % G.preDeg (F.toFamily hd))).2 true := by
  have hPpos : 0 < G.preDeg (F.toFamily hd) := G.preDeg_pos _
  have hdig : modC (G.preDeg (F.toFamily hd))
      (divC (G.preDeg (F.toFamily hd) ^ i) (List.replicate s true))
      = List.replicate ((s / G.preDeg (F.toFamily hd) ^ i)
        % G.preDeg (F.toFamily hd)) true := by
    rw [divC_eq (Nat.pow_pos hPpos), List.length_replicate, modC_eq hPpos,
      List.length_replicate]
  have hdlt : (s / G.preDeg (F.toFamily hd) ^ i) % G.preDeg (F.toFamily hd)
      < 2 + 2 * (F.toFamily hd).degree := by
    rw [← G.preDeg_eq (F.toFamily hd)]
    exact Nat.mod_lt _ hPpos
  rw [backFn, pairFst_pair, pairSnd_pair, pairSnd_pair,
    walkFn_eq F pol hd G v s hv hpc hpe, hdig,
    preRotFn_eq G F pol hd _ _ (G.walkNum_lt _ hv s i) hdlt hpc hpe, pairSnd_pair]

/-- The reversed dart's digits, for a fixed stopping index `k`, over the first
`n` places. -/
noncomputable def revSum (deg P k : ℕ) : ℕ → List Bool → List Bool
  | 0, _ => []
  | n + 1, w =>
      revSum deg P k n w ++ mulC (P ^ n)
        (if n < k then backFn F pol deg P (k - 1 - n) w
          else modC P (divC (P ^ n) (pairSnd (pairSnd w))))

theorem revSum_mem_FP (deg P k : ℕ) : ∀ n, revSum F pol deg P k n ∈ FP := by
  intro n
  induction n with
  | zero => exact mem_FP_of_eq (constFn_mem_FP []) fun w => by rw [revSum]
  | succ n ih =>
      have hs : (fun w : List Bool => pairSnd (pairSnd w)) ∈ FP :=
        mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
      have hterm : (fun w : List Bool =>
          if n < k then backFn F pol deg P (k - 1 - n) w
            else modC P (divC (P ^ n) (pairSnd (pairSnd w)))) ∈ FP := by
        by_cases h : n < k
        · simpa [h] using backFn_mem_FP F pol deg P (k - 1 - n)
        · simpa [h] using modC_mem_FP (divC_mem_FP hs (P ^ n)) P
      refine mem_FP_of_eq (Cobham.appendFn_mem_FP ih (mulC_mem_FP hterm (P ^ n))) fun w => ?_
      rw [revSum]

variable {F pol} in
/-- **The digit sum has the reversed dart's number as its length.** -/
theorem length_revSum (hd : 1 < F.deg) (G : ConstraintGraph α) (v s k : ℕ)
    (hv : v < 2 * G.numEdges)
    (hpc : ∀ u : Fin G.numVerts,
      F.fitLevel hd (G.cloudList u).length ≤ pol.eval (G.cloudList u).length)
    (hpe : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges)) :
    ∀ n, (revSum F pol (F.toFamily hd).degree (G.preDeg (F.toFamily hd)) k n
        (pair (encGraph G) (pair (List.replicate v true) (List.replicate s true)))).length
      = ∑ j ∈ Finset.range n,
          (if j < k then (G.preRotNum (F.toFamily hd)
                (G.walkNum (F.toFamily hd) s (k - 1 - j) v)
                ((s / G.preDeg (F.toFamily hd) ^ (k - 1 - j))
                  % G.preDeg (F.toFamily hd))).2
            else (s / G.preDeg (F.toFamily hd) ^ j) % G.preDeg (F.toFamily hd))
            * G.preDeg (F.toFamily hd) ^ j := by
  have hPpos : 0 < G.preDeg (F.toFamily hd) := G.preDeg_pos _
  intro n
  induction n with
  | zero => rw [revSum, Finset.range_zero, Finset.sum_empty, List.length_nil]
  | succ n ih =>
      rw [revSum, List.length_append, ih, Finset.sum_range_succ, length_mulC]
      congr 1
      congr 1
      by_cases h : n < k
      · rw [ite_eq_left h, ite_eq_left h, backFn_eq hd G v s (k - 1 - n) hv hpc hpe,
          List.length_replicate]
      · rw [ite_eq_right h, ite_eq_right h, pairSnd_pair, pairSnd_pair,
          divC_eq (Nat.pow_pos hPpos), List.length_replicate, modC_eq hPpos]
        simp

namespace ConstraintGraph

variable (G : ConstraintGraph α) (E : ExpanderFamily)

/-- The reversed dart's number, for a fixed stopping index. -/
noncomputable def revAtNum (T k v s : ℕ) : ℕ :=
  ∑ j ∈ Finset.range T,
    (if j < k then (G.preRotNum E (G.walkNum E s (k - 1 - j) v)
          ((s / G.preDeg E ^ (k - 1 - j)) % G.preDeg E)).2
      else (s / G.preDeg E ^ j) % G.preDeg E) * G.preDeg E ^ j

omit [Fintype α] in
theorem killedRevNum_eq_revAtNum (T q v s c : ℕ) :
    G.killedRevNum E T q v s c = G.revAtNum E T (stopAtNum T q c) v s := rfl

end ConstraintGraph

/-! ### The powered graph's rotation map -/

/-- The coins of a killed dart. -/
noncomputable def coinsOf (q T : ℕ) (z : List Bool) : List Bool :=
  modC (q ^ T) (pairSnd (pairSnd z))

/-- A killed dart's steps, in the walk's input format. -/
noncomputable def toWalk (q T : ℕ) (z : List Bool) : List Bool :=
  pair (pairFst z)
    (pair (pairFst (pairSnd z))
      (divC (q ^ T) (pairSnd (pairSnd z))))

theorem coinsOf_mem_FP (q T : ℕ) : coinsOf q T ∈ FP :=
  modC_mem_FP (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP) _

theorem toWalk_mem_FP (q T : ℕ) : toWalk q T ∈ FP :=
  Cobham.pairFn_mem_FP Cobham.fstBlock_mem_FP
    (Cobham.pairFn_mem_FP (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP)
      (divC_mem_FP (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP) _))

/-- **The dart a killed walk comes back by**, on `pair (graph) (pair (unary
vertex) (unary dart))`. -/
noncomputable def revNumFn (deg P T q : ℕ) (z : List Bool) : List Bool :=
  selectAt (fun k w => marks (revSum F pol deg P k T (toWalk q T w)))
    (fun w => stopFn q (coinsOf q T) 0 T w) T z

theorem revNumFn_mem_FP (deg P T q : ℕ) : revNumFn F pol deg P T q ∈ FP :=
  selectAt_mem_FP
    (fun k => marks_mem_FP (mem_FP_of_eq
      (mem_FP_comp (toWalk_mem_FP q T) (revSum_mem_FP F pol deg P k T)) fun _ => rfl))
    (stopFn_mem_FP (coinsOf_mem_FP q T) T 0) T

/-- **The powered graph's rotation map**, on `pair (graph) (pair (unary vertex)
(unary dart))`: walk to the end, come back by the reversed labels, and keep the
coins. -/
noncomputable def killedRotFn (deg P T q : ℕ) (z : List Bool) : List Bool :=
  pair
    (selectAt (fun k w => walkFn F pol deg P k (toWalk q T w))
      (fun w => stopFn q (coinsOf q T) 0 T w) T z)
    (marks (mulC (q ^ T) (revNumFn F pol deg P T q z)) ++ coinsOf q T z)

theorem killedRotFn_mem_FP (deg P T q : ℕ) : killedRotFn F pol deg P T q ∈ FP := by
  have hkey : (fun w : List Bool => stopFn q (coinsOf q T) 0 T w) ∈ FP :=
    stopFn_mem_FP (coinsOf_mem_FP q T) T 0
  have hwalk : ∀ k, (fun w : List Bool => walkFn F pol deg P k (toWalk q T w)) ∈ FP :=
    fun k => mem_FP_of_eq (mem_FP_comp (toWalk_mem_FP q T) (walkFn_mem_FP F pol deg P k))
      fun _ => rfl
  have hrev : ∀ k, (fun w : List Bool =>
      marks (revSum F pol deg P k T (toWalk q T w))) ∈ FP :=
    fun k => marks_mem_FP (mem_FP_of_eq
      (mem_FP_comp (toWalk_mem_FP q T) (revSum_mem_FP F pol deg P k T)) fun _ => rfl)
  refine mem_FP_of_eq (Cobham.pairFn_mem_FP (selectAt_mem_FP hwalk hkey T)
    (Cobham.appendFn_mem_FP
      (marks_mem_FP (mulC_mem_FP (selectAt_mem_FP hrev hkey T) (q ^ T)))
      (coinsOf_mem_FP q T))) fun w => ?_
  rw [killedRotFn, revNumFn]

variable {F pol} in
theorem marks_revSum_eq (hd : 1 < F.deg) (G : ConstraintGraph α) (T v s k : ℕ)
    (hv : v < 2 * G.numEdges)
    (hpc : ∀ u : Fin G.numVerts,
      F.fitLevel hd (G.cloudList u).length ≤ pol.eval (G.cloudList u).length)
    (hpe : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges)) :
    marks (revSum F pol (F.toFamily hd).degree (G.preDeg (F.toFamily hd)) k T
        (pair (encGraph G) (pair (List.replicate v true) (List.replicate s true))))
      = List.replicate (G.revAtNum (F.toFamily hd) T k v s) true := by
  rw [marks_eq, length_revSum hd G v s k hv hpc hpe, ConstraintGraph.revAtNum]

variable {F pol} in
/-- **The return-dart algorithm computes the dart the walk comes back by.** -/
theorem revNumFn_eq (hd : 1 < F.deg) (G : ConstraintGraph α) (T q v s c : ℕ)
    (hq : 0 < q) (hv : v < 2 * G.numEdges) (hc : c < q ^ T)
    (hpc : ∀ u : Fin G.numVerts,
      F.fitLevel hd (G.cloudList u).length ≤ pol.eval (G.cloudList u).length)
    (hpe : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges)) :
    revNumFn F pol (F.toFamily hd).degree (G.preDeg (F.toFamily hd)) T q
        (pair (encGraph G) (pair (List.replicate v true)
          (List.replicate (s * q ^ T + c) true)))
      = List.replicate (G.killedRevNum (F.toFamily hd) T q v s c) true := by
  have hqT : 0 < q ^ T := Nat.pow_pos hq
  have hdiv : (s * q ^ T + c) / q ^ T = s := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hqT, Nat.div_eq_of_lt hc, Nat.zero_add]
  have hmod : (s * q ^ T + c) % q ^ T = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  have hco : coinsOf q T (pair (encGraph G) (pair (List.replicate v true)
      (List.replicate (s * q ^ T + c) true))) = List.replicate c true := by
    rw [coinsOf, pairSnd_pair, pairSnd_pair, modC_eq hqT,
      List.length_replicate, hmod]
  have htw : toWalk q T (pair (encGraph G) (pair (List.replicate v true)
      (List.replicate (s * q ^ T + c) true)))
      = pair (encGraph G) (pair (List.replicate v true) (List.replicate s true)) := by
    rw [toWalk, pairFst_pair, pairSnd_pair, pairFst_pair,
      pairSnd_pair, divC_eq hqT, List.length_replicate, hdiv]
  have hstop : stopFn q (coinsOf q T) 0 T (pair (encGraph G) (pair (List.replicate v true)
      (List.replicate (s * q ^ T + c) true))) = List.replicate (stopAtNum T q c) true := by
    rw [stopFn_eq hq hco T 0, ← stopAtNum_eq_stopFromNum]
  have hle : stopAtNum T q c ≤ T := by
    have h : (List.finRange T).findIdx (fun j : Fin T => (c / q ^ j.val) % q == 0)
        ≤ (List.finRange T).length := List.findIdx_le_length
    rwa [List.length_finRange] at h
  rw [revNumFn, selectAt_eq hstop hle, htw, marks_revSum_eq hd G T v s _ hv hpc hpe,
    G.killedRevNum_eq_revAtNum]

variable {F pol} in
/-- **The rotation algorithm runs the powered graph's rotation map.** -/
theorem killedRotFn_eq (hd : 1 < F.deg) (G : ConstraintGraph α) (T q v s c : ℕ)
    (hq : 0 < q) (hv : v < 2 * G.numEdges) (hc : c < q ^ T)
    (hpc : ∀ u : Fin G.numVerts,
      F.fitLevel hd (G.cloudList u).length ≤ pol.eval (G.cloudList u).length)
    (hpe : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges)) :
    killedRotFn F pol (F.toFamily hd).degree (G.preDeg (F.toFamily hd)) T q
        (pair (encGraph G) (pair (List.replicate v true)
          (List.replicate (s * q ^ T + c) true)))
      = pair (List.replicate (G.killedRotNum (F.toFamily hd) T q v s c).1 true)
        (List.replicate (G.killedRotNum (F.toFamily hd) T q v s c).2 true) := by
  have hqT : 0 < q ^ T := Nat.pow_pos hq
  have hdiv : (s * q ^ T + c) / q ^ T = s := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hqT, Nat.div_eq_of_lt hc, Nat.zero_add]
  have hmod : (s * q ^ T + c) % q ^ T = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  have hco : coinsOf q T (pair (encGraph G) (pair (List.replicate v true)
      (List.replicate (s * q ^ T + c) true))) = List.replicate c true := by
    rw [coinsOf, pairSnd_pair, pairSnd_pair, modC_eq hqT,
      List.length_replicate, hmod]
  have htw : toWalk q T (pair (encGraph G) (pair (List.replicate v true)
      (List.replicate (s * q ^ T + c) true)))
      = pair (encGraph G) (pair (List.replicate v true) (List.replicate s true)) := by
    rw [toWalk, pairFst_pair, pairSnd_pair, pairFst_pair,
      pairSnd_pair, divC_eq hqT, List.length_replicate, hdiv]
  have hstop : stopFn q (coinsOf q T) 0 T (pair (encGraph G) (pair (List.replicate v true)
      (List.replicate (s * q ^ T + c) true))) = List.replicate (stopAtNum T q c) true := by
    rw [stopFn_eq hq hco T 0, ← stopAtNum_eq_stopFromNum]
  have hle : stopAtNum T q c ≤ T := by
    have h : (List.finRange T).findIdx (fun j : Fin T => (c / q ^ j.val) % q == 0)
        ≤ (List.finRange T).length := List.findIdx_le_length
    rwa [List.length_finRange] at h
  rw [killedRotFn, revNumFn, selectAt_eq hstop hle, selectAt_eq hstop hle, htw,
    walkFn_eq F pol hd G v s hv hpc hpe, marks_revSum_eq hd G T v s _ hv hpc hpe,
    marks_eq, length_mulC, List.length_replicate, hco, ConstraintGraph.killedRotNum]
  dsimp only
  refine congrArg (pair _) ?_
  rw [← List.replicate_add, G.killedRevNum_eq_revAtNum]

end Complexity
