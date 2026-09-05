/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.AlgKey
public import Complexitylib.Classes.PCP.Internal.AlgKilled

/-!
# Reading an edge's data off the input

The constants of a round — the expander's degree, the walk's length, the killing
rate, how many constraints the alphabet has, how many random strings the tester
uses — are fixed. Given them, an edge number of the composed graph splits by
division into a test, a random string and a read; the test splits into a vertex
and a killed dart; and the killed dart drives the walk, whose parities, codes
and return darts are what the edge's data is made of.

This module writes that out as `FP` functions.

## Main definitions

- `Complexity.Round` — the constants of a round
- `Complexity.keyFn` — the edge's data, as a string

## Main results

- `Complexity.keyFn_mem_FP` — it is an `FP` function
- `Complexity.keyFn_length_le` — of bounded length, whatever the input
- `Complexity.keyFn_eq` — on a real edge it writes that edge's own data
- `Complexity.cubeFn_eq`, `Complexity.codeFn_eq` — so the composed edge's second
  endpoint and its constraint are `FP` functions of the input
-/

@[expose] public section

namespace Complexity

open BooleanAnalysis Tester

/-- The constants of one round of amplification, as an algorithm sees them. -/
structure Round where
  /-- The expander's degree. -/
  deg : ℕ
  /-- The preprocessed system's degree. -/
  P : ℕ
  /-- The walk's length. -/
  T : ℕ
  /-- The killing rate. -/
  q : ℕ
  /-- How many constraints there are on the alphabet. -/
  C : ℕ
  /-- How many random strings the tester has. -/
  cZ : ℕ

namespace Round

variable (r : Round)

/-- How many darts the powered graph has at a vertex. -/
def cD : ℕ := r.P ^ r.T * r.q ^ r.T

/-- How many coin tuples there are. -/
def cQ : ℕ := r.q ^ r.T

end Round

variable (F : FinBase) (pol : Polynomial ℕ) (r : Round)

/-! ### Splitting an edge number -/

/-- The test an edge belongs to. -/
noncomputable def testFn (w : List Bool) : List Bool :=
  divC (r.cZ * 22) (pairSnd w)

/-- The random string it runs on. -/
noncomputable def randFn (w : List Bool) : List Bool :=
  divC 22 (modC (r.cZ * 22) (pairSnd w))

/-- The read it asks for. -/
noncomputable def readFn (w : List Bool) : List Bool := modC 22 (pairSnd w)

/-- The killed dart the test is. -/
noncomputable def dartFn (w : List Bool) : List Bool := modC r.cD (testFn r w)

/-- The vertex it starts at. -/
noncomputable def vertFn (w : List Bool) : List Bool := divC r.cD (testFn r w)

/-- The walk's steps. -/
noncomputable def stepsFn (w : List Bool) : List Bool := divC r.cQ (dartFn r w)

/-- The walk's coins. -/
noncomputable def coinFn (w : List Bool) : List Bool := modC r.cQ (dartFn r w)

/-- The input the walk algorithm reads. -/
noncomputable def walkArg (w : List Bool) : List Bool :=
  pair (pairFst w) (pair (vertFn r w) (stepsFn r w))

/-- The input the killed-walk algorithms read. -/
noncomputable def killArg (w : List Bool) : List Bool :=
  pair (pairFst w) (pair (vertFn r w) (dartFn r w))

theorem testFn_mem_FP : testFn r ∈ FP := divC_mem_FP Cobham.sndBlock_mem_FP _

theorem randFn_mem_FP : randFn r ∈ FP :=
  divC_mem_FP (modC_mem_FP Cobham.sndBlock_mem_FP _) _

theorem readFn_mem_FP : readFn ∈ FP := modC_mem_FP Cobham.sndBlock_mem_FP _

theorem dartFn_mem_FP : dartFn r ∈ FP := modC_mem_FP (testFn_mem_FP r) _

theorem vertFn_mem_FP : vertFn r ∈ FP := divC_mem_FP (testFn_mem_FP r) _

theorem stepsFn_mem_FP : stepsFn r ∈ FP := divC_mem_FP (dartFn_mem_FP r) _

theorem coinFn_mem_FP : coinFn r ∈ FP := modC_mem_FP (dartFn_mem_FP r) _

theorem walkArg_mem_FP : walkArg r ∈ FP :=
  Cobham.pairFn_mem_FP Cobham.fstBlock_mem_FP
    (Cobham.pairFn_mem_FP (vertFn_mem_FP r) (stepsFn_mem_FP r))

theorem killArg_mem_FP : killArg r ∈ FP :=
  Cobham.pairFn_mem_FP Cobham.fstBlock_mem_FP
    (Cobham.pairFn_mem_FP (vertFn_mem_FP r) (dartFn_mem_FP r))

/-! ### The walk's data -/

/-- Where the walk stops. -/
noncomputable def stopBlk (w : List Bool) : List Bool :=
  stopFn r.q (coinsOf r.q r.T) 0 r.T (killArg r w)

theorem stopBlk_mem_FP : stopBlk r ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (killArg_mem_FP r)
    (stopFn_mem_FP (coinsOf_mem_FP r.q r.T) r.T 0)) fun _ => rfl

/-- The parity of the vertex the `i`-th step stands on, and `0` past the end. -/
noncomputable def parDigit (i : ℕ) (w : List Bool) : List Bool :=
  ifLtLen (List.replicate i true) (stopBlk r w)
    (modC 2 (walkFn F pol r.deg r.P i (walkArg r w))) []

theorem parDigit_mem_FP (i : ℕ) : parDigit F pol r i ∈ FP :=
  ifLtLen_mem_FP (constFn_mem_FP _) (stopBlk_mem_FP r)
    (modC_mem_FP (mem_FP_of_eq
      (mem_FP_comp (walkArg_mem_FP r) (walkFn_mem_FP F pol r.deg r.P i)) fun _ => rfl) 2)
    (constFn_mem_FP [])

/-- The code of the constraint the `i`-th step meets, and `0` past the end. -/
noncomputable def codeDigit (i : ℕ) (w : List Bool) : List Bool :=
  ifLtLen (List.replicate i true) (stopBlk r w)
    ((recThd (pairSnd (pairFst w))
      (divC 2 (walkFn F pol r.deg r.P i (walkArg r w))).length).take r.C) []

theorem codeDigit_mem_FP (i : ℕ) : codeDigit F pol r i ∈ FP := by
  have hwalk : (fun w : List Bool => walkFn F pol r.deg r.P i (walkArg r w)) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp (walkArg_mem_FP r) (walkFn_mem_FP F pol r.deg r.P i))
      fun _ => rfl
  have hcode : (fun w : List Bool => recThd (pairSnd (pairFst w))
      (divC 2 (walkFn F pol r.deg r.P i (walkArg r w))).length) ∈ FP :=
    gCodeFn_mem_FP (divC_mem_FP hwalk 2) Cobham.fstBlock_mem_FP
  refine ifLtLen_mem_FP (constFn_mem_FP _) (stopBlk_mem_FP r) ?_ (constFn_mem_FP [])
  have := Cobham.takeLenFn_mem_FP (constFn_mem_FP (List.replicate r.C true)) hcode
  refine mem_FP_of_eq this fun w => ?_
  rw [List.length_replicate]

/-! ### The data as a string -/

/-- **An edge's data**, written out as the seven blocks `packKey` expects. -/
noncomputable def keyFn (w : List Bool) : List Bool :=
  pair (pair (stepsFn r w) (coinFn r w))
    (pair (pair (marks (digitSum 2 (parDigit F pol r) r.T w))
        (marks (digitSum r.C (codeDigit F pol r) r.T w)))
      (pair ((revNumFn F pol r.deg r.P r.T r.q (killArg r w)).take (r.P ^ r.T))
        (pair (randFn r w) (readFn w))))

theorem keyFn_mem_FP : keyFn F pol r ∈ FP := by
  refine Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP (stepsFn_mem_FP r) (coinFn_mem_FP r))
    (Cobham.pairFn_mem_FP
      (Cobham.pairFn_mem_FP (marks_mem_FP (digitSum_mem_FP (parDigit_mem_FP F pol r) r.T))
        (marks_mem_FP (digitSum_mem_FP (codeDigit_mem_FP F pol r) r.T)))
      (Cobham.pairFn_mem_FP ?_ (Cobham.pairFn_mem_FP (randFn_mem_FP r) readFn_mem_FP)))
  have hrev : (fun w : List Bool => revNumFn F pol r.deg r.P r.T r.q (killArg r w)) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp (killArg_mem_FP r)
      (revNumFn_mem_FP F pol r.deg r.P r.T r.q)) fun _ => rfl
  have := Cobham.takeLenFn_mem_FP (constFn_mem_FP (List.replicate (r.P ^ r.T) true)) hrev
  refine mem_FP_of_eq this fun w => ?_
  rw [List.length_replicate]

/-! ### What the blocks read -/

/-- **The blocks split an edge number.** -/
theorem blocks_eq (hD : 0 < r.cD) (hZ : 0 < r.cZ) (g : List Bool) (a b c d : ℕ)
    (hb : b < r.cD) (hc : c < r.cZ) (hd : d < 22) :
    testFn r (pair g (List.replicate (((a * r.cD + b) * r.cZ + c) * 22 + d) true))
        = List.replicate (a * r.cD + b) true
      ∧ vertFn r (pair g (List.replicate (((a * r.cD + b) * r.cZ + c) * 22 + d) true))
        = List.replicate a true
      ∧ dartFn r (pair g (List.replicate (((a * r.cD + b) * r.cZ + c) * 22 + d) true))
        = List.replicate b true
      ∧ randFn r (pair g (List.replicate (((a * r.cD + b) * r.cZ + c) * 22 + d) true))
        = List.replicate c true
      ∧ readFn (pair g (List.replicate (((a * r.cD + b) * r.cZ + c) * 22 + d) true))
        = List.replicate d true := by
  have hre : ((a * r.cD + b) * r.cZ + c) * 22 + d
      = (a * r.cD + b) * (r.cZ * 22) + (c * 22 + d) := by ring
  obtain ⟨h1, h2, h3⟩ := MultiTest.split_mixed (a := a * r.cD + b) hc hd
  rw [← hre] at h1 h2 h3
  have htest : testFn r (pair g (List.replicate (((a * r.cD + b) * r.cZ + c) * 22 + d) true))
      = List.replicate (a * r.cD + b) true := by
    rw [testFn, pairSnd_pair, divC_eq (by positivity), List.length_replicate, h1]
  refine ⟨htest, ?_, ?_, ?_, ?_⟩
  · rw [vertFn, htest, divC_eq hD, List.length_replicate, Nat.add_comm,
      Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hb, Nat.zero_add]
  · rw [dartFn, htest, modC_eq hD, List.length_replicate, Nat.add_comm,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  · rw [randFn, pairSnd_pair, modC_eq (by positivity), List.length_replicate,
      divC_eq (by omega), List.length_replicate, h2]
  · rw [readFn, pairSnd_pair, modC_eq (by omega), List.length_replicate, h3]

/-- **The dart block splits into steps and coins.** -/
theorem steps_coin_eq (hQ : 0 < r.cQ) (w : List Bool) (s t : ℕ) (ht : t < r.cQ)
    (hdart : dartFn r w = List.replicate (s * r.cQ + t) true) :
    stepsFn r w = List.replicate s true ∧ coinFn r w = List.replicate t true := by
  constructor
  · rw [stepsFn, hdart, divC_eq hQ, List.length_replicate, Nat.add_comm,
      Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt ht, Nat.zero_add]
  · rw [coinFn, hdart, modC_eq hQ, List.length_replicate, Nat.add_comm,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

/-- **The walk's input**, once the blocks are known. -/
theorem walkArg_eq {w g : List Bool} {a s : ℕ} (hg : pairFst w = g)
    (hv : vertFn r w = List.replicate a true)
    (hs : stepsFn r w = List.replicate s true) :
    walkArg r w = pair g (pair (List.replicate a true) (List.replicate s true)) := by
  rw [walkArg, hg, hv, hs]

/-- **The killed walk's input**, likewise. -/
theorem killArg_eq {w g : List Bool} {a b : ℕ} (hg : pairFst w = g)
    (hv : vertFn r w = List.replicate a true)
    (hb : dartFn r w = List.replicate b true) :
    killArg r w = pair g (pair (List.replicate a true) (List.replicate b true)) := by
  rw [killArg, hg, hv, hb]

/-! ### The walk, on encoded vertices -/

variable {α : Type} [Fintype α] [DecidableEq α]

variable {F pol} in
/-- **The walk algorithm, run on a dart's own numbers.** -/
theorem walkFn_enc (hd : 1 < F.deg) (G : ConstraintGraph α) {T q : ℕ}
    (v : (G.preprocess (F.toFamily hd)).graph.V)
    (x : (Fin T → (G.preprocess (F.toFamily hd)).graph.D) × (Fin T → Fin q))
    (hpc : ∀ u : Fin G.numVerts,
      F.fitLevel hd (G.cloudList u).length ≤ pol.eval (G.cloudList u).length)
    (hpe : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges))
    (j : ℕ) (hj : j ≤ (G.preprocess (F.toFamily hd)).graph.kLen x) :
    walkFn F pol (F.toFamily hd).degree (G.preDeg (F.toFamily hd)) j
        (pair (encGraph G) (pair (List.replicate (NumEnc.enc v) true)
          (List.replicate (NumEnc.enc x.1) true)))
      = List.replicate (NumEnc.enc ((G.preprocess (F.toFamily hd)).graph.walkAt
          ((G.preprocess (F.toFamily hd)).graph.kLen x) v
          ((G.preprocess (F.toFamily hd)).graph.kWalk x) j)) true := by
  have hv : NumEnc.enc v < 2 * G.numEdges := by
    have h := NumEnc.enc_lt v
    rw [NumEnc.card_eq_fintype_card] at h
    have horder : Fintype.card (G.preprocess (F.toFamily hd)).graph.V = 2 * G.numEdges :=
      G.order_preprocess (F.toFamily hd)
    omega
  have hpos : 0 < G.preDeg (F.toFamily hd) := G.preDeg_pos _
  have hle : (G.preprocess (F.toFamily hd)).graph.kLen x ≤ T :=
    (G.preprocess (F.toFamily hd)).graph.kLen_le x
  have hpre : ∀ (k : ℕ) (hk : k < (G.preprocess (F.toFamily hd)).graph.kLen x),
      (NumEnc.enc x.1 / G.preDeg (F.toFamily hd) ^ k) % G.preDeg (F.toFamily hd)
        = NumEnc.enc ((G.preprocess (F.toFamily hd)).graph.kWalk x ⟨k, hk⟩) := by
    intro k hk
    rw [G.digit_enc (F.toFamily hd) x.1 hpos k (lt_of_lt_of_le hk hle)]
    simp only [RegGraph.kWalk, RegGraph.preWalk]
  refine (walkFn_eq F pol hd G _ _ hv hpc hpe j).trans ?_
  exact congrArg (fun n => List.replicate n true)
    (G.walkNum_eq (F.toFamily hd) v ((G.preprocess (F.toFamily hd)).graph.kWalk x)
      (NumEnc.enc x.1) hpre hj)

variable {F pol} in
/-- **The stopping block is the effective walk's length.** -/
theorem stopBlk_eq (hd : 1 < F.deg) (G : ConstraintGraph α) (hq : 0 < r.q)
    (v : (G.preprocess (F.toFamily hd)).graph.V)
    (x : (Fin r.T → (G.preprocess (F.toFamily hd)).graph.D) × (Fin r.T → Fin r.q))
    {w : List Bool} (hg : pairFst w = encGraph G)
    (hv : vertFn r w = List.replicate (NumEnc.enc v) true)
    (hdart : dartFn r w = List.replicate (NumEnc.enc x) true) :
    stopBlk r w = List.replicate ((G.preprocess (F.toFamily hd)).graph.kLen x) true := by
  have hlt : NumEnc.enc x.2 < r.q ^ r.T := NumEnc.enc_lt x.2
  have hxenc : NumEnc.enc x = NumEnc.enc x.1 * r.q ^ r.T + NumEnc.enc x.2 := rfl
  have hco : coinsOf r.q r.T (killArg r w) = List.replicate (NumEnc.enc x.2) true := by
    rw [killArg_eq r hg hv hdart, coinsOf, pairSnd_pair, pairSnd_pair,
      modC_eq (Nat.pow_pos hq), List.length_replicate, hxenc, Nat.add_comm,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  rw [stopBlk, stopFn_eq hq hco r.T 0, ← stopAtNum_eq_stopFromNum, stopAtNum_eq hq x.2]
  rfl

variable {F pol} in
/-- **The parity block is the parity tuple's number.** -/
theorem parBlk_eq (hd : 1 < F.deg) (G : ConstraintGraph α) (hq : 0 < r.q)
    (hdeg : r.deg = (F.toFamily hd).degree) (hP : r.P = G.preDeg (F.toFamily hd))
    (v : (G.preprocess (F.toFamily hd)).graph.V)
    (x : (Fin r.T → (G.preprocess (F.toFamily hd)).graph.D) × (Fin r.T → Fin r.q))
    {w : List Bool} (hg : pairFst w = encGraph G)
    (hv : vertFn r w = List.replicate (NumEnc.enc v) true)
    (hs : stepsFn r w = List.replicate (NumEnc.enc x.1) true)
    (hdart : dartFn r w = List.replicate (NumEnc.enc x) true)
    (hpc : ∀ u : Fin G.numVerts,
      F.fitLevel hd (G.cloudList u).length ≤ pol.eval (G.cloudList u).length)
    (hpe : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges))
    (B : ℕ) (z : Cube (ROf B)) (i : ReadIdx) :
    marks (digitSum 2 (parDigit F pol r) r.T w)
      = List.replicate (NumEnc.enc (stepKeyOf G (F.toFamily hd) v x B z i).par) true := by
  have hstop := stopBlk_eq r hd G hq v x hg hv hdart
  rw [marks_eq]
  refine congrArg (List.replicate · true) ?_
  refine length_digitSum_eq_enc (X := Fin 2)
    (stepKeyOf G (F.toFamily hd) v x B z i).par _ w fun j hj => ?_
  rw [parDigit, hstop, hdeg, hP]
  by_cases hjk : j < (G.preprocess (F.toFamily hd)).graph.kLen x
  · rw [ifLtLen_pos (by simpa using hjk), walkArg_eq r hg hv hs,
      walkFn_enc hd G v x hpc hpe j (le_of_lt hjk), modC_eq (by omega),
      List.length_replicate, List.length_replicate]
    show _ = NumEnc.enc (StepKey.par _ _)
    rw [stepKeyOf]
    simp only [StepKey.par]
    rw [dite_eq_left hjk]
    rfl
  · rw [ifLtLen_neg (by simpa using hjk), List.length_nil]
    show _ = NumEnc.enc (StepKey.par _ _)
    rw [stepKeyOf]
    simp only [StepKey.par]
    rw [dite_eq_right hjk]
    rfl

omit [Fintype α] [DecidableEq α] in
theorem enc_halfEdge_div_two (G : ConstraintGraph α) (p : G.HalfEdge) :
    NumEnc.enc p / 2 = p.1.val := by
  have hcode : NumEnc.enc p = 2 * p.1.val + (if p.2 then 0 else 1) := by
    rw [ConstraintGraph.enc_halfEdge, ConstraintGraph.halfCode]
  rw [hcode]
  by_cases h : p.2 = true
  · rw [ite_eq_left h]
    omega
  · rw [ite_eq_right h]
    omega

variable {F pol} in
/-- **The code block is the code tuple's number.** -/
theorem codeBlk_eq (hd : 1 < F.deg) (G : ConstraintGraph α) (hq : 0 < r.q)
    (hdeg : r.deg = (F.toFamily hd).degree) (hP : r.P = G.preDeg (F.toFamily hd))
    (hC : r.C = Fintype.card (α → α → Bool))
    (v : (G.preprocess (F.toFamily hd)).graph.V)
    (x : (Fin r.T → (G.preprocess (F.toFamily hd)).graph.D) × (Fin r.T → Fin r.q))
    {w : List Bool} (hg : pairFst w = encGraph G)
    (hv : vertFn r w = List.replicate (NumEnc.enc v) true)
    (hs : stepsFn r w = List.replicate (NumEnc.enc x.1) true)
    (hdart : dartFn r w = List.replicate (NumEnc.enc x) true)
    (hpc : ∀ u : Fin G.numVerts,
      F.fitLevel hd (G.cloudList u).length ≤ pol.eval (G.cloudList u).length)
    (hpe : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges))
    (B : ℕ) (z : Cube (ROf B)) (i : ReadIdx) :
    marks (digitSum r.C (codeDigit F pol r) r.T w)
      = List.replicate (NumEnc.enc (stepKeyOf G (F.toFamily hd) v x B z i).code) true := by
  have hstop := stopBlk_eq r hd G hq v x hg hv hdart
  rw [marks_eq]
  refine congrArg (List.replicate · true) ?_
  rw [hC]
  refine length_digitSum_eq_enc (X := Fin (Fintype.card (α → α → Bool)))
    (stepKeyOf G (F.toFamily hd) v x B z i).code _ w fun j hj => ?_
  rw [codeDigit, hstop, hdeg, hP]
  by_cases hjk : j < (G.preprocess (F.toFamily hd)).graph.kLen x
  · rw [ifLtLen_pos (by simpa using hjk), hg, walkArg_eq r hg hv hs,
      walkFn_enc hd G v x hpc hpe j (le_of_lt hjk), divC_eq (by omega),
      List.length_take]
    simp only [List.length_replicate]
    have henc : NumEnc.enc ((G.preprocess (F.toFamily hd)).graph.walkAt
        ((G.preprocess (F.toFamily hd)).graph.kLen x) v
        ((G.preprocess (F.toFamily hd)).graph.kWalk x) j) < 2 * G.numEdges := by
      have h := NumEnc.enc_lt ((G.preprocess (F.toFamily hd)).graph.walkAt
        ((G.preprocess (F.toFamily hd)).graph.kLen x) v
        ((G.preprocess (F.toFamily hd)).graph.kWalk x) j)
      rw [NumEnc.card_eq_fintype_card] at h
      have horder : Fintype.card (G.preprocess (F.toFamily hd)).graph.V = 2 * G.numEdges :=
        G.order_preprocess (F.toFamily hd)
      omega
    have hidx : NumEnc.enc ((G.preprocess (F.toFamily hd)).graph.walkAt
        ((G.preprocess (F.toFamily hd)).graph.kLen x) v
        ((G.preprocess (F.toFamily hd)).graph.kWalk x) j) / 2 < G.numEdges := by omega
    have hgc := gCode_encGraph G _ hidx
    rw [gCode] at hgc
    rw [hgc]
    have hlt : codeOfRel (G.rel ⟨NumEnc.enc ((G.preprocess (F.toFamily hd)).graph.walkAt
        ((G.preprocess (F.toFamily hd)).graph.kLen x) v
        ((G.preprocess (F.toFamily hd)).graph.kWalk x) j) / 2, hidx⟩) < r.C := by
      rw [hC]
      exact codeOfRel_lt _
    rw [Nat.min_eq_right (le_of_lt hlt)]
    show _ = NumEnc.enc (StepKey.code _ _)
    rw [stepKeyOf]
    simp only [StepKey.code]
    rw [dite_eq_left hjk]
    have hfin : (⟨NumEnc.enc ((G.preprocess (F.toFamily hd)).graph.walkAt
        ((G.preprocess (F.toFamily hd)).graph.kLen x) v
        ((G.preprocess (F.toFamily hd)).graph.kWalk x) j) / 2, hidx⟩ : Fin G.numEdges)
        = ((G.preprocess (F.toFamily hd)).graph.walkAt
          ((G.preprocess (F.toFamily hd)).graph.kLen x) v
          ((G.preprocess (F.toFamily hd)).graph.kWalk x) j).1 :=
      Fin.ext (enc_halfEdge_div_two G _)
    rw [hfin]
    rfl
  · rw [ifLtLen_neg (by simpa using hjk), List.length_nil]
    show _ = NumEnc.enc (StepKey.code _ _)
    rw [stepKeyOf]
    simp only [StepKey.code]
    rw [dite_eq_right hjk]
    rfl

variable {F pol} in
/-- **The return-dart block is the return tuple's number.** -/
theorem revBlk_eq (hd : 1 < F.deg) (G : ConstraintGraph α) (hq : 0 < r.q)
    (hdeg : r.deg = (F.toFamily hd).degree) (hP : r.P = G.preDeg (F.toFamily hd))
    (v : (G.preprocess (F.toFamily hd)).graph.V)
    (x : (Fin r.T → (G.preprocess (F.toFamily hd)).graph.D) × (Fin r.T → Fin r.q))
    {w : List Bool} (hg : pairFst w = encGraph G)
    (hv : vertFn r w = List.replicate (NumEnc.enc v) true)
    (hdart : dartFn r w = List.replicate (NumEnc.enc x) true)
    (hpc : ∀ u : Fin G.numVerts,
      F.fitLevel hd (G.cloudList u).length ≤ pol.eval (G.cloudList u).length)
    (hpe : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges))
    (B : ℕ) (z : Cube (ROf B)) (i : ReadIdx) :
    (revNumFn F pol r.deg r.P r.T r.q (killArg r w)).take (r.P ^ r.T)
      = List.replicate (NumEnc.enc (stepKeyOf G (F.toFamily hd) v x B z i).rev) true := by
  have henc : NumEnc.enc v < 2 * G.numEdges := by
    have h := NumEnc.enc_lt v
    rw [NumEnc.card_eq_fintype_card] at h
    have horder : Fintype.card (G.preprocess (F.toFamily hd)).graph.V = 2 * G.numEdges :=
      G.order_preprocess (F.toFamily hd)
    omega
  have hclt : NumEnc.enc x.2 < r.q ^ r.T := NumEnc.enc_lt x.2
  have hxenc : NumEnc.enc x = NumEnc.enc x.1 * r.q ^ r.T + NumEnc.enc x.2 := rfl
  have hrev : NumEnc.enc ((G.preprocess (F.toFamily hd)).graph.killedRev v x.1 x.2)
      < r.P ^ r.T := by
    have h := NumEnc.enc_lt ((G.preprocess (F.toFamily hd)).graph.killedRev v x.1 x.2)
    have hcard : NumEnc.card (Fin r.T → (G.preprocess (F.toFamily hd)).graph.D)
        = G.preDeg (F.toFamily hd) ^ r.T := rfl
    rw [hcard, ← hP] at h
    exact h
  rw [killArg_eq r hg hv hdart, hdeg, hP, hxenc,
    revNumFn_eq hd G r.T r.q (NumEnc.enc v) (NumEnc.enc x.1) (NumEnc.enc x.2) hq henc
      hclt hpc hpe]
  have hknum : G.killedRevNum (F.toFamily hd) r.T r.q (NumEnc.enc v) (NumEnc.enc x.1)
      (NumEnc.enc x.2)
      = NumEnc.enc ((G.preprocess (F.toFamily hd)).graph.killedRev v x.1 x.2) :=
    G.killedRevNum_eq (F.toFamily hd) hq (G.preDeg_pos _) v x.1 x.2
  rw [hknum, List.take_replicate]
  show List.replicate _ true = List.replicate (NumEnc.enc (StepKey.rev _)) true
  rw [stepKeyOf]
  simp only [StepKey.rev]
  rw [← hP, Nat.min_eq_right (le_of_lt hrev)]
  rfl

variable {F pol} in
/-- **The algorithm writes out the walk's own data.** -/
theorem keyFn_eq (hd : 1 < F.deg) (G : ConstraintGraph α) (hq : 0 < r.q)
    (hdeg : r.deg = (F.toFamily hd).degree) (hP : r.P = G.preDeg (F.toFamily hd))
    (hC : r.C = Fintype.card (α → α → Bool)) (hZ : 0 < r.cZ)
    (v : (G.preprocess (F.toFamily hd)).graph.V)
    (x : (Fin r.T → (G.preprocess (F.toFamily hd)).graph.D) × (Fin r.T → Fin r.q))
    {B : ℕ} (z : Cube (ROf B)) (i : ReadIdx)
    (hcZ : r.cZ = NumEnc.card (Cube (ROf B)))
    (hpc : ∀ u : Fin G.numVerts,
      F.fitLevel hd (G.cloudList u).length ≤ pol.eval (G.cloudList u).length)
    (hpe : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges)) :
    keyFn F pol r (pair (encGraph G) (List.replicate
        (((NumEnc.enc v * r.cD + NumEnc.enc x) * r.cZ + NumEnc.enc z) * 22 + NumEnc.enc i) true))
      = packKey (stepKeyOf G (F.toFamily hd) v x B z i) := by
  have hxlt : NumEnc.enc x < r.cD := by
    have h := NumEnc.enc_lt x
    have hcard : NumEnc.card ((Fin r.T → (G.preprocess (F.toFamily hd)).graph.D)
        × (Fin r.T → Fin r.q)) = G.preDeg (F.toFamily hd) ^ r.T * r.q ^ r.T := rfl
    rw [hcard] at h
    rw [Round.cD, hP]
    exact h
  have hzlt : NumEnc.enc z < r.cZ := by rw [hcZ]; exact NumEnc.enc_lt z
  have hilt : NumEnc.enc i < 22 := NumEnc.enc_lt i
  obtain ⟨-, hv, hdart, hrand, hread⟩ :=
    blocks_eq r (by
      rw [Round.cD, hP]
      exact Nat.mul_pos (Nat.pow_pos (G.preDeg_pos _)) (Nat.pow_pos hq)) hZ (encGraph G)
      (NumEnc.enc v) (NumEnc.enc x) (NumEnc.enc z) (NumEnc.enc i) hxlt hzlt hilt
  have hclt : NumEnc.enc x.2 < r.cQ := NumEnc.enc_lt x.2
  have hxenc : NumEnc.enc x = NumEnc.enc x.1 * r.cQ + NumEnc.enc x.2 := rfl
  obtain ⟨hs, hc⟩ := steps_coin_eq r (Nat.pow_pos hq) _ (NumEnc.enc x.1)
    (NumEnc.enc x.2) hclt (by rw [hdart, hxenc])
  have hg : pairFst (pair (encGraph G) (List.replicate
      (((NumEnc.enc v * r.cD + NumEnc.enc x) * r.cZ + NumEnc.enc z) * 22 + NumEnc.enc i) true))
      = encGraph G := pairFst_pair _ _
  rw [keyFn, hs, hc, hrand, hread,
    parBlk_eq r hd G hq hdeg hP v x hg hv hs hdart hpc hpe B z i,
    codeBlk_eq r hd G hq hdeg hP hC v x hg hv hs hdart hpc hpe B z i,
    revBlk_eq r hd G hq hdeg hP v x hg hv hdart hpc hpe B z i, packKey]
  rfl

/-- A bound on the length of an edge's data. -/
def keyBound : ℕ :=
  2 * (2 * r.cD + 2 + r.cQ) + 2
    + (2 * (2 * (r.T * (1 * 2 ^ r.T)) + 2 + r.T * (r.C * r.C ^ r.T)) + 2
      + (2 * r.P ^ r.T + 2 + (2 * r.cZ + 2 + 22)))

theorem keyFn_length_le (hQ : 0 < r.cQ) (hD : 0 < r.cD) (hZ : 0 < r.cZ) (hC : 0 < r.C)
    (w : List Bool) :
    (keyFn F pol r w).length ≤ keyBound r := by
  have hdart : (dartFn r w).length < r.cD := by
    rw [dartFn, modC_eq hD, List.length_replicate]
    exact Nat.mod_lt _ hD
  have hsteps : (stepsFn r w).length ≤ r.cD := by
    rw [stepsFn, divC_eq hQ, List.length_replicate]
    exact le_trans (Nat.div_le_self _ _) (le_of_lt hdart)
  have hcoin : (coinFn r w).length < r.cQ := by
    rw [coinFn, modC_eq hQ, List.length_replicate]
    exact Nat.mod_lt _ hQ
  have hrand : (randFn r w).length ≤ r.cZ := by
    rw [randFn, divC_eq (by omega), List.length_replicate, modC_eq (by positivity),
      List.length_replicate]
    have hlt : (pairSnd w).length % (r.cZ * 22) < r.cZ * 22 :=
      Nat.mod_lt _ (by positivity)
    exact Nat.div_le_of_le_mul (by omega)
  have hread : (readFn w).length ≤ 22 := by
    rw [readFn, modC_eq (by omega), List.length_replicate]
    exact le_of_lt (Nat.mod_lt _ (by omega))
  have hpar : (digitSum 2 (parDigit F pol r) r.T w).length ≤ r.T * (1 * 2 ^ r.T) := by
    refine length_digitSum_le (by omega) (fun j u => ?_) r.T w
    rw [parDigit]
    by_cases h : (List.replicate j true).length < (stopBlk r u).length
    · rw [ifLtLen_pos h, modC_eq (by omega), List.length_replicate]
      omega
    · rw [ifLtLen_neg h]
      simp
  have hcode : (digitSum r.C (codeDigit F pol r) r.T w).length ≤ r.T * (r.C * r.C ^ r.T) := by
    refine length_digitSum_le hC (fun j u => ?_) r.T w
    rw [codeDigit]
    by_cases h : (List.replicate j true).length < (stopBlk r u).length
    · rw [ifLtLen_pos h]
      exact le_trans (List.length_take_le _ _) (by simp)
    · rw [ifLtLen_neg h]
      simp
  have hrevb : ((revNumFn F pol r.deg r.P r.T r.q (killArg r w)).take (r.P ^ r.T)).length
      ≤ r.P ^ r.T := by
    exact le_trans (List.length_take_le _ _) (by simp)
  rw [keyFn, keyBound]
  simp only [pair_length, marks_eq, List.length_replicate]
  omega

/-! ### The cube and the code, in polynomial time -/

variable {E : ExpanderFamily} {B : ℕ}

/-- The cube a composed edge's second endpoint names. -/
noncomputable def cubeFn
    (dflt : StepKey E r.T r.q B (Fintype.card (α → α → Bool)))
    (encβ : (PreWalk E r.T → α) → Cube B) (w : List Bool) : List Bool :=
  List.replicate (cubeOfKey encβ (keyOfString dflt (keyFn F pol r w))) true

/-- The code of a composed edge's constraint. -/
noncomputable def codeFn
    (dflt : StepKey E r.T r.q B (Fintype.card (α → α → Bool)))
    (encβ : (PreWalk E r.T → α) → Cube B) (w : List Bool) : List Bool :=
  List.replicate (codeOfKey encβ (keyOfString dflt (keyFn F pol r w))) true

theorem cubeFn_mem_FP (hQ : 0 < r.cQ) (hD : 0 < r.cD) (hZ : 0 < r.cZ) (hC : 0 < r.C)
    (dflt : StepKey E r.T r.q B (Fintype.card (α → α → Bool)))
    (encβ : (PreWalk E r.T → α) → Cube B) : cubeFn F pol r dflt encβ ∈ FP :=
  mem_FP_of_bounded_key (keyFn_mem_FP F pol r) (keyFn_length_le F pol r hQ hD hZ hC)
    (fun s => List.replicate (cubeOfKey encβ (keyOfString dflt s)) true)

theorem codeFn_mem_FP (hQ : 0 < r.cQ) (hD : 0 < r.cD) (hZ : 0 < r.cZ) (hC : 0 < r.C)
    (dflt : StepKey E r.T r.q B (Fintype.card (α → α → Bool)))
    (encβ : (PreWalk E r.T → α) → Cube B) : codeFn F pol r dflt encβ ∈ FP :=
  mem_FP_of_bounded_key (keyFn_mem_FP F pol r) (keyFn_length_le F pol r hQ hD hZ hC)
    (fun s => List.replicate (codeOfKey encβ (keyOfString dflt s)) true)

variable {F pol} in
/-- **The cube algorithm computes the composed edge's cube.** -/
theorem cubeFn_eq (hd : 1 < F.deg) (G : ConstraintGraph α) (hq : 0 < r.q)
    (hdeg : r.deg = (F.toFamily hd).degree) (hP : r.P = G.preDeg (F.toFamily hd))
    (hC : r.C = Fintype.card (α → α → Bool)) (hZ : 0 < r.cZ)
    (v : (G.preprocess (F.toFamily hd)).graph.V)
    (x : (Fin r.T → (G.preprocess (F.toFamily hd)).graph.D) × (Fin r.T → Fin r.q))
    (z : Cube (ROf B)) (i : ReadIdx)
    (hcZ : r.cZ = NumEnc.card (Cube (ROf B)))
    (hpc : ∀ u : Fin G.numVerts,
      F.fitLevel hd (G.cloudList u).length ≤ pol.eval (G.cloudList u).length)
    (hpe : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges))
    (dflt : StepKey (F.toFamily hd) r.T r.q B (Fintype.card (α → α → Bool)))
    (encβ : (PreWalk (F.toFamily hd) r.T → α) → Cube B) :
    cubeFn F pol r dflt encβ (pair (encGraph G) (List.replicate
        (((NumEnc.enc v * r.cD + NumEnc.enc x) * r.cZ + NumEnc.enc z) * 22 + NumEnc.enc i) true))
      = List.replicate (((G.preprocess (F.toFamily hd)).killedPow r.q r.T hq).cubeNum
          encβ (v, x) z i) true := by
  rw [cubeFn, keyFn_eq r hd G hq hdeg hP hC hZ v x z i hcZ hpc hpe, keyOfString_packKey,
    cubeOfKey_eq G (F.toFamily hd) hq v x z i encβ]

variable {F pol} in
/-- **The cube algorithm**, with the dart given as one object. -/
theorem cubeFn_eq' (hd : 1 < F.deg) (G : ConstraintGraph α) (hq : 0 < r.q)
    (hdeg : r.deg = (F.toFamily hd).degree) (hP : r.P = G.preDeg (F.toFamily hd))
    (hC : r.C = Fintype.card (α → α → Bool)) (hZ : 0 < r.cZ)
    (p : ((G.preprocess (F.toFamily hd)).killedPow r.q r.T hq).Dart)
    (z : Cube (ROf B)) (i : ReadIdx)
    (hcZ : r.cZ = NumEnc.card (Cube (ROf B)))
    (hpc : ∀ u : Fin G.numVerts,
      F.fitLevel hd (G.cloudList u).length ≤ pol.eval (G.cloudList u).length)
    (hpe : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges))
    (dflt : StepKey (F.toFamily hd) r.T r.q B (Fintype.card (α → α → Bool)))
    (encβ : (PreWalk (F.toFamily hd) r.T → α) → Cube B) :
    cubeFn F pol r dflt encβ (pair (encGraph G) (List.replicate
        (((NumEnc.enc p.1 * r.cD + NumEnc.enc p.2) * r.cZ + NumEnc.enc z) * 22
          + NumEnc.enc i) true))
      = List.replicate (((G.preprocess (F.toFamily hd)).killedPow r.q r.T hq).cubeNum
          encβ p z i) true := by
  obtain ⟨v, x⟩ := p
  exact cubeFn_eq r hd G hq hdeg hP hC hZ v x z i hcZ hpc hpe dflt encβ

variable {F pol} in
/-- **The code algorithm computes the composed edge's constraint.** -/
theorem codeFn_eq (hd : 1 < F.deg) (G : ConstraintGraph α) (hq : 0 < r.q)
    (hdeg : r.deg = (F.toFamily hd).degree) (hP : r.P = G.preDeg (F.toFamily hd))
    (hC : r.C = Fintype.card (α → α → Bool)) (hZ : 0 < r.cZ)
    (v : (G.preprocess (F.toFamily hd)).graph.V)
    (x : (Fin r.T → (G.preprocess (F.toFamily hd)).graph.D) × (Fin r.T → Fin r.q))
    (z : Cube (ROf B)) (i : ReadIdx)
    (hcZ : r.cZ = NumEnc.card (Cube (ROf B)))
    (hpc : ∀ u : Fin G.numVerts,
      F.fitLevel hd (G.cloudList u).length ≤ pol.eval (G.cloudList u).length)
    (hpe : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges))
    (dflt : StepKey (F.toFamily hd) r.T r.q B (Fintype.card (α → α → Bool)))
    (encβ : (PreWalk (F.toFamily hd) r.T → α) → Cube B) :
    codeFn F pol r dflt encβ (pair (encGraph G) (List.replicate
        (((NumEnc.enc v * r.cD + NumEnc.enc x) * r.cZ + NumEnc.enc z) * 22 + NumEnc.enc i) true))
      = List.replicate (codeOfRel (MultiTest.relOfCheck
          ((((G.preprocess (F.toFamily hd)).killedPow r.q r.T hq).compose encβ).check (v, x) z)
          i)) true := by
  rw [codeFn, keyFn_eq r hd G hq hdeg hP hC hZ v x z i hcZ hpc hpe, keyOfString_packKey,
    codeOfKey_eq G (F.toFamily hd) hq v x z i encβ]

variable {F pol} in
/-- **The code algorithm**, with the dart given as one object. -/
theorem codeFn_eq' (hd : 1 < F.deg) (G : ConstraintGraph α) (hq : 0 < r.q)
    (hdeg : r.deg = (F.toFamily hd).degree) (hP : r.P = G.preDeg (F.toFamily hd))
    (hC : r.C = Fintype.card (α → α → Bool)) (hZ : 0 < r.cZ)
    (p : ((G.preprocess (F.toFamily hd)).killedPow r.q r.T hq).Dart)
    (z : Cube (ROf B)) (i : ReadIdx)
    (hcZ : r.cZ = NumEnc.card (Cube (ROf B)))
    (hpc : ∀ u : Fin G.numVerts,
      F.fitLevel hd (G.cloudList u).length ≤ pol.eval (G.cloudList u).length)
    (hpe : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges))
    (dflt : StepKey (F.toFamily hd) r.T r.q B (Fintype.card (α → α → Bool)))
    (encβ : (PreWalk (F.toFamily hd) r.T → α) → Cube B) :
    codeFn F pol r dflt encβ (pair (encGraph G) (List.replicate
        (((NumEnc.enc p.1 * r.cD + NumEnc.enc p.2) * r.cZ + NumEnc.enc z) * 22
          + NumEnc.enc i) true))
      = List.replicate (codeOfRel (MultiTest.relOfCheck
          ((((G.preprocess (F.toFamily hd)).killedPow r.q r.T hq).compose encβ).check p z)
          i)) true := by
  obtain ⟨v, x⟩ := p
  exact codeFn_eq r hd G hq hdeg hP hC hZ v x z i hcZ hpc hpe dflt encβ

end Complexity
