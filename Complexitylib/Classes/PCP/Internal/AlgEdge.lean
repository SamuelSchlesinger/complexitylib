/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.AlgKeyFn
public import Complexitylib.Classes.PCP.Internal.AlgPosNum

/-!
# A composed edge's record

An edge of the composed graph carries three numbers: its two endpoints and the
code of its constraint. The first endpoint is arithmetic in the edge number; the
second is a position, laid out by kind — an encoding block, a linear table or a
quadratic one — and the third is the code the tester's verdict names.

This module writes the position's layout out as an algorithm.

## Main definitions

- `Complexity.posBlk` — a position's number, from its kind, block and cube
- `Complexity.tailBlk` — an edge's first endpoint
- `Complexity.kindBlk`, `Complexity.blockBlk` — which kind of block the second
  endpoint lies in, and which block
- `Complexity.headBlk` — the second endpoint itself
- `Complexity.edgeRule`, `Complexity.stepFn` — one edge's record, and the graph
  a round produces

## Main results

- `Complexity.posBlk_eq` — it is `RegCSP.posNum`
- `Complexity.posBlk_mem_FP` — and it is computed in polynomial time
- `Complexity.tailBlk_eq`, `Complexity.tailBlk_mem_FP` — likewise for the first
  endpoint
-/

@[expose] public section

namespace Complexity

open BooleanAnalysis Tester

/-- A position's number, from its kind, the block it lies in and the cube inside
that block. Kind `0` is an encoding block, kind `1` a dart's linear table, and
anything else a dart's quadratic table. -/
noncomputable def posBlk (cardB cardN cardNN cardD : ℕ)
    (cardV kind block cube : List Bool) : List Bool :=
  ifEqLen kind [] (marks (mulC cardB block) ++ cube)
    (ifEqLen kind [true]
      (marks (mulC cardB cardV) ++ (marks (mulC cardN block) ++ cube))
      (marks (mulC cardB cardV)
        ++ (marks (mulC (cardD * cardN) cardV) ++ (marks (mulC cardNN block) ++ cube))))

/-- **The layout computes the position's number.** -/
theorem posBlk_eq (cardB cardN cardNN cardD k b c : ℕ) (cardV kind block cube : List Bool)
    (hk : kind.length = k) (hb : block.length = b) (hc : cube = List.replicate c true) :
    posBlk cardB cardN cardNN cardD cardV kind block cube
      = List.replicate (RegCSP.posNum cardV.length cardD cardB cardN cardNN k b c) true := by
  have happ : ∀ m n : ℕ, List.replicate m true ++ List.replicate n true
      = List.replicate (m + n) true := fun m n => (List.replicate_add m n true).symm
  rw [posBlk, RegCSP.posNum]
  by_cases h0 : k = 0
  · rw [ifEqLen_pos (by simp [hk, h0]), ite_eq_left h0, marks_eq, length_mulC, hb, hc, happ]
  rw [ifEqLen_neg (by simp [hk, h0]), ite_eq_right h0]
  by_cases h1 : k = 1
  · rw [ifEqLen_pos (by simp [hk, h1]), ite_eq_left h1, marks_eq, marks_eq, length_mulC,
      length_mulC, hb, hc, happ, happ]
  rw [ifEqLen_neg (by simp [hk, h1]), ite_eq_right h1, marks_eq, marks_eq, marks_eq,
    length_mulC, length_mulC, length_mulC, hb, hc, happ, happ, happ]
  congr 2
  ring

theorem posBlk_mem_FP {cardB cardN cardNN cardD : ℕ}
    {cardV kind block cube : List Bool → List Bool}
    (hV : cardV ∈ FP) (hk : kind ∈ FP) (hb : block ∈ FP) (hc : cube ∈ FP) :
    (fun w => posBlk cardB cardN cardNN cardD (cardV w) (kind w) (block w) (cube w)) ∈ FP := by
  have hbb := marks_mem_FP (mulC_mem_FP hb cardB)
  have hVB := marks_mem_FP (mulC_mem_FP hV cardB)
  have hNb := marks_mem_FP (mulC_mem_FP hb cardN)
  have hNV := marks_mem_FP (mulC_mem_FP hV (cardD * cardN))
  have hNNb := marks_mem_FP (mulC_mem_FP hb cardNN)
  exact ifEqLen_mem_FP hk (constFn_mem_FP []) (Cobham.appendFn_mem_FP hbb hc)
    (ifEqLen_mem_FP hk (constFn_mem_FP [true])
      (Cobham.appendFn_mem_FP hVB (Cobham.appendFn_mem_FP hNb hc))
      (Cobham.appendFn_mem_FP hVB
        (Cobham.appendFn_mem_FP hNV (Cobham.appendFn_mem_FP hNNb hc))))

/-! ### The first endpoint -/

variable {α : Type} [Fintype α] [DecidableEq α]

/-- An edge's first endpoint: the test vertex it belongs to, after all the
positions. -/
noncomputable def tailBlk (posF : ℕ) (r : Round) (w : List Bool) : List Bool :=
  marks (mulC posF (posCount (pairSnd (pairFst w))))
    ++ (marks (mulC r.cZ (testFn r w)) ++ randFn r w)

theorem tailBlk_mem_FP (posF : ℕ) (r : Round) : tailBlk posF r ∈ FP :=
  Cobham.appendFn_mem_FP
    (marks_mem_FP (mulC_mem_FP (posCount_mem_FP
      (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP)) posF))
    (Cobham.appendFn_mem_FP (marks_mem_FP (mulC_mem_FP (testFn_mem_FP r) r.cZ))
      (randFn_mem_FP r))

/-- **The first endpoint's algorithm computes it.** -/
theorem tailBlk_eq (posF : ℕ) (r : Round) (G : ConstraintGraph α) {w : List Bool} {t zN : ℕ}
    (hg : pairFst w = encGraph G) (ht : testFn r w = List.replicate t true)
    (hz : randFn r w = List.replicate zN true) :
    tailBlk posF r w = List.replicate (G.numEdges * posF + (t * r.cZ + zN)) true := by
  have hcnt : (posCount (pairSnd (encGraph G))).length = G.numEdges := by
    have h := gEdges_encGraph G
    rwa [gEdges] at h
  rw [tailBlk, hg, ht, hz, marks_eq, marks_eq, length_mulC, length_mulC, hcnt,
    List.length_replicate, ← List.replicate_add, ← List.replicate_add]

/-! ### Which block the second endpoint lies in -/

theorem readFn_length_le (w : List Bool) : (readFn w).length ≤ 22 := by
  rw [readFn, modC_eq (by omega), List.length_replicate]
  exact le_of_lt (Nat.mod_lt _ (by omega))

/-- The kind of block a read lands in. -/
noncomputable def kindBlk (w : List Bool) : List Bool :=
  List.replicate (RegCSP.readKind (decOr ReadIdx.f1x (readFn w).length)) true

theorem kindBlk_mem_FP : kindBlk ∈ FP :=
  mem_FP_of_bounded_key readFn_mem_FP readFn_length_le
    (fun s => List.replicate (RegCSP.readKind (decOr ReadIdx.f1x s.length)) true)

/-- **The kind is the read's.** -/
theorem kindBlk_eq {w : List Bool} {i : ReadIdx} (hi : readFn w = List.replicate
    (NumEnc.enc i) true) :
    kindBlk w = List.replicate (RegCSP.readKind i) true := by
  rw [kindBlk, hi, List.length_replicate, decOr_enc]

/-- The block the second endpoint lies in: the dart's tail for the first input
read, its head for the second, and the dart itself otherwise. -/
noncomputable def blockBlk (F : FinBase) (pol : Polynomial ℕ) (r : Round) (w : List Bool) :
    List Bool :=
  ifEqLen (readFn w) (List.replicate (NumEnc.enc ReadIdx.i5r) true) (vertFn r w)
    (ifEqLen (readFn w) (List.replicate (NumEnc.enc ReadIdx.i6r) true)
      (pairFst (killedRotFn F pol r.deg r.P r.T r.q (killArg r w)))
      (testFn r w))

theorem blockBlk_mem_FP (F : FinBase) (pol : Polynomial ℕ) (r : Round) :
    blockBlk F pol r ∈ FP := by
  have hrot : (fun w : List Bool =>
      pairFst (killedRotFn F pol r.deg r.P r.T r.q (killArg r w))) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp (killArg_mem_FP r)
      (mem_FP_comp (killedRotFn_mem_FP F pol r.deg r.P r.T r.q) Cobham.fstBlock_mem_FP))
      fun _ => rfl
  exact ifEqLen_mem_FP readFn_mem_FP (constFn_mem_FP _) (vertFn_mem_FP r)
    (ifEqLen_mem_FP readFn_mem_FP (constFn_mem_FP _) hrot (testFn_mem_FP r))

/-- **The block is the one the read asks for.** -/
-- The signature mirrors the family this belongs to; the argument is part of
-- that shape even where this member does not consult it.
@[nolint unusedArguments]
theorem blockBlk_eq {β : Type} [Fintype β] [DecidableEq β] [Nonempty β] {R : RegCSP β}
    [NumEnc R.graph.V] [NumEnc R.graph.D] (F : FinBase) (pol : Polynomial ℕ) (r : Round)
    {w : List Bool} (p : R.Dart) (i : ReadIdx)
    (hread : readFn w = List.replicate (NumEnc.enc i) true)
    (hv : vertFn r w = List.replicate (NumEnc.enc p.1) true)
    (ht : testFn r w = List.replicate (NumEnc.enc p) true)
    (hrot : pairFst (killedRotFn F pol r.deg r.P r.T r.q (killArg r w))
      = List.replicate (NumEnc.enc (R.graph.rot p).1) true) :
    blockBlk F pol r w = List.replicate (R.blockNum p i) true := by
  have hne : ∀ j k : ReadIdx, j ≠ k → NumEnc.enc j ≠ NumEnc.enc k :=
    fun j k h hcon => h (NumEnc.enc_injective hcon)
  rw [blockBlk, hread]
  rcases eq_or_ne i ReadIdx.i5r with rfl | h5
  · rw [ifEqLen_pos (by simp), hv, RegCSP.blockNum]
  rw [ifEqLen_neg (by simpa using hne i ReadIdx.i5r h5)]
  rcases eq_or_ne i ReadIdx.i6r with rfl | h6
  · rw [ifEqLen_pos (by simp), hrot, RegCSP.blockNum]
    rfl
  rw [ifEqLen_neg (by simpa using hne i ReadIdx.i6r h6), ht]
  cases i <;> first | rfl | exact absurd rfl h5 | exact absurd rfl h6

/-! ### The second endpoint -/

/-- How many vertices the powered graph has: twice the input's edge count. -/
noncomputable def vertCount (w : List Bool) : List Bool :=
  marks (mulC 2 (posCount (pairSnd (pairFst w))))

theorem vertCount_mem_FP : vertCount ∈ FP :=
  marks_mem_FP (mulC_mem_FP (posCount_mem_FP
    (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP)) 2)

theorem vertCount_eq (G : ConstraintGraph α) {w : List Bool}
    (hg : pairFst w = encGraph G) :
    vertCount w = List.replicate (2 * G.numEdges) true := by
  have hcnt : (posCount (pairSnd (encGraph G))).length = G.numEdges := by
    have h := gEdges_encGraph G
    rwa [gEdges] at h
  rw [vertCount, hg, marks_eq, length_mulC, hcnt, Nat.mul_comm]

/-- An edge's second endpoint. -/
noncomputable def headBlk (F : FinBase) (pol : Polynomial ℕ) (r : Round)
    (cardB cardN cardNN : ℕ) {E : ExpanderFamily} {B : ℕ}
    (dflt : StepKey E r.T r.q B (Fintype.card (α → α → Bool)))
    (encβ : (PreWalk E r.T → α) → Cube B) (w : List Bool) : List Bool :=
  posBlk cardB cardN cardNN r.cD (vertCount w) (kindBlk w) (blockBlk F pol r w)
    (cubeFn F pol r dflt encβ w)

theorem headBlk_mem_FP (F : FinBase) (pol : Polynomial ℕ) (r : Round)
    (cardB cardN cardNN : ℕ) {E : ExpanderFamily} {B : ℕ}
    (hQ : 0 < r.cQ) (hD : 0 < r.cD) (hZ : 0 < r.cZ) (hC : 0 < r.C)
    (dflt : StepKey E r.T r.q B (Fintype.card (α → α → Bool)))
    (encβ : (PreWalk E r.T → α) → Cube B) :
    headBlk F pol r cardB cardN cardNN dflt encβ ∈ FP :=
  posBlk_mem_FP vertCount_mem_FP kindBlk_mem_FP (blockBlk_mem_FP F pol r)
    (cubeFn_mem_FP F pol r hQ hD hZ hC dflt encβ)

/-- **The second endpoint's algorithm computes its number.** -/
theorem headBlk_eq (F : FinBase) (pol : Polynomial ℕ) (r : Round)
    (cardB cardN cardNN : ℕ) {E : ExpanderFamily} {B : ℕ}
    (dflt : StepKey E r.T r.q B (Fintype.card (α → α → Bool)))
    (encβ : (PreWalk E r.T → α) → Cube B) {w : List Bool} {V k b c : ℕ}
    (hV : vertCount w = List.replicate V true)
    (hk : kindBlk w = List.replicate k true)
    (hb : blockBlk F pol r w = List.replicate b true)
    (hc : cubeFn F pol r dflt encβ w = List.replicate c true) :
    headBlk F pol r cardB cardN cardNN dflt encβ w
      = List.replicate (RegCSP.posNum V r.cD cardB cardN cardNN k b c) true := by
  have hVlen : (vertCount w).length = V := by rw [hV, List.length_replicate]
  rw [headBlk, posBlk_eq cardB cardN cardNN r.cD k b c _ _ _ _
    (by rw [hk, List.length_replicate]) (by rw [hb, List.length_replicate]) hc, hVlen]

/-! ### The label encoding, without the graph -/

theorem card_preDart (E : ExpanderFamily) : Fintype.card (PreDart E) = Dinur.powDeg E := by
  show Fintype.card (Unit ⊕ (Option (Fin E.degree) ⊕ Fin E.degree)) = _
  rw [Dinur.powDeg]
  simp
  omega

theorem card_preWalk (E : ExpanderFamily) (T : ℕ) :
    Fintype.card (PreWalk E T) = Dinur.walkCount E T := by
  rw [Dinur.walkCount, ← Fin.sum_univ_eq_sum_range (fun ℓ => Dinur.powDeg E ^ ℓ) (T + 1)]
  show Fintype.card (Σ ℓ : Fin (T + 1), Fin ℓ.val → PreDart E) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Fintype.card_fun, Fintype.card_fin, card_preDart]

theorem card_preOpinion (E : ExpanderFamily) (T : ℕ) :
    Fintype.card (PreWalk E T → DinurAlpha) = Dinur.bits E T := by
  rw [Fintype.card_fun, card_preWalk, Dinur.bits]

/-- **The encoding of a powered label**, at a type that does not mention the
graph. -/
noncomputable def encPre (E : ExpanderFamily) (T : ℕ) (σ : PreWalk E T → DinurAlpha) :
    Cube (Dinur.bits E T) :=
  basisVec (Fin.cast (card_preOpinion E T) (Fintype.equivFin _ σ))

/-- **It is the encoding the round uses.** -/
theorem enc_eq_encPre (E : ExpanderFamily) (G : ConstraintGraph DinurAlpha) (T : ℕ) :
    Dinur.enc E G T = encPre E T := rfl

/-! ### The round's constants -/

/-- The constants of a Dinur round at killing rate `q`, over the expander family
a finite base generates. The alphabet's constraint count and the tester's string
count are supplied, so that they carry the caller's own instances. -/
noncomputable def dinurRound (F : FinBase) (hd : 1 < F.deg) (q C cZ : ℕ) : Round where
  deg := (F.toFamily hd).degree
  P := 2 + 2 * (F.toFamily hd).degree
  T := powT Dinur.K q
  q := q
  C := C
  cZ := cZ

@[simp] theorem dinurRound_deg (F : FinBase) (hd : 1 < F.deg) (q C cZ : ℕ) :
    (dinurRound F hd q C cZ).deg = (F.toFamily hd).degree := rfl

theorem dinurRound_P (F : FinBase) (hd : 1 < F.deg) (q C cZ : ℕ)
    (G : ConstraintGraph DinurAlpha) :
    (dinurRound F hd q C cZ).P = G.preDeg (F.toFamily hd) :=
  (G.preDeg_eq (F.toFamily hd)).symm

@[simp] theorem dinurRound_T (F : FinBase) (hd : 1 < F.deg) (q C cZ : ℕ) :
    (dinurRound F hd q C cZ).T = powT Dinur.K q := rfl

@[simp] theorem dinurRound_q (F : FinBase) (hd : 1 < F.deg) (q C cZ : ℕ) :
    (dinurRound F hd q C cZ).q = q := rfl

@[simp] theorem dinurRound_C (F : FinBase) (hd : 1 < F.deg) (q C cZ : ℕ) :
    (dinurRound F hd q C cZ).C = C := rfl

@[simp] theorem dinurRound_cZ (F : FinBase) (hd : 1 < F.deg) (q C cZ : ℕ) :
    (dinurRound F hd q C cZ).cZ = cZ := rfl

@[simp] theorem dinurRound_cQ (F : FinBase) (hd : 1 < F.deg) (q C cZ : ℕ) :
    (dinurRound F hd q C cZ).cQ = q ^ powT Dinur.K q := rfl

/-! ### The round's output -/

/-- One edge's record: its two endpoints and the code of its constraint. -/
noncomputable def edgeRule (F : FinBase) (pol : Polynomial ℕ) (r : Round)
    (posF cardB cardN cardNN : ℕ) {E : ExpanderFamily} {B : ℕ}
    (dflt : StepKey E r.T r.q B (Fintype.card (α → α → Bool)))
    (encβ : (PreWalk E r.T → α) → Cube B) (w : List Bool) : List Bool :=
  encTriple (tailBlk posF r w) (headBlk F pol r cardB cardN cardNN dflt encβ w)
    (codeFn F pol r dflt encβ w)

theorem edgeRule_mem_FP (F : FinBase) (pol : Polynomial ℕ) (r : Round)
    (posF cardB cardN cardNN : ℕ) {E : ExpanderFamily} {B : ℕ}
    (hQ : 0 < r.cQ) (hD : 0 < r.cD) (hZ : 0 < r.cZ) (hC : 0 < r.C)
    (dflt : StepKey E r.T r.q B (Fintype.card (α → α → Bool)))
    (encβ : (PreWalk E r.T → α) → Cube B) :
    edgeRule F pol r posF cardB cardN cardNN dflt encβ ∈ FP :=
  encTriple_mem_FP (tailBlk_mem_FP posF r)
    (headBlk_mem_FP F pol r cardB cardN cardNN hQ hD hZ hC dflt encβ)
    (codeFn_mem_FP F pol r hQ hD hZ hC dflt encβ)

/-- **The graph a round produces**, from the graph it is given. -/
noncomputable def stepFn (F : FinBase) (pol : Polynomial ℕ) (r : Round)
    (vertF edgeF posF cardB cardN cardNN : ℕ) {E : ExpanderFamily} {B : ℕ}
    (dflt : StepKey E r.T r.q B (Fintype.card (α → α → Bool)))
    (encβ : (PreWalk E r.T → α) → Cube B) : List Bool → List Bool :=
  buildGraph (fun z => marks (mulC vertF (posCount (pairSnd z))))
    (fun z => marks (mulC edgeF (posCount (pairSnd z))))
    (edgeRule F pol r posF cardB cardN cardNN dflt encβ)

/-- **A count block is a constant multiple of the input's edge count.** -/
theorem countBlk_eq (G : ConstraintGraph α) (c : ℕ) :
    marks (mulC c (posCount (pairSnd (encGraph G))))
      = List.replicate (c * G.numEdges) true := by
  have hcnt : (posCount (pairSnd (encGraph G))).length = G.numEdges := by
    have h := gEdges_encGraph G
    rwa [gEdges] at h
  rw [marks_eq, length_mulC, hcnt, Nat.mul_comm]

theorem stepFn_mem_FP (F : FinBase) (pol : Polynomial ℕ) (r : Round)
    (vertF edgeF posF cardB cardN cardNN : ℕ) {E : ExpanderFamily} {B : ℕ}
    (hQ : 0 < r.cQ) (hD : 0 < r.cD) (hZ : 0 < r.cZ) (hC : 0 < r.C)
    (dflt : StepKey E r.T r.q B (Fintype.card (α → α → Bool)))
    (encβ : (PreWalk E r.T → α) → Cube B) :
    stepFn F pol r vertF edgeF posF cardB cardN cardNN dflt encβ ∈ FP :=
  buildGraph_mem_FP (marks_mem_FP (mulC_mem_FP (posCount_mem_FP Cobham.sndBlock_mem_FP) vertF))
    (marks_mem_FP (mulC_mem_FP (posCount_mem_FP Cobham.sndBlock_mem_FP) edgeF))
    (edgeRule_mem_FP F pol r posF cardB cardN cardNN hQ hD hZ hC dflt encβ)

/-- **One round of amplification, computed.** The algorithm's output is the
graph the round produces. -/
theorem stepFn_eq (F : FinBase) (pol : Polynomial ℕ) (hd : 1 < F.deg)
    (G : ConstraintGraph DinurAlpha)
    (r : Round) (hq : 0 < r.q) (vertF edgeF posF cardB cardN cardNN : ℕ)
    (hrD : r.cD = NumEnc.card ((G.preprocess (F.toFamily hd)).killedPow r.q r.T hq).graph.D)
    (hrZ : r.cZ = 2 ^ ROf (Dinur.bits (F.toFamily hd) r.T))
    (hdeg : r.deg = (F.toFamily hd).degree) (hP : r.P = G.preDeg (F.toFamily hd))
    (hC : r.C = Fintype.card (DinurAlpha → DinurAlpha → Bool))
    (hpc : ∀ u : Fin G.numVerts,
      F.fitLevel hd (G.cloudList u).length ≤ pol.eval (G.cloudList u).length)
    (hpe : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges))
    (hvertF : (((G.preprocess (F.toFamily hd)).killedPow r.q r.T hq).compose
      (Dinur.enc (F.toFamily hd) G r.T)).toGraph.numVerts = vertF * G.numEdges)
    (hedgeF : (((G.preprocess (F.toFamily hd)).killedPow r.q r.T hq).compose
      (Dinur.enc (F.toFamily hd) G r.T)).toGraph.numEdges = edgeF * G.numEdges)
    (hcardB : cardB = NumEnc.card (Cube (Dinur.bits (F.toFamily hd) r.T)))
    (hcardN : cardN = NumEnc.card (Cube (nOf (Dinur.bits (F.toFamily hd) r.T))))
    (hcardNN : cardNN = NumEnc.card (Cube (nOf (Dinur.bits (F.toFamily hd) r.T)
      * nOf (Dinur.bits (F.toFamily hd) r.T))))
    (hposF : Fintype.card (((G.preprocess (F.toFamily hd)).killedPow r.q r.T hq).Pos
      (B := Dinur.bits (F.toFamily hd) r.T)) = G.numEdges * posF)
    (dflt : StepKey (F.toFamily hd) r.T r.q (Dinur.bits (F.toFamily hd) r.T)
      (Fintype.card (DinurAlpha → DinurAlpha → Bool)))
 :
    stepFn F pol r vertF edgeF posF cardB cardN cardNN dflt
        (Dinur.enc (F.toFamily hd) G r.T) (encGraph G)
      = encGraph ((((G.preprocess (F.toFamily hd)).killedPow r.q r.T hq).compose
        (Dinur.enc (F.toFamily hd) G r.T)).toGraph) := by
  refine buildGraph_eq ?_ ?_ ?_
  · rw [countBlk_eq, hvertF]
  · rw [countBlk_eq, hedgeF]
  · intro e he
    obtain ⟨p, z, i, hsplit, htail, hhead, hrel⟩ := RegCSP.edge_facts
      ((G.preprocess (F.toFamily hd)).killedPow r.q r.T hq)
      (Dinur.enc (F.toFamily hd) G r.T) e he
    rw [htail, hhead, hrel]
    rw [← hrD, ← hrZ] at hsplit
    have hDpos : 0 < r.cD := by
      rw [hrD]
      have := NumEnc.enc_lt p.2
      omega
    have hblt : NumEnc.enc p.2 < r.cD := by
      rw [hrD]
      exact NumEnc.enc_lt p.2
    have hilt : NumEnc.enc i < 22 := NumEnc.enc_lt i
    have hclt : NumEnc.enc z < r.cZ := by
      rw [hrZ]
      have h := NumEnc.enc_lt z
      rw [NumEnc.card_eq_fintype_card, card_cube] at h
      exact h
    subst hsplit
    have hV' : NumEnc.card ((G.preprocess (F.toFamily hd)).killedPow r.q r.T hq).graph.V
        = 2 * G.numEdges := by
      rw [NumEnc.card_eq_fintype_card]
      exact G.order_preprocess (F.toFamily hd)
    obtain ⟨htest, hvert, hdart, hrand, hread⟩ :=
      blocks_eq r hDpos (by omega) (encGraph G)
        (NumEnc.enc p.1) (NumEnc.enc p.2) (NumEnc.enc z) (NumEnc.enc i) hblt hclt hilt
    simp only [edgeRule]
    rw [tailBlk_eq posF r G (pairFst_pair _ _) htest hrand,
      RegCSP.tailNum_split' (cZ := r.cZ) _ _ _ _ _ _ hrZ hclt hilt, hposF]
    rw [codeFn_eq' (B := Dinur.bits (F.toFamily hd) r.T) r hd G hq hdeg hP hC (by omega) p z i
      (by rw [hrZ, NumEnc.card_eq_fintype_card, card_cube]) hpc hpe dflt
      (Dinur.enc (F.toFamily hd) G r.T)]
    have hread : readFn (pair (encGraph G) (List.replicate
        (((NumEnc.enc p.1 * r.cD + NumEnc.enc p.2) * r.cZ + NumEnc.enc z) * 22
          + NumEnc.enc i) true)) = List.replicate (NumEnc.enc i) true := hread
    have hcube := cubeFn_eq' (B := Dinur.bits (F.toFamily hd) r.T) r hd G hq hdeg hP hC
      (by omega) p z i (by rw [hrZ, NumEnc.card_eq_fintype_card, card_cube]) hpc hpe dflt
      (Dinur.enc (F.toFamily hd) G r.T)
    have hblock : blockBlk F pol r (pair (encGraph G) (List.replicate
        (((NumEnc.enc p.1 * r.cD + NumEnc.enc p.2) * r.cZ + NumEnc.enc z) * 22
          + NumEnc.enc i) true))
        = List.replicate (((G.preprocess (F.toFamily hd)).killedPow r.q r.T hq).blockNum p i)
          true := by
      refine blockBlk_eq F pol r p i hread hvert ?_ ?_
      · have hdart' : NumEnc.enc p = NumEnc.enc p.1 * r.cD + NumEnc.enc p.2 := by
          rw [RegCSP.enc_dart, hrD]
        rw [hdart']
        exact htest
      · have hv2 : NumEnc.enc p.1 < 2 * G.numEdges := by
          have h := NumEnc.enc_lt p.1
          rwa [hV'] at h
        have hc2 : NumEnc.enc p.2.2 < r.q ^ r.T := NumEnc.enc_lt p.2.2
        have hd2 : NumEnc.enc p.2 = NumEnc.enc p.2.1 * r.q ^ r.T + NumEnc.enc p.2.2 := rfl
        have hkr := killedRotFn_eq hd G r.T r.q (NumEnc.enc p.1) (NumEnc.enc p.2.1)
          (NumEnc.enc p.2.2) hq hv2 hc2 hpc hpe
        rw [killArg_eq r (pairFst_pair _ _) hvert hdart, hdeg, hP, hd2, hkr,
          pairFst_pair]
        have hrn := G.killedRotNum_eq (F.toFamily hd) hq (G.preDeg_pos _) p.1 p.2
          (w := (((G.preprocess (F.toFamily hd)).graph.killedPower r.q r.T hq).rot
            (p.1, p.2)).1)
          (y := (((G.preprocess (F.toFamily hd)).graph.killedPower r.q r.T hq).rot
            (p.1, p.2)).2) rfl
        exact congrArg (fun n => List.replicate n true) (congrArg Prod.fst hrn)
    rw [headBlk_eq F pol r cardB cardN cardNN dflt (Dinur.enc (F.toFamily hd) G r.T)
      (vertCount_eq G (pairFst_pair _ _)) (kindBlk_eq hread) hblock hcube]
    rw [hV', ← hrD, ← hcardB, ← hcardN, ← hcardNN]
    rfl

end Complexity
