/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.AlgGraph
public import Complexitylib.Classes.PCP.Internal.AlgPreprocess
public import Complexitylib.Classes.PCP.Internal.Materialize
public import Complexitylib.Classes.PCP.Internal.AlgFamily

/-!
# Reading a half-edge's endpoint

A half-edge is numbered `2 e` or `2 e + 1` according to which end of edge `e` it
is, so the vertex it hangs from is one of that edge's two endpoints — and both
are written down in the encoded graph. Halving the number picks the edge, its
parity picks the end.

## Main definitions

- `Complexity.ownerFn` — the vertex a half-edge number hangs from
- `Complexity.cloudSizeFn` — how many half-edges hang from a vertex
- `Complexity.cloudIdxFn` — how many of them come first

## Main results

- `Complexity.ownerFn_mem_FP`, `Complexity.ownerFn_eq`
- `Complexity.cloudSizeFn_mem_FP`, `Complexity.length_cloudSizeFn` — the count
  is the number of half-edges the rule accepts
- `Complexity.ConstraintGraph.count_owner_eq_card_cloud` — and counting numbers
  is counting half-edges
- `Complexity.cloudStepFn`, `Complexity.expStepFn` — the two moves that need the
  expander
- `Complexity.preRotFn` — the preprocessed graph's rotation map, as one function

## Main results

- `Complexity.expStepFn_eq` — the expander move computes what it should
-/

@[expose] public section

namespace Complexity

/-- The vertex a half-edge hangs from, on `pair (encoded graph) (unary p)`. -/
noncomputable def ownerFn (z : List Bool) : List Bool :=
  ifEqLen (modC 2 (pairSnd z)) []
    (recSnd (pairSnd (pairFst z)) (divC 2 (pairSnd z)).length)
    (recFst (pairSnd (pairFst z)) (divC 2 (pairSnd z)).length)

theorem ownerFn_mem_FP : ownerFn ∈ FP := by
  have hp : (fun z : List Bool => pairSnd z) ∈ FP := Cobham.sndBlock_mem_FP
  have hG : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP) fun _ => rfl
  have he := divC_mem_FP hp 2
  have hb := modC_mem_FP hp 2
  exact ifEqLen_mem_FP hb (constFn_mem_FP []) (recSnd_mem_FP he hG) (recFst_mem_FP he hG)

/-! ### Counting a cloud -/

/-- One mark when the half-edge `j` hangs from the vertex asked for. The
argument is `pair (pair (encoded graph) (unary u)) (unary j)`. -/
noncomputable def cloudMark (w : List Bool) : List Bool :=
  ifEqLen (ownerFn (pair (pairFst (pairFst w)) (pairSnd w)))
    (pairSnd (pairFst w)) [true] []

theorem cloudMark_mem_FP : cloudMark ∈ FP := by
  have hG : (fun w : List Bool => pairFst (pairFst w)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
  have hu : (fun w : List Bool => pairSnd (pairFst w)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hj : (fun w : List Bool => pairSnd w) ∈ FP := Cobham.sndBlock_mem_FP
  have hown : (fun w : List Bool =>
      ownerFn (pair (pairFst (pairFst w)) (pairSnd w))) ∈ FP := by
    have h := mem_FP_comp (Cobham.pairFn_mem_FP hG hj) ownerFn_mem_FP
    refine mem_FP_of_eq h fun w => ?_
    rw [Function.comp_apply]
  exact ifEqLen_mem_FP hown hu (constFn_mem_FP [true]) (constFn_mem_FP [])

theorem length_cloudMark (Gz u j : List Bool) :
    (cloudMark (pair (pair Gz u) j)).length
      = if (ownerFn (pair Gz j)).length = u.length then 1 else 0 := by
  rw [cloudMark, pairFst_pair, pairSnd_pair, pairFst_pair,
    pairSnd_pair]
  by_cases h : (ownerFn (pair Gz j)).length = u.length
  · rw [ifEqLen_pos h, ite_eq_left h]
    rfl
  · rw [ifEqLen_neg h, ite_eq_right h]
    rfl

/-- How many half-edges hang from the vertex asked for, on
`pair (encoded graph) (unary u)`. -/
noncomputable def cloudSizeFn (z : List Bool) : List Bool :=
  countOver cloudMark
    (pair (marks (mulC 2 (posCount (pairSnd (pairFst z))))) z)

theorem cloudSizeFn_mem_FP : cloudSizeFn ∈ FP := by
  have hcnt : (fun z : List Bool =>
      marks (mulC 2 (posCount (pairSnd (pairFst z))))) ∈ FP := by
    have h1 : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
      mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
    exact marks_mem_FP (mulC_mem_FP (posCount_mem_FP h1) 2)
  have harg := Cobham.pairFn_mem_FP hcnt id_mem_FP
  have h := mem_FP_comp harg (countOver_mem_FP cloudMark_mem_FP)
  refine mem_FP_of_eq h fun w => ?_
  rw [Function.comp_apply, cloudSizeFn]
  rfl

/-- **The count is the number of half-edges the rule accepts.** -/
theorem length_cloudSizeFn (Gz u : List Bool) (m : ℕ)
    (hm : (mulC 2 (posCount (pairSnd Gz))).length = m) :
    (cloudSizeFn (pair Gz u)).length
      = ∑ j ∈ Finset.range m,
        (if (ownerFn (pair Gz (List.replicate j true))).length = u.length then 1 else 0) := by
  have hmarks : marks (mulC 2 (posCount (pairSnd Gz))) = List.replicate m true := by
    rw [marks_eq, hm]
  rw [cloudSizeFn, pairFst_pair, hmarks, length_countOver]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [length_cloudMark]

/-- How many half-edges before this one hang from the same vertex, on
`pair (encoded graph) (unary p)`. -/
noncomputable def cloudIdxFn (z : List Bool) : List Bool :=
  countOver cloudMark
    (pair (marks (pairSnd z)) (pair (pairFst z) (ownerFn z)))

theorem cloudIdxFn_mem_FP : cloudIdxFn ∈ FP := by
  have hcnt := marks_mem_FP Cobham.sndBlock_mem_FP
  have hdata := Cobham.pairFn_mem_FP Cobham.fstBlock_mem_FP ownerFn_mem_FP
  have h := mem_FP_comp (Cobham.pairFn_mem_FP hcnt hdata)
    (countOver_mem_FP cloudMark_mem_FP)
  refine mem_FP_of_eq h fun w => ?_
  rw [Function.comp_apply, cloudIdxFn]

/-- **The index is the number of earlier half-edges in the same cloud.** -/
theorem length_cloudIdxFn (Gz : List Bool) (p : ℕ) :
    (cloudIdxFn (pair Gz (List.replicate p true))).length
      = ∑ j ∈ Finset.range p,
        (if (ownerFn (pair Gz (List.replicate j true))).length
            = (ownerFn (pair Gz (List.replicate p true))).length then 1 else 0) := by
  have hmarks : marks (pairSnd (pair Gz (List.replicate p true)))
      = List.replicate p true := by
    rw [pairSnd_pair, marks_eq, List.length_replicate]
  rw [cloudIdxFn, hmarks, pairFst_pair, length_countOver]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [length_cloudMark]

/-! ### Finding a cloud's members -/



/-- One mark when the half-edge `c` is the `k`-th of the cloud of `u`. The
argument is `pair (pair (encoded graph) (pair (unary u) (unary k))) (unary c)`. -/
noncomputable def eltMark (w : List Bool) : List Bool :=
  ifEqLen (ownerFn (pair (pairFst (pairFst w)) (pairSnd w)))
    (pairFst (pairSnd (pairFst w)))
    (ifEqLen (cloudIdxFn (pair (pairFst (pairFst w)) (pairSnd w)))
      (pairSnd (pairSnd (pairFst w))) [true] [])
    []

theorem eltMark_mem_FP : eltMark ∈ FP := by
  have hG : (fun w : List Bool => pairFst (pairFst w)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
  have hc : (fun w : List Bool => pairSnd w) ∈ FP := Cobham.sndBlock_mem_FP
  have hu : (fun w : List Bool =>
      pairFst (pairSnd (pairFst w))) ∈ FP :=
    mem_FP_comp (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP)
      Cobham.fstBlock_mem_FP
  have hk : (fun w : List Bool =>
      pairSnd (pairSnd (pairFst w))) ∈ FP :=
    mem_FP_comp (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP)
      Cobham.sndBlock_mem_FP
  have harg := Cobham.pairFn_mem_FP hG hc
  have hown : (fun w : List Bool =>
      ownerFn (pair (pairFst (pairFst w)) (pairSnd w))) ∈ FP := by
    have h := mem_FP_comp harg ownerFn_mem_FP
    refine mem_FP_of_eq h fun w => ?_
    rw [Function.comp_apply]
  have hidx : (fun w : List Bool =>
      cloudIdxFn (pair (pairFst (pairFst w)) (pairSnd w))) ∈ FP := by
    have h := mem_FP_comp harg cloudIdxFn_mem_FP
    refine mem_FP_of_eq h fun w => ?_
    rw [Function.comp_apply]
  exact ifEqLen_mem_FP hown hu
    (ifEqLen_mem_FP hidx hk (constFn_mem_FP [true]) (constFn_mem_FP []))
    (constFn_mem_FP [])

theorem length_eltMark (Gz u k c : List Bool) :
    (eltMark (pair (pair Gz (pair u k)) c)).length
      = if (ownerFn (pair Gz c)).length = u.length then
          (if (cloudIdxFn (pair Gz c)).length = k.length then 1 else 0)
        else 0 := by
  rw [eltMark, pairFst_pair, pairSnd_pair, pairFst_pair,
    pairSnd_pair, pairFst_pair, pairSnd_pair]
  by_cases h1 : (ownerFn (pair Gz c)).length = u.length
  · rw [ifEqLen_pos h1, ite_eq_left h1]
    by_cases h2 : (cloudIdxFn (pair Gz c)).length = k.length
    · rw [ifEqLen_pos h2, ite_eq_left h2]
      rfl
    · rw [ifEqLen_neg h2, ite_eq_right h2]
      rfl
  · rw [ifEqLen_neg h1, ite_eq_right h1]
    rfl

/-- The `k`-th half-edge of the cloud of `u`, on
`pair (encoded graph) (pair (unary u) (unary k))`. -/
noncomputable def cloudEltFn (z : List Bool) : List Bool :=
  findFirst eltMark
    (pair (marks (mulC 2 (posCount (pairSnd (pairFst z))))) z)

theorem cloudEltFn_eq_replicate (z : List Bool) :
    cloudEltFn z = List.replicate (cloudEltFn z).length true := by
  conv_lhs => rw [cloudEltFn, findFirst_eq_replicate]
  rw [← cloudEltFn]

theorem cloudEltFn_mem_FP : cloudEltFn ∈ FP := by
  have h1 : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hcnt := marks_mem_FP (mulC_mem_FP (posCount_mem_FP h1) 2)
  have h := mem_FP_comp (Cobham.pairFn_mem_FP hcnt id_mem_FP)
    (findFirst_mem_FP eltMark_mem_FP)
  refine mem_FP_of_eq h fun w => ?_
  rw [Function.comp_apply, cloudEltFn]
  rfl

variable {α : Type} [Fintype α] [DecidableEq α]

/-- **The reading is the owner.** -/
theorem ownerFn_eq (G : ConstraintGraph α) (p : ℕ) (hp : p / 2 < G.numEdges) :
    ownerFn (pair (encGraph G) (List.replicate p true))
      = List.replicate (G.ownerNum p) true := by
  have hdiv : (divC 2 (List.replicate p true)) = List.replicate (p / 2) true := by
    rw [divC_eq (by norm_num), List.length_replicate]
  have hmod : (modC 2 (List.replicate p true)) = List.replicate (p % 2) true := by
    rw [modC_eq (by norm_num), List.length_replicate]
  rw [ownerFn, pairSnd_pair, pairFst_pair, hdiv, hmod,
    List.length_replicate, ConstraintGraph.ownerNum, dite_eq_left hp]
  by_cases h : p % 2 = 0
  · rw [ite_eq_left h, ifEqLen_pos (by rw [h]; rfl)]
    rw [encGraph, pairSnd_pair,
      recSnd_eq (l3 := edgeRecs G) (by rw [length_edgeRecs]; exact hp)
        (getElem_edgeRecs G _ hp)]
  · rw [ite_eq_right h, ifEqLen_neg (by
      rw [List.length_replicate, List.length_nil]
      exact h)]
    rw [encGraph, pairSnd_pair,
      recFst_eq (l3 := edgeRecs G) (by rw [length_edgeRecs]; exact hp)
        (getElem_edgeRecs G _ hp)]

namespace ConstraintGraph

omit [Fintype α] [DecidableEq α] in
/-- **Counting numbers is counting half-edges.** -/
theorem count_owner_eq_card_cloud (G : ConstraintGraph α) (v : Fin G.numVerts) :
    ((Finset.range (2 * G.numEdges)).filter fun j => G.ownerNum j = v.val).card
      = (G.cloud v).card := by
  classical
  refine (Finset.card_bij (fun p _ => NumEnc.enc p) ?_ ?_ ?_).symm
  · intro p hp
    have howner : G.owner p = v := (G.mem_cloud).mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · show NumEnc.enc p < 2 * G.numEdges
      rw [enc_halfEdge, halfCode]
      have he := p.1.isLt
      cases p.2
      · simp
        omega
      · simp
    · show G.ownerNum (NumEnc.enc p) = v.val
      rw [G.ownerNum_enc p, howner]
  · intro p _ q _ h
    exact NumEnc.enc_injective h
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    have he : j / 2 < G.numEdges := by omega
    refine ⟨(⟨j / 2, he⟩, decide (j % 2 = 0)), ?_, ?_⟩
    · have hcode : NumEnc.enc ((⟨j / 2, he⟩, decide (j % 2 = 0)) : G.HalfEdge) = j := by
        rw [enc_halfEdge, halfCode]
        by_cases h2 : j % 2 = 0 <;> simp [h2] <;> omega
      have hown := G.ownerNum_enc ((⟨j / 2, he⟩, decide (j % 2 = 0)) : G.HalfEdge)
      rw [hcode] at hown
      exact (G.mem_cloud).mpr (Fin.ext (hown.symm.trans hj.2))
    · show NumEnc.enc ((⟨j / 2, he⟩, decide (j % 2 = 0)) : G.HalfEdge) = j
      rw [enc_halfEdge, halfCode]
      by_cases h2 : j % 2 = 0 <;> simp [h2] <;> omega

omit [Fintype α] [DecidableEq α] in
/-- **Counting numbers below a bound is counting codes below it.** -/
theorem count_owner_lt_eq_countBelow (G : ConstraintGraph α) (v : Fin G.numVerts) (m : ℕ)
    (hm : m ≤ 2 * G.numEdges) :
    ((Finset.range m).filter fun j => G.ownerNum j = v.val).card
      = countBelow (G.cloudCodes v) m := by
  classical
  rw [G.countBelow_cloudCodes v m]
  refine (Finset.card_bij (fun p _ => NumEnc.enc p) ?_ ?_ ?_).symm
  · intro p hp
    rw [Finset.mem_filter] at hp
    have howner : G.owner p = v := (G.mem_cloud).mp hp.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · show NumEnc.enc p < m
      rw [enc_halfEdge]
      exact hp.2
    · show G.ownerNum (NumEnc.enc p) = v.val
      rw [G.ownerNum_enc p, howner]
  · intro p _ q _ h
    exact NumEnc.enc_injective h
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    have he : j / 2 < G.numEdges := by omega
    refine ⟨(⟨j / 2, he⟩, decide (j % 2 = 0)), ?_, ?_⟩
    · have hcode : NumEnc.enc ((⟨j / 2, he⟩, decide (j % 2 = 0)) : G.HalfEdge) = j := by
        rw [enc_halfEdge, halfCode]
        by_cases h2 : j % 2 = 0 <;> simp [h2] <;> omega
      have hown := G.ownerNum_enc ((⟨j / 2, he⟩, decide (j % 2 = 0)) : G.HalfEdge)
      rw [hcode] at hown
      refine Finset.mem_filter.mpr ⟨(G.mem_cloud).mpr (Fin.ext (hown.symm.trans hj.2)), ?_⟩
      rw [← enc_halfEdge, hcode]
      exact hj.1
    · show NumEnc.enc ((⟨j / 2, he⟩, decide (j % 2 = 0)) : G.HalfEdge) = j
      rw [enc_halfEdge, halfCode]
      by_cases h2 : j % 2 = 0 <;> simp [h2] <;> omega

end ConstraintGraph

/-! ### What the counts compute -/

variable (G : ConstraintGraph α)

theorem length_count_encGraph :
    (mulC 2 (posCount (pairSnd (encGraph G)))).length = 2 * G.numEdges := by
  rw [encGraph, pairSnd_pair, posCount_eq, length_mulC, List.length_replicate,
    length_edgeRecs]
  ring

/-- **The size the algorithm counts is the size of the cloud.** -/
theorem length_cloudSizeFn_eq (v : Fin G.numVerts) :
    (cloudSizeFn (pair (encGraph G) (List.replicate v.val true))).length
      = (G.cloud v).card := by
  classical
  rw [length_cloudSizeFn _ _ _ (length_count_encGraph G)]
  rw [← ConstraintGraph.count_owner_eq_card_cloud G v, Finset.card_filter]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hje : j / 2 < G.numEdges := by omega
  rw [ownerFn_eq G j hje, List.length_replicate, List.length_replicate]

/-- **The index the algorithm counts is the position in the cloud.** -/
theorem length_cloudIdxFn_eq (m : ℕ) (hm : m < 2 * G.numEdges) :
    (cloudIdxFn (pair (encGraph G) (List.replicate m true))).length
      = countBelow (G.cloudCodes ⟨G.ownerNum m, by
          have hme : m / 2 < G.numEdges := by omega
          rw [ConstraintGraph.ownerNum, dite_eq_left hme]
          split <;> exact Fin.isLt _⟩) m := by
  classical
  have hme : m / 2 < G.numEdges := by omega
  rw [length_cloudIdxFn, ← ConstraintGraph.count_owner_lt_eq_countBelow G _ m (by omega),
    Finset.card_filter]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hje : j / 2 < G.numEdges := by omega
  rw [ownerFn_eq G j hje, ownerFn_eq G m hme, List.length_replicate, List.length_replicate]

omit [Fintype α] [DecidableEq α] in
/-- The code of a half-edge is below twice the edge count. -/
theorem halfCode_lt (p : G.HalfEdge) : G.halfCode p < 2 * G.numEdges := by
  rw [ConstraintGraph.halfCode]
  by_cases hb : p.2 = true
  · rw [ite_eq_left hb]
    omega
  · rw [ite_eq_right hb]
    omega

/-- **The search finds the `k`-th half-edge of the cloud.** -/
theorem length_cloudEltFn_eq (v : Fin G.numVerts) (k : ℕ)
    (hk : k < (G.cloudList v).length) :
    (cloudEltFn (pair (encGraph G) (pair (List.replicate v.val true)
        (List.replicate k true)))).length
      = G.halfCode ((G.cloudList v)[k]) := by
  classical
  set q : G.HalfEdge := (G.cloudList v)[k] with hq
  have hmem : q ∈ G.cloudList v := List.getElem_mem hk
  have howner : G.owner q = v := (G.mem_cloud).mp ((G.mem_cloudList).mp hmem)
  have hidx : (G.cloudList v).idxOf q = k := (G.nodup_cloudList v).idxOf_getElem _ hk
  have hcount : countBelow (G.cloudCodes v) (G.halfCode q) = k := by
    rw [← G.idxOf_cloudList howner, hidx]
  have hclt : G.halfCode q < 2 * G.numEdges := halfCode_lt G q
  have hmarks : marks (mulC 2 (posCount (pairSnd (encGraph G))))
      = List.replicate (2 * G.numEdges) true := by
    rw [marks_eq, length_count_encGraph]
  rw [cloudEltFn, pairFst_pair, hmarks]
  refine length_findFirst_eq hclt ?_ ?_
  · have howner' : G.ownerNum (G.halfCode q) = v.val := by
      rw [← ConstraintGraph.enc_halfEdge, ConstraintGraph.ownerNum_enc, howner]
    have hown1 : (ownerFn (pair (encGraph G) (List.replicate (G.halfCode q) true))).length
        = (List.replicate v.val true).length := by
      rw [ownerFn_eq G _ (by omega), List.length_replicate, List.length_replicate, howner']
    have hidx1 : (cloudIdxFn (pair (encGraph G) (List.replicate (G.halfCode q) true))).length
        = (List.replicate k true).length := by
      rw [length_cloudIdxFn_eq G _ hclt, List.length_replicate]
      have hv : (⟨G.ownerNum (G.halfCode q), by
          have hme : G.halfCode q / 2 < G.numEdges := by omega
          rw [ConstraintGraph.ownerNum, dite_eq_left hme]
          split <;> exact Fin.isLt _⟩ : Fin G.numVerts) = v := Fin.ext howner'
      rw [hv, hcount]
    rw [length_eltMark, ite_eq_left hown1, ite_eq_left hidx1]
    omega
  · intro j hj
    rw [length_eltMark]
    by_cases h1 : (ownerFn (pair (encGraph G) (List.replicate j true))).length
        = (List.replicate v.val true).length
    · rw [ite_eq_left h1, ite_eq_right ?_]
      have hjlt : j < 2 * G.numEdges := by omega
      have hjown : G.ownerNum j = v.val := by
        rw [ownerFn_eq G j (by omega), List.length_replicate, List.length_replicate] at h1
        exact h1
      have hjmem : j ∈ G.cloudCodes v := by
        refine (G.mem_cloudCodes).mpr ⟨(⟨j / 2, by omega⟩, decide (j % 2 = 0)), ?_, ?_⟩
        · have hcode : NumEnc.enc ((⟨j / 2, by omega⟩, decide (j % 2 = 0)) : G.HalfEdge) = j := by
            rw [ConstraintGraph.enc_halfEdge, ConstraintGraph.halfCode]
            by_cases h2 : j % 2 = 0 <;> simp [h2] <;> omega
          have hown := G.ownerNum_enc ((⟨j / 2, by omega⟩, decide (j % 2 = 0)) : G.HalfEdge)
          rw [hcode] at hown
          exact Fin.ext (hown.symm.trans hjown)
        · rw [ConstraintGraph.halfCode]
          by_cases h2 : j % 2 = 0 <;> simp [h2] <;> omega
      have hlt := countBelow_lt_countBelow hjmem hj
      rw [hcount] at hlt
      rw [length_cloudIdxFn_eq G _ hjlt, List.length_replicate]
      have hjv : (⟨G.ownerNum j, by
          have hme : j / 2 < G.numEdges := by omega
          rw [ConstraintGraph.ownerNum, dite_eq_left hme]
          split <;> exact Fin.isLt _⟩ : Fin G.numVerts) = v := Fin.ext hjown
      rw [hjv]
      omega
    · rw [ite_eq_right h1]

/-! ### The two moves that need the expander -/

variable (F : FinBase) (pol : Polynomial ℕ)

/-- The cloud move, on `pair (pair (graph) (unary owner)) (pair (unary code)
(unary dart))`: rotate the half-edge's index inside its cloud, then read off the
half-edge the new index names. -/
noncomputable def cloudStepFn (z : List Bool) : List Bool :=
  pair
    (cloudEltFn (pair (pairFst (pairFst z))
      (pair (pairSnd (pairFst z))
        (pairFst (F.famRotFn pol
          (pair (cloudSizeFn (pair (pairFst (pairFst z))
              (pairSnd (pairFst z))))
            (pair (cloudIdxFn (pair (pairFst (pairFst z))
                (pairFst (pairSnd z))))
              (pairSnd (pairSnd z)))))))))
    (pairSnd (F.famRotFn pol
      (pair (cloudSizeFn (pair (pairFst (pairFst z))
          (pairSnd (pairFst z))))
        (pair (cloudIdxFn (pair (pairFst (pairFst z))
            (pairFst (pairSnd z))))
          (pairSnd (pairSnd z))))))

theorem cloudStepFn_mem_FP : cloudStepFn F pol ∈ FP := by
  have hG : (fun z : List Bool => pairFst (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
  have hu : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hc : (fun z : List Bool => pairFst (pairSnd z)) ∈ FP :=
    mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
  have hj : (fun z : List Bool => pairSnd (pairSnd z)) ∈ FP :=
    mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  have hsize : (fun z : List Bool => cloudSizeFn (pair (pairFst (pairFst z))
      (pairSnd (pairFst z)))) ∈ FP := by
    have h := mem_FP_comp (Cobham.pairFn_mem_FP hG hu) cloudSizeFn_mem_FP
    refine mem_FP_of_eq h fun w => ?_
    rw [Function.comp_apply]
  have hidx : (fun z : List Bool => cloudIdxFn (pair (pairFst (pairFst z))
      (pairFst (pairSnd z)))) ∈ FP := by
    have h := mem_FP_comp (Cobham.pairFn_mem_FP hG hc) cloudIdxFn_mem_FP
    refine mem_FP_of_eq h fun w => ?_
    rw [Function.comp_apply]
  have hy : (fun z : List Bool => F.famRotFn pol
      (pair (cloudSizeFn (pair (pairFst (pairFst z))
          (pairSnd (pairFst z))))
        (pair (cloudIdxFn (pair (pairFst (pairFst z))
            (pairFst (pairSnd z))))
          (pairSnd (pairSnd z))))) ∈ FP := by
    have h := mem_FP_comp (Cobham.pairFn_mem_FP hsize (Cobham.pairFn_mem_FP hidx hj))
      (F.famRotFn_mem_FP pol)
    refine mem_FP_of_eq h fun w => ?_
    rw [Function.comp_apply]
  have helt : (fun z : List Bool => cloudEltFn (pair (pairFst (pairFst z))
      (pair (pairSnd (pairFst z))
        (pairFst (F.famRotFn pol
          (pair (cloudSizeFn (pair (pairFst (pairFst z))
              (pairSnd (pairFst z))))
            (pair (cloudIdxFn (pair (pairFst (pairFst z))
                (pairFst (pairSnd z))))
              (pairSnd (pairSnd z))))))))) ∈ FP := by
    have h := mem_FP_comp (Cobham.pairFn_mem_FP hG
      (Cobham.pairFn_mem_FP hu (mem_FP_comp hy Cobham.fstBlock_mem_FP))) cloudEltFn_mem_FP
    refine mem_FP_of_eq h fun w => ?_
    simp only [Function.comp_apply]
  have hout := Cobham.pairFn_mem_FP helt (mem_FP_comp hy Cobham.sndBlock_mem_FP)
  refine mem_FP_of_eq hout fun w => ?_
  simp only [Function.comp_apply]
  rw [cloudStepFn]

/-- The expander move, on `pair (graph) (pair (unary vertex) (unary dart))`. -/
noncomputable def expStepFn (z : List Bool) : List Bool :=
  F.famRotFn pol
    (pair (marks (mulC 2 (posCount (pairSnd (pairFst z)))))
      (pairSnd z))

theorem expStepFn_mem_FP : expStepFn F pol ∈ FP := by
  have h1 : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hcnt := marks_mem_FP (mulC_mem_FP (posCount_mem_FP h1) 2)
  have h := mem_FP_comp (Cobham.pairFn_mem_FP hcnt Cobham.sndBlock_mem_FP)
    (F.famRotFn_mem_FP pol)
  refine mem_FP_of_eq h fun w => ?_
  rw [Function.comp_apply, expStepFn]

/-- **The cloud move computes what it should.** -/
theorem cloudStepFn_eq (hd : 1 < F.deg) (v : Fin G.numVerts) (c j : ℕ)
    (hc : c < 2 * G.numEdges) (hown : G.ownerNum c = v.val)
    (hj : j < (F.toFamily hd).degree)
    (hp : F.fitLevel hd (G.cloudList v).length ≤ pol.eval (G.cloudList v).length) :
    cloudStepFn F pol (pair (pair (encGraph G) (List.replicate v.val true))
        (pair (List.replicate c true) (List.replicate j true)))
      = pair (List.replicate (G.cloudStepNum (F.toFamily hd) v c ⟨j, hj⟩).1 true)
        (List.replicate (G.cloudStepNum (F.toFamily hd) v c ⟨j, hj⟩).2 true) := by
  classical
  have hce : c / 2 < G.numEdges := by omega
  have hcmem : c ∈ G.cloudCodes v := by
    refine (G.mem_cloudCodes).mpr ⟨(⟨c / 2, hce⟩, decide (c % 2 = 0)), ?_, ?_⟩
    · have hcode : NumEnc.enc ((⟨c / 2, hce⟩, decide (c % 2 = 0)) : G.HalfEdge) = c := by
        rw [ConstraintGraph.enc_halfEdge, ConstraintGraph.halfCode]
        by_cases h2 : c % 2 = 0 <;> simp [h2] <;> omega
      have hown' := G.ownerNum_enc ((⟨c / 2, hce⟩, decide (c % 2 = 0)) : G.HalfEdge)
      rw [hcode] at hown'
      exact Fin.ext (hown'.symm.trans hown)
    · rw [ConstraintGraph.halfCode]
      by_cases h2 : c % 2 = 0 <;> simp [h2] <;> omega
  have hidxlt : countBelow (G.cloudCodes v) c < (G.cloudList v).length := by
    rw [← G.card_cloudCodes_eq_length v]
    exact countBelow_lt_card hcmem
  have hpos : 0 < (G.cloudList v).length := by omega
  have hsizelen : (cloudSizeFn (pair (encGraph G) (List.replicate v.val true))).length
      = (G.cloudList v).length := by
    rw [length_cloudSizeFn_eq, ConstraintGraph.length_cloudList]
  have hsize : cloudSizeFn (pair (encGraph G) (List.replicate v.val true))
      = List.replicate (G.cloudList v).length true := by
    conv_lhs => rw [cloudSizeFn, countOver_eq_replicate]
    rw [← cloudSizeFn, hsizelen]
  have hvfin : (⟨G.ownerNum c, by
      rw [ConstraintGraph.ownerNum, dite_eq_left hce]
      split <;> exact Fin.isLt _⟩ : Fin G.numVerts) = v := Fin.ext hown
  have hidxlen : (cloudIdxFn (pair (encGraph G) (List.replicate c true))).length
      = countBelow (G.cloudCodes v) c := by
    rw [length_cloudIdxFn_eq G _ hc, hvfin]
  have hidx : cloudIdxFn (pair (encGraph G) (List.replicate c true))
      = List.replicate (countBelow (G.cloudCodes v) c) true := by
    conv_lhs => rw [cloudIdxFn, countOver_eq_replicate]
    rw [← cloudIdxFn, hidxlen]
  have hval : F.famRotVal hd (G.cloudList v).length (countBelow (G.cloudCodes v) c, j)
      = (((F.toFamily hd).rot (G.cloudList v).length
            ((⟨countBelow (G.cloudCodes v) c, hidxlt⟩ : Fin (G.cloudList v).length),
              (⟨j, hj⟩ : Fin (F.toFamily hd).degree))).1.val,
          ((F.toFamily hd).rot (G.cloudList v).length
            ((⟨countBelow (G.cloudCodes v) c, hidxlt⟩ : Fin (G.cloudList v).length),
              (⟨j, hj⟩ : Fin (F.toFamily hd).degree))).2.val) :=
    F.famRotVal_eq hd hpos (⟨_, hidxlt⟩ : Fin (G.cloudList v).length) ⟨j, hj⟩
  have hrot := F.famRotFn_eq pol hd (G.cloudList v).length
    (countBelow (G.cloudCodes v) c) j hpos hp
  rw [hval] at hrot
  have helt : cloudEltFn (pair (encGraph G) (pair (List.replicate v.val true)
      (List.replicate ((F.toFamily hd).rot (G.cloudList v).length
        ((⟨countBelow (G.cloudCodes v) c, hidxlt⟩ : Fin (G.cloudList v).length),
          (⟨j, hj⟩ : Fin (F.toFamily hd).degree))).1.val true)))
      = List.replicate (G.halfCode ((G.cloudList v)[((F.toFamily hd).rot
        (G.cloudList v).length
        ((⟨countBelow (G.cloudCodes v) c, hidxlt⟩ : Fin (G.cloudList v).length),
          (⟨j, hj⟩ : Fin (F.toFamily hd).degree))).1.val])) true := by
    conv_lhs => rw [cloudEltFn_eq_replicate]
    rw [length_cloudEltFn_eq G v _ (Fin.isLt _)]
  rw [cloudStepFn]
  simp only [pairFst_pair, pairSnd_pair]
  rw [hsize, hidx, hrot]
  simp only [pairFst_pair, pairSnd_pair]
  rw [helt, ConstraintGraph.cloudStepNum, dite_eq_left hidxlt]
  dsimp only
  rw [← G.halfCode_getElem_cloudList v _ (Fin.isLt _)]

/-- **The expander move computes what it should.** -/
theorem expStepFn_eq (hd : 1 < F.deg) (v j : ℕ) (hn : 0 < 2 * G.numEdges)
    (hp : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges)) :
    expStepFn F pol (pair (encGraph G)
        (pair (List.replicate v true) (List.replicate j true)))
      = pair (List.replicate (F.famRotVal hd (2 * G.numEdges) (v, j)).1 true)
        (List.replicate (F.famRotVal hd (2 * G.numEdges) (v, j)).2 true) := by
  have hmarks : marks (mulC 2 (posCount (pairSnd (encGraph G))))
      = List.replicate (2 * G.numEdges) true := by
    rw [marks_eq, length_count_encGraph]
  rw [expStepFn, pairFst_pair, pairSnd_pair, hmarks]
  exact F.famRotFn_eq pol hd _ v j hn hp

/-! ### The whole rotation map -/

/-- Crossing an edge: flip the last bit of the vertex number. -/
noncomputable def flipFn (v : List Bool) : List Bool :=
  ifEqLen (modC 2 v) [] (v ++ [true]) (dropOne v)

theorem flipFn_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun z => flipFn (f z)) ∈ FP :=
  ifEqLen_mem_FP (modC_mem_FP hf 2) (constFn_mem_FP [])
    (Cobham.appendFn_mem_FP hf (constFn_mem_FP [true])) (dropOneFn_mem_FP hf)

theorem flipFn_eq (v : ℕ) :
    flipFn (List.replicate v true)
      = List.replicate (if v % 2 = 0 then v + 1 else v - 1) true := by
  by_cases h : v % 2 = 0
  · rw [flipFn, modC_eq (by norm_num), List.length_replicate, h,
      ifEqLen_pos (by simp)]
    simp [List.replicate_succ']
  · rw [flipFn, modC_eq (by norm_num), List.length_replicate,
      ifEqLen_neg (by simp [h]), ite_eq_right h, dropOne]
    simp

/-- **The preprocessed graph's rotation map**, on
`pair (graph) (pair (unary vertex) (unary dart))`. Dart `0` is the self-loop,
dart `1` crosses the edge, the next `deg` are the cloud's, and the rest are the
superposed expander's. -/
noncomputable def preRotFn (deg : ℕ) (z : List Bool) : List Bool :=
  ifEqLen (pairSnd (pairSnd z)) []
    (pair (pairFst (pairSnd z)) [])
    (ifEqLen (pairSnd (pairSnd z)) [true]
      (pair (flipFn (pairFst (pairSnd z))) [true])
      (ifLtLen (pairSnd (pairSnd z)) (List.replicate (2 + deg) true)
        (pair
          (pairFst (cloudStepFn F pol
            (pair (pair (pairFst z)
                (ownerFn (pair (pairFst z) (pairFst (pairSnd z)))))
              (pair (pairFst (pairSnd z))
                ((pairSnd (pairSnd z)).drop 2)))))
          (pairSnd (cloudStepFn F pol
            (pair (pair (pairFst z)
                (ownerFn (pair (pairFst z) (pairFst (pairSnd z)))))
              (pair (pairFst (pairSnd z))
                ((pairSnd (pairSnd z)).drop 2)))) ++ [true, true]))
        (pair
          (pairFst (expStepFn F pol
            (pair (pairFst z)
              (pair (pairFst (pairSnd z))
                ((pairSnd (pairSnd z)).drop (2 + deg))))))
          (pairSnd (expStepFn F pol
            (pair (pairFst z)
              (pair (pairFst (pairSnd z))
                ((pairSnd (pairSnd z)).drop (2 + deg)))))
            ++ List.replicate (2 + deg) true))))

theorem preRotFn_mem_FP (deg : ℕ) : preRotFn F pol deg ∈ FP := by
  have hG : (fun z : List Bool => pairFst z) ∈ FP := Cobham.fstBlock_mem_FP
  have hv : (fun z : List Bool => pairFst (pairSnd z)) ∈ FP :=
    mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
  have hd : (fun z : List Bool => pairSnd (pairSnd z)) ∈ FP :=
    mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  have hd2 : (fun z : List Bool => (pairSnd (pairSnd z)).drop 2) ∈ FP := by
    have := dropLenFn_mem_FP (constFn_mem_FP (List.replicate 2 true)) hd
    refine mem_FP_of_eq this fun w => ?_
    rw [List.length_replicate]
  have hdk : (fun z : List Bool =>
      (pairSnd (pairSnd z)).drop (2 + deg)) ∈ FP := by
    have := dropLenFn_mem_FP (constFn_mem_FP (List.replicate (2 + deg) true)) hd
    refine mem_FP_of_eq this fun w => ?_
    rw [List.length_replicate]
  have hown : (fun z : List Bool =>
      ownerFn (pair (pairFst z) (pairFst (pairSnd z)))) ∈ FP := by
    have h := mem_FP_comp (Cobham.pairFn_mem_FP hG hv) ownerFn_mem_FP
    refine mem_FP_of_eq h fun w => ?_
    simp only [Function.comp_apply]
  have hcs : (fun z : List Bool => cloudStepFn F pol
      (pair (pair (pairFst z)
          (ownerFn (pair (pairFst z) (pairFst (pairSnd z)))))
        (pair (pairFst (pairSnd z))
          ((pairSnd (pairSnd z)).drop 2)))) ∈ FP := by
    have h := mem_FP_comp (Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP hG hown)
      (Cobham.pairFn_mem_FP hv hd2)) (cloudStepFn_mem_FP F pol)
    refine mem_FP_of_eq h fun w => ?_
    simp only [Function.comp_apply]
  have hes : (fun z : List Bool => expStepFn F pol
      (pair (pairFst z)
        (pair (pairFst (pairSnd z))
          ((pairSnd (pairSnd z)).drop (2 + deg))))) ∈ FP := by
    have h := mem_FP_comp (Cobham.pairFn_mem_FP hG (Cobham.pairFn_mem_FP hv hdk))
      (expStepFn_mem_FP F pol)
    refine mem_FP_of_eq h fun w => ?_
    simp only [Function.comp_apply]
  have hloop := Cobham.pairFn_mem_FP hv (constFn_mem_FP [])
  have hflip := Cobham.pairFn_mem_FP (flipFn_mem_FP hv) (constFn_mem_FP [true])
  have hcloud := Cobham.pairFn_mem_FP (mem_FP_comp hcs Cobham.fstBlock_mem_FP)
    (Cobham.appendFn_mem_FP (mem_FP_comp hcs Cobham.sndBlock_mem_FP)
      (constFn_mem_FP [true, true]))
  have hexp := Cobham.pairFn_mem_FP (mem_FP_comp hes Cobham.fstBlock_mem_FP)
    (Cobham.appendFn_mem_FP (mem_FP_comp hes Cobham.sndBlock_mem_FP)
      (constFn_mem_FP (List.replicate (2 + deg) true)))
  have hinner := ifLtLen_mem_FP hd (constFn_mem_FP (List.replicate (2 + deg) true))
    hcloud hexp
  have houter := ifEqLen_mem_FP hd (constFn_mem_FP []) hloop
    (ifEqLen_mem_FP hd (constFn_mem_FP [true]) hflip hinner)
  refine mem_FP_of_eq houter fun w => ?_
  simp only [Function.comp_apply]
  rw [preRotFn]

/-- **The whole rotation map computes what it should.** -/
theorem preRotFn_eq (hd : 1 < F.deg) (v d : ℕ) (hv : v < 2 * G.numEdges)
    (hdlt : d < 2 + 2 * (F.toFamily hd).degree)
    (hpc : ∀ u : Fin G.numVerts,
      F.fitLevel hd (G.cloudList u).length ≤ pol.eval (G.cloudList u).length)
    (hpe : F.fitLevel hd (2 * G.numEdges) ≤ pol.eval (2 * G.numEdges)) :
    preRotFn F pol (F.toFamily hd).degree
        (pair (encGraph G) (pair (List.replicate v true) (List.replicate d true)))
      = pair (List.replicate (G.preRotNum (F.toFamily hd) v d).1 true)
        (List.replicate (G.preRotNum (F.toFamily hd) v d).2 true) := by
  have hne : 0 < 2 * G.numEdges := Nat.lt_of_le_of_lt (Nat.zero_le _) hv
  have hvd : v / 2 < G.numEdges := by omega
  have hulr : G.ownerNum v < G.numVerts := by
    rw [ConstraintGraph.ownerNum, dite_eq_left hvd]
    split <;> exact Fin.isLt _
  rw [preRotFn]
  simp only [pairFst_pair, pairSnd_pair]
  rw [ConstraintGraph.preRotNum]
  by_cases h0 : d = 0
  · subst h0
    rw [ifEqLen_pos (by simp), ite_eq_left rfl]
    rfl
  rw [ifEqLen_neg (by simpa using h0), ite_eq_right h0]
  by_cases h1 : d = 1
  · subst h1
    rw [ifEqLen_pos (by simp), ite_eq_left rfl, flipFn_eq]
    rfl
  rw [ifEqLen_neg (by simpa using h1), ite_eq_right h1]
  have hdrop2 : (List.replicate d true).drop 2 = List.replicate (d - 2) true := by simp
  by_cases h2 : d < 2 + (F.toFamily hd).degree
  · -- the cloud's move
    have hjlt : d - 2 < (F.toFamily hd).degree := by omega
    rw [ifLtLen_pos (by simpa using h2), ite_eq_left h2, hdrop2,
      ownerFn_eq G v hvd,
      cloudStepFn_eq G F pol hd ⟨G.ownerNum v, hulr⟩ v (d - 2) hv rfl hjlt
        (hpc ⟨G.ownerNum v, hulr⟩)]
    rw [ConstraintGraph.cloudStepN, dite_eq_left hulr, dite_eq_left hjlt]
    simp only [pairFst_pair, pairSnd_pair]
    have happ : ∀ n : ℕ, List.replicate n true ++ [true, true]
        = List.replicate (n + 2) true := by
      intro n
      rw [List.replicate_add]
      rfl
    congr 1
    exact happ _
  · -- the expander's move
    have hjlt : d - (2 + (F.toFamily hd).degree) < (F.toFamily hd).degree := by omega
    have horder : (G.reduce (F.toFamily hd)).graph.order = 2 * G.numEdges := by
      rw [ConstraintGraph.graph_reduce, ConstraintGraph.order_reduceGraph]
    have hvlt : v < (G.reduce (F.toFamily hd)).graph.order := by rw [horder]; exact hv
    have key : ∀ (n : ℕ) (_ : n = 2 * G.numEdges) (hvn : v < n)
        (hjn : d - (2 + (F.toFamily hd).degree) < (F.toFamily hd).degree),
        (((F.toFamily hd).rot n (⟨v, hvn⟩, ⟨d - (2 + (F.toFamily hd).degree), hjn⟩)).1.val,
          ((F.toFamily hd).rot n
            (⟨v, hvn⟩, ⟨d - (2 + (F.toFamily hd).degree), hjn⟩)).2.val)
          = F.famRotVal hd (2 * G.numEdges) (v, d - (2 + (F.toFamily hd).degree)) := by
      rintro n rfl hvn hjn
      exact (F.famRotVal_eq hd hne ⟨v, hvn⟩ ⟨_, hjn⟩).symm
    have hdropk : (List.replicate d true).drop (2 + (F.toFamily hd).degree)
        = List.replicate (d - (2 + (F.toFamily hd).degree)) true := by simp
    rw [ifLtLen_neg (by simpa using h2), ite_eq_right h2, hdropk,
      expStepFn_eq G F pol hd v (d - (2 + (F.toFamily hd).degree)) hne hpe]
    rw [ConstraintGraph.expStepN, dite_eq_left hvlt, dite_eq_left hjlt]
    simp only [pairFst_pair, pairSnd_pair]
    have hk := key _ horder hvlt hjlt
    have hk1 := congrArg Prod.fst hk
    have hk2 := congrArg Prod.snd hk
    dsimp only at hk1 hk2 ⊢
    rw [hk1, hk2]
    congr 1
    rw [Nat.add_assoc, ← List.replicate_add]

end Complexity
