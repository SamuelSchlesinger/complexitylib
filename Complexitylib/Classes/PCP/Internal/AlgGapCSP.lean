/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.AlgGapAll
public import Complexitylib.Classes.PCP.Internal.BaseAlg

/-!
# The gap graph, as an algorithm

The verifier does not read a graph; it reads *an algorithm* that answers three
questions about one — how many edges, where an edge's ends are, and whether a
pair of symbols satisfies it. This module packages the gap graph that way, by
reading the string the reduction writes.

The constraint is a bounded-key decision: an edge's record names its constraint
by a code, and the code, together with the two symbol blocks, is all the
constraint depends on. Both are clamped to constant width, so the key is
constant-size even on strings that are not graphs at all.

## Main definitions

- `Complexity.gapAlg` — the gap graph as an `AlgCSP`

## Main results

- `Complexity.gapAlg_models` — it agrees with the gap graph
-/

@[expose] public section

set_option maxRecDepth 8000

namespace Complexity

open SAT

variable (F : FinBase) (hd : 1 < F.deg) (E padU : List Bool → List Bool)

/-! ### Reading the graph -/

/-- The graph string a verifier argument names. -/
noncomputable def gapStr (z : List Bool) : List Bool :=
  gapAll F hd E padU (pairFst (pairFst z))

theorem gapStr_mem_FP (hgap : gapAll F hd E padU ∈ FP) : gapStr F hd E padU ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP) hgap)
    fun _ => rfl

/-- The code of the constraint the argument names, clamped to the number of
constraints there are. -/
noncomputable def gapCodeBlk (z : List Bool) : List Bool :=
  (recThd (pairSnd (gapStr F hd E padU z))
    (pairSnd (pairFst z)).length).take cRel

theorem gapCodeBlk_mem_FP (hgap : gapAll F hd E padU ∈ FP) :
    gapCodeBlk F hd E padU ∈ FP := by
  have hidx : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP) fun _ => rfl
  have hrec := gCodeFn_mem_FP hidx (gapStr_mem_FP F hd E padU hgap)
  refine mem_FP_of_eq (Cobham.takeLenFn_mem_FP
    (constFn_mem_FP (List.replicate cRel false)) hrec) fun z => ?_
  rw [gapCodeBlk, List.length_replicate]

/-- Everything the constraint depends on: the code and the two symbol blocks. -/
noncomputable def gapOkKey (z : List Bool) : List Bool :=
  pair (gapCodeBlk F hd E padU z) ((pairSnd z).take 46)

theorem gapOkKey_mem_FP (hgap : gapAll F hd E padU ∈ FP) : gapOkKey F hd E padU ∈ FP :=
  Cobham.pairFn_mem_FP (gapCodeBlk_mem_FP F hd E padU hgap)
    (mem_FP_of_eq (Cobham.takeLenFn_mem_FP
      (constFn_mem_FP (List.replicate 46 false)) Cobham.sndBlock_mem_FP)
      fun z => by rw [List.length_replicate])

theorem gapOkKey_length_le (z : List Bool) :
    (gapOkKey F hd E padU z).length ≤ 2 * cRel + 48 := by
  have h1 : (gapCodeBlk F hd E padU z).length ≤ cRel := by
    rw [gapCodeBlk, List.length_take]
    omega
  have h2 : ((pairSnd z).take 46).length ≤ 46 := by
    rw [List.length_take]
    omega
  rw [gapOkKey, pair_length]
  omega

/-- What the constraint says, of the key alone. -/
def gapOkPred (k : List Bool) : Prop :=
  relOfCode DinurAlpha (pairFst k).length
      (symDec DinurAlpha ((pairSnd k).take 23))
      (symDec DinurAlpha ((pairSnd k).drop 23)) = true

/-- The constraint, as a language on the verifier's verdict argument. -/
noncomputable def gapOk : Language :=
  {z : List Bool | gapOkPred (gapOkKey F hd E padU z)}

theorem gapOk_mem_P (hgap : gapAll F hd E padU ∈ FP) : gapOk F hd E padU ∈ P :=
  mem_P_of_bounded_key (gapOkKey_mem_FP F hd E padU hgap)
    (gapOkKey_length_le F hd E padU) gapOkPred

/-! ### The record -/

/-- **The gap graph as an algorithm.** -/
noncomputable def gapAlg (hgap : gapAll F hd E padU ∈ FP) : AlgCSP where
  numEdges x := gEdges (gapAll F hd E padU x)
  numEdges_mem := by
    refine mem_FP_of_eq (marks_mem_FP (gEdgesFn_mem_FP hgap)) fun x => ?_
    rw [marks_eq, length_posCount_sndBlock]
  width := 23
  width_pos := by omega
  vert b x e :=
    cond b (gHead (gapAll F hd E padU x) e) (gTail (gapAll F hd E padU x) e)
  vert_mem := by
    intro b
    have hg : (fun w : List Bool => gapAll F hd E padU (pairFst w)) ∈ FP :=
      mem_FP_of_eq (mem_FP_comp Cobham.fstBlock_mem_FP hgap) fun _ => rfl
    cases b
    · refine mem_FP_of_eq (marks_mem_FP (gTailFn_mem_FP Cobham.sndBlock_mem_FP hg))
        fun w => ?_
      simp only [Bool.cond_false]
      rw [marks_eq, length_recFst_sndBlock]
    · refine mem_FP_of_eq (marks_mem_FP (gHeadFn_mem_FP Cobham.sndBlock_mem_FP hg))
        fun w => ?_
      simp only [Bool.cond_true]
      rw [marks_eq, length_recSnd_sndBlock]
  ok := gapOk F hd E padU
  ok_mem := gapOk_mem_P F hd E padU hgap

@[simp] theorem numEdges_gapAlg (hgap : gapAll F hd E padU ∈ FP) (x : List Bool) :
    (gapAlg F hd E padU hgap).numEdges x = gEdges (gapAll F hd E padU x) := rfl

@[simp] theorem width_gapAlg (hgap : gapAll F hd E padU ∈ FP) :
    (gapAlg F hd E padU hgap).width = 23 := rfl

theorem vert_gapAlg_false (hgap : gapAll F hd E padU ∈ FP) (x : List Bool) (e : ℕ) :
    (gapAlg F hd E padU hgap).vert false x e = gTail (gapAll F hd E padU x) e := by
  simp only [gapAlg, Bool.cond_false]

theorem vert_gapAlg_true (hgap : gapAll F hd E padU ∈ FP) (x : List Bool) (e : ℕ) :
    (gapAlg F hd E padU hgap).vert true x e = gHead (gapAll F hd E padU x) e := by
  simp only [gapAlg, Bool.cond_true]

@[simp] theorem ok_gapAlg (hgap : gapAll F hd E padU ∈ FP) :
    (gapAlg F hd E padU hgap).ok = gapOk F hd E padU := rfl

/-! ### It models the gap graph -/

variable {Φ : List Bool → CNF}

theorem gapCodeBlk_length (hE : ∀ x, E x = (Φ x).encode) (h3 : ∀ x, CNF.Is3CNF (Φ x))
    (hmark : ∀ x, padU x = List.replicate (padU x).length true)
    (hle : ∀ x, 3 * (Φ x).length ≤ (padU x).length) (x : List Bool) (e : ℕ)
    (he : e < (gapAllG F hd padU (Φ := Φ) x).numEdges) (a : List Bool) :
    (gapCodeBlk F hd E padU (pair (pair x (List.replicate e true)) a)).length
      = codeOfRel ((gapAllG F hd padU (Φ := Φ) x).rel ⟨e, he⟩) := by
  have hcode : (recThd (pairSnd (gapAll F hd E padU x)) e).length
      = codeOfRel ((gapAllG F hd padU (Φ := Φ) x).rel ⟨e, he⟩) := by
    rw [length_recThd_sndBlock, gapAll_eq F hd E padU hE h3 hmark hle x, gCode_encGraph]
  have hlt : codeOfRel ((gapAllG F hd padU (Φ := Φ) x).rel ⟨e, he⟩) < cRel := by
    rw [cRel_eq]
    exact codeOfRel_lt _
  rw [gapCodeBlk, gapStr, pairFst_pair, pairFst_pair,
    pairSnd_pair, List.length_replicate, List.length_take, hcode]
  omega

/-- **The algorithm models the gap graph.** -/
theorem gapAlg_models (hgap : gapAll F hd E padU ∈ FP)
    (hE : ∀ x, E x = (Φ x).encode) (h3 : ∀ x, CNF.Is3CNF (Φ x))
    (hmark : ∀ x, padU x = List.replicate (padU x).length true)
    (hle : ∀ x, 3 * (Φ x).length ≤ (padU x).length) :
    (gapAlg F hd E padU hgap).Models (fun x => gapAllG F hd padU (Φ := Φ) x)
      (symEnc DinurAlpha 23) (symDec DinurAlpha) where
  numEdges_eq x := by
    rw [numEdges_gapAlg, gapAll_eq F hd E padU hE h3 hmark hle x, gEdges_encGraph]
  tail_eq x e he := by
    rw [vert_gapAlg_false, gapAll_eq F hd E padU hE h3 hmark hle x, gTail_encGraph _ e he]
  head_eq x e he := by
    rw [vert_gapAlg_true, gapAll_eq F hd E padU hE h3 hmark hle x, gHead_encGraph _ e he]
  length_enc := length_symEnc_gapAlpha
  dec_enc := symDec_symEnc_gapAlpha
  ok_iff x e he u v hu hv := by
    rw [width_gapAlg] at hu hv
    have ha : (u ++ v).length = 46 := by
      rw [List.length_append, hu, hv]
    have htake : (u ++ v).take 23 = u := by
      rw [← hu, List.take_left]
    have hdrop : (u ++ v).drop 23 = v := by
      rw [← hu, List.drop_left]
    have hcode := gapCodeBlk_length F hd E padU hE h3 hmark hle x e he (u ++ v)
    have htake46 : (u ++ v).take 46 = u ++ v := List.take_of_length_le (by omega)
    show gapOkPred (gapOkKey F hd E padU (pair (pair x (List.replicate e true)) (u ++ v))) ↔ _
    rw [gapOkPred, gapOkKey, pairFst_pair, pairSnd_pair, hcode,
      pairSnd_pair, htake46, htake, hdrop, relOfCode_codeOfRel]

end Complexity
