/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.CNFMaxVar
public import Complexitylib.Classes.PCP.Internal.GapReduction
public import Complexitylib.Classes.PCP.Internal.FiniteKey
public import Complexitylib.Classes.PCP.Internal.SymbolCodec
public import Complexitylib.Classes.PCP.Internal.CSPVerifier
public import Complexitylib.Classes.PCP.Internal.AlgCSPModel

/-!
# The base graph, as an algorithm sees it

The constraint graph of a 3CNF formula has three edges per clause, a vertex per
variable and a vertex per clause. This module computes those numbers and those
endpoints from the formula's encoding, in polynomial time.

The vertex numbering puts variables first, so a clause vertex sits at
`maxVar + 1 + j`; both quantities are read off the encoding by the loops of
`MaxLoop` and the parser.

## Main definitions

- `Complexity.baseEdgesU` — the edge count, in unary
- `Complexity.baseMaxU` — the largest variable index, in unary

## Main results

- `Complexity.baseEdgesU_eq`, `Complexity.baseMaxU_eq` — what they compute
- `Complexity.baseTailU_eq`, `Complexity.baseHeadU_eq` — the two endpoints
- `Complexity.baseKey_mem_FP`, `Complexity.length_baseKey_le` — the constraint's
  bounded key
- `Complexity.baseOk_mem_P` — the constraint is polynomial-time decidable
- `Complexity.baseAlg` — the base graph as an `AlgCSP`
- `Complexity.baseAlg_numEdges_eq`, `Complexity.baseAlg_tail_eq`,
  `Complexity.baseAlg_head_eq` — it agrees with `baseCSP`
- `Complexity.card_gapAlpha` — the alphabet fits in `23` bits
- `Complexity.litSignFn_encode` — the sign flag is the literal's sign
- `Complexity.baseAlg_models` — the base graph is modelled faithfully
-/

@[expose] public section

namespace Complexity

open SAT ThreeSATCSP

variable (E : List Bool → List Bool)

/-- The number of edges, in unary: three per clause. -/
noncomputable def baseEdgesU (z : List Bool) : List Bool :=
  clauseCountFn (E z) ++ clauseCountFn (E z) ++ clauseCountFn (E z)

theorem baseEdgesU_mem_FP (hE : E ∈ FP) : baseEdgesU E ∈ FP := by
  have hc : (fun z => clauseCountFn (E z)) ∈ FP := by
    have := mem_FP_comp hE clauseCountFn_mem_FP
    refine mem_FP_of_eq this fun z => ?_
    rw [Function.comp_apply]
  exact Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP hc hc) hc

theorem baseEdgesU_eq {Φ : List Bool → CNF} (hE : ∀ x, E x = (Φ x).encode) (x : List Bool) :
    baseEdgesU E x = List.replicate (3 * (Φ x).length) true := by
  rw [baseEdgesU, hE, clauseCountFn_eq (even_length_encode _), sepCount_encode]
  rw [← List.replicate_add, ← List.replicate_add]
  congr 1
  ring

/-- The largest variable index, in unary. -/
noncomputable def baseMaxU (z : List Bool) : List Bool :=
  maxFn slotVar (pair (baseEdgesU E z) (E z))

theorem baseMaxU_mem_FP (hE : E ∈ FP) : baseMaxU E ∈ FP := by
  have hpair : (fun z => pair (baseEdgesU E z) (E z)) ∈ FP :=
    Cobham.pairFn_mem_FP (baseEdgesU_mem_FP E hE) hE
  have := mem_FP_comp hpair (maxFn_mem_FP slotVar_mem_FP)
  refine mem_FP_of_eq this fun z => ?_
  rw [Function.comp_apply, baseMaxU]

theorem baseMaxU_eq {Φ : List Bool → CNF} (hE : ∀ x, E x = (Φ x).encode)
    (h3 : ∀ x, CNF.Is3CNF (Φ x)) (x : List Bool) :
    (baseMaxU E x).length = (Φ x).maxVar := by
  rw [baseMaxU, baseEdgesU_eq E hE, hE, maxFn_eq, maxOver_slotVar _ (h3 x)]

/-- The unary form of the first endpoint: the clause vertex. -/
noncomputable def baseTailU (w : List Bool) : List Bool :=
  baseMaxU E (pairFst w) ++ [true]
    ++ List.replicate (divFn [false, false, false] (pairSnd w)).length true

/-- The unary form of the second endpoint: the variable vertex. -/
noncomputable def baseHeadU (w : List Bool) : List Bool :=
  slotVar (pair (E (pairFst w)) (pairSnd w))

theorem baseTailU_mem_FP (hE : E ∈ FP) : baseTailU E ∈ FP := by
  have hm : (fun w => baseMaxU E (pairFst w)) ∈ FP := by
    have := mem_FP_comp Cobham.fstBlock_mem_FP (baseMaxU_mem_FP E hE)
    refine mem_FP_of_eq this fun w => ?_
    rw [Function.comp_apply]
  have hd : (fun w : List Bool =>
      List.replicate (divFn [false, false, false] (pairSnd w)).length true) ∈ FP := by
    have h1 : (fun w : List Bool => divFn [false, false, false] (pairSnd w)) ∈ FP := by
      have := mem_FP_comp Cobham.sndBlock_mem_FP (divFn_mem_FP [false, false, false])
      refine mem_FP_of_eq this fun w => ?_
      rw [Function.comp_apply]
    have := mem_FP_comp h1 unaryLength_mem_FP
    refine mem_FP_of_eq this fun w => ?_
    rw [Function.comp_apply]
  exact Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP hm (constFn_mem_FP [true])) hd

theorem baseHeadU_mem_FP (hE : E ∈ FP) : baseHeadU E ∈ FP := by
  have hp : (fun w => pair (E (pairFst w)) (pairSnd w)) ∈ FP := by
    refine Cobham.pairFn_mem_FP ?_ Cobham.sndBlock_mem_FP
    have := mem_FP_comp Cobham.fstBlock_mem_FP hE
    refine mem_FP_of_eq this fun w => ?_
    rw [Function.comp_apply]
  have := mem_FP_comp hp slotVar_mem_FP
  refine mem_FP_of_eq this fun w => ?_
  rw [Function.comp_apply, baseHeadU]

/-! ### What the endpoints compute -/

theorem baseTailU_eq {Φ : List Bool → CNF} (hE : ∀ x, E x = (Φ x).encode)
    (h3 : ∀ x, CNF.Is3CNF (Φ x)) (x : List Bool) (e : ℕ) :
    (baseTailU E (pair x (List.replicate e true))).length
      = ((Φ x).maxVar + 1) + e / 3 := by
  rw [baseTailU, pairFst_pair, pairSnd_pair, List.length_append,
    List.length_append, List.length_replicate, List.length_singleton,
    divFn_eq (by simp) (List.replicate e true), List.length_replicate,
    List.length_replicate, baseMaxU_eq E hE h3]
  congr 1

theorem baseHeadU_eq {Φ : List Bool → CNF} (hE : ∀ x, E x = (Φ x).encode)
    (h3 : ∀ x, CNF.Is3CNF (Φ x)) (x : List Bool) {e : ℕ} (he : e < 3 * (Φ x).length) :
    (baseHeadU E (pair x (List.replicate e true))).length
      = (litOf (Φ x) (e / 3) ⟨e % 3, Nat.mod_lt _ (by omega)⟩).var := by
  have hj : e / 3 < (Φ x).length := by omega
  have hp : e % 3 < ((Φ x)[e / 3]'hj).length := by
    rw [h3 x _ (List.getElem_mem hj)]
    omega
  rw [baseHeadU, pairFst_pair, pairSnd_pair, hE,
    slotVar_eq (Φ x) hj hp rfl rfl]
  congr 1
  rw [litOf, List.getElem?_eq_getElem hj]
  simp only [Option.getD_some]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
  rfl

/-! ### The key the constraint looks at -/

/-- The three literal signs of the clause an edge belongs to. -/
noncomputable def baseSigns (z : List Bool) : List Bool :=
  let j := divFn [false, false, false] (pairSnd (pairFst z))
  let x := pairFst (pairFst z)
  litSignFn (pair (pair j []) (E x))
    ++ litSignFn (pair (pair j [true]) (E x))
    ++ litSignFn (pair (pair j [true, true]) (E x))

/-- Everything the constraint depends on: the clause's signs, the position
inside the clause, and the two symbol blocks. -/
noncomputable def baseKey (w : ℕ) (z : List Bool) : List Bool :=
  pair (pair (baseSigns E z)
      (modFn [false, false, false] (pairSnd (pairFst z))))
    ((pairSnd z).take (2 * w))

theorem baseSigns_mem_FP (hE : E ∈ FP) : baseSigns E ∈ FP := by
  have hx : (fun z : List Bool => E (pairFst (pairFst z))) ∈ FP := by
    have := mem_FP_comp (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP) hE
    refine mem_FP_of_eq this fun z => ?_
    rw [Function.comp_apply, Function.comp_apply]
  have hj : (fun z : List Bool =>
      divFn [false, false, false] (pairSnd (pairFst z))) ∈ FP := by
    have := mem_FP_comp (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP)
      (divFn_mem_FP [false, false, false])
    refine mem_FP_of_eq this fun z => ?_
    rw [Function.comp_apply, Function.comp_apply]
  have hsign : ∀ c : List Bool, (fun z : List Bool =>
      litSignFn (pair (pair (divFn [false, false, false]
        (pairSnd (pairFst z))) c)
        (E (pairFst (pairFst z))))) ∈ FP := by
    intro c
    have := mem_FP_comp
      (Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP hj (constFn_mem_FP c)) hx) litSignFn_mem_FP
    refine mem_FP_of_eq this fun z => ?_
    rw [Function.comp_apply]
  exact Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP (hsign []) (hsign [true]))
    (hsign [true, true])

theorem baseKey_mem_FP (hE : E ∈ FP) (w : ℕ) : baseKey E w ∈ FP := by
  have hm : (fun z : List Bool =>
      modFn [false, false, false] (pairSnd (pairFst z))) ∈ FP := by
    have := mem_FP_comp (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP)
      (modFn_mem_FP [false, false, false])
    refine mem_FP_of_eq this fun z => ?_
    rw [Function.comp_apply, Function.comp_apply]
  have ht : (fun z : List Bool => (pairSnd z).take (2 * w)) ∈ FP := by
    have := Cobham.takeLenFn_mem_FP
      (constFn_mem_FP (List.replicate (2 * w) false)) Cobham.sndBlock_mem_FP
    refine mem_FP_of_eq this fun z => ?_
    rw [List.length_replicate]
  exact Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP (baseSigns_mem_FP E hE) hm) ht

theorem length_baseSigns_le (z : List Bool) : (baseSigns E z).length ≤ 3 := by
  have hs : ∀ y, (litSignFn y).length ≤ 1 := by
    intro y
    rw [litSignFn, Cobham.selectHead]
    split
    · simp
    · split <;> simp
  rw [baseSigns, List.length_append, List.length_append]
  have h1 := hs (pair (pair (divFn [false, false, false]
    (pairSnd (pairFst z))) []) (E (pairFst (pairFst z))))
  have h2 := hs (pair (pair (divFn [false, false, false]
    (pairSnd (pairFst z))) [true]) (E (pairFst (pairFst z))))
  have h3 := hs (pair (pair (divFn [false, false, false]
    (pairSnd (pairFst z))) [true, true])
    (E (pairFst (pairFst z))))
  omega

theorem length_baseKey_le (w : ℕ) (z : List Bool) :
    (baseKey E w z).length ≤ 2 * w + 22 := by
  have hs := length_baseSigns_le E z
  have hm : (modFn [false, false, false]
      (pairSnd (pairFst z))).length ≤ 2 := by
    rw [modFn_eq (by simp)]
    simp only [List.length_replicate,
      show ([false, false, false] : List Bool).length = 3 from rfl]
    omega
  have ht : ((pairSnd z).take (2 * w)).length ≤ 2 * w := by
    rw [List.length_take]
    omega
  rw [baseKey, pair_length, pair_length]
  omega

/-! ### The constraint -/

open Classical in
/-- What the constraint says, as a predicate of the key alone: the two blocks
name symbols in the image of the alphabet embedding whose preimages satisfy the
clause and agree on the checked position. -/
noncomputable def baseOkKey (w : ℕ) (k : List Bool) : Prop :=
  ∃ a₁ a₂ : Fin 3 → Bool,
    alphaEmb a₁ = symDec GapAlpha ((pairSnd k).take w) ∧
    alphaEmb a₂ = symDec GapAlpha ((pairSnd k).drop w) ∧
    (∃ q : Fin 3, a₁ q = (pairFst (pairFst k)).getD q.val false) ∧
    a₁ ⟨(pairSnd (pairFst k)).length % 3,
      Nat.mod_lt _ (by omega)⟩ = a₂ 0

/-- The constraint, as a language on the verifier's verdict argument. -/
noncomputable def baseOk (w : ℕ) : Language :=
  {z : List Bool | baseOkKey w (baseKey E w z)}

theorem baseOk_mem_P (hE : E ∈ FP) (w : ℕ) : baseOk E w ∈ P :=
  mem_P_of_bounded_key (baseKey_mem_FP E hE w) (length_baseKey_le E w) (baseOkKey w)

/-! ### The record -/

/-- **The base graph as an algorithm.** -/
noncomputable def baseAlg (hE : E ∈ FP) : AlgCSP where
  numEdges x := (baseEdgesU E x).length
  numEdges_mem := by
    have := mem_FP_comp (baseEdgesU_mem_FP E hE) unaryLength_mem_FP
    refine mem_FP_of_eq this fun x => ?_
    rw [Function.comp_apply]
  width := 23
  width_pos := by omega
  vert b x e :=
    cond b (baseHeadU E (pair x (List.replicate e true))).length
      (baseTailU E (pair x (List.replicate e true))).length
  vert_mem := by
    intro b
    have hu : (fun w : List Bool => List.replicate (pairSnd w).length true) ∈ FP := by
      have := mem_FP_comp Cobham.sndBlock_mem_FP unaryLength_mem_FP
      refine mem_FP_of_eq this fun w => ?_
      rw [Function.comp_apply]
    have harg : (fun w : List Bool =>
        pair (pairFst w) (List.replicate (pairSnd w).length true)) ∈ FP :=
      Cobham.pairFn_mem_FP Cobham.fstBlock_mem_FP hu
    cases b
    · have := mem_FP_comp (mem_FP_comp harg (baseTailU_mem_FP E hE)) unaryLength_mem_FP
      refine mem_FP_of_eq this fun w => ?_
      rw [Function.comp_apply, Function.comp_apply]
      simp only [Bool.cond_false]
    · have := mem_FP_comp (mem_FP_comp harg (baseHeadU_mem_FP E hE)) unaryLength_mem_FP
      refine mem_FP_of_eq this fun w => ?_
      rw [Function.comp_apply, Function.comp_apply]
      simp only [Bool.cond_true]
  ok := baseOk E 23
  ok_mem := baseOk_mem_P E hE 23

@[simp] theorem numEdges_baseAlg (hE : E ∈ FP) (x : List Bool) :
    (baseAlg E hE).numEdges x = (baseEdgesU E x).length := rfl

@[simp] theorem width_baseAlg (hE : E ∈ FP) : (baseAlg E hE).width = 23 := rfl

theorem vert_baseAlg_false (hE : E ∈ FP) (x : List Bool) (e : ℕ) :
    (baseAlg E hE).vert false x e
      = (baseTailU E (pair x (List.replicate e true))).length := by
  simp only [baseAlg, Bool.cond_false]

theorem vert_baseAlg_true (hE : E ∈ FP) (x : List Bool) (e : ℕ) :
    (baseAlg E hE).vert true x e
      = (baseHeadU E (pair x (List.replicate e true))).length := by
  simp only [baseAlg, Bool.cond_true]

@[simp] theorem ok_baseAlg (hE : E ∈ FP) : (baseAlg E hE).ok = baseOk E 23 := rfl

/-! ### The symbol codec fits -/

theorem card_gapAlpha : Fintype.card GapAlpha = 2 ^ 23 := by
  show Fintype.card (ZMod 2 × (ReadIdx → ZMod 2)) = 2 ^ 23
  rw [Fintype.card_prod, Fintype.card_fun, ZMod.card, card_readIdx]
  norm_num

theorem length_symEnc_gapAlpha (s : GapAlpha) : (symEnc GapAlpha 23 s).length = 23 :=
  length_symEnc 23 s

theorem symDec_symEnc_gapAlpha (s : GapAlpha) :
    symDec GapAlpha (symEnc GapAlpha 23 s) = s :=
  symDec_symEnc (by rw [card_gapAlpha]) s

/-! ### The sign flag -/

theorem litSignFn_encode (φ : CNF) {j p : ℕ} (hj : j < φ.length)
    (hp : p < (φ[j]'hj).length) :
    litSignFn (pair (pair (List.replicate j true) (List.replicate p true)) φ.encode)
      = [((φ[j]'hj)[p]'hp).sign] := by
  have hseg : litSegFn (pair (pair (List.replicate j true) (List.replicate p true)) φ.encode)
      = encodeTokens (Lit.rawTokens ((φ[j]'hj)[p]'hp)) := litSegFn_encode φ hj hp
  have hhead : encodeTokens (Lit.rawTokens ((φ[j]'hj)[p]'hp))
      = ((φ[j]'hj)[p]'hp).sign :: ((φ[j]'hj)[p]'hp).sign
        :: encodeTokens ((Lit.encodeRaw ((φ[j]'hj)[p]'hp)).tail.map EncToken.bit) := by
    rw [Lit.rawTokens, Lit.encodeRaw]
    simp only [List.map_cons, List.tail_cons]
    rw [encodeTokens_cons]
    cases h : ((φ[j]'hj)[p]'hp).sign <;> rfl
  rw [litSignFn, hseg, hhead, selectHead_cons]
  cases ((φ[j]'hj)[p]'hp).sign <;> simp

theorem litOf_eq (φ : CNF) {j : ℕ} (hj : j < φ.length) (p : Fin 3)
    (hq : p.val < (φ[j]'hj).length) : litOf φ j p = (φ[j]'hj)[p.val]'hq := by
  rw [litOf, List.getElem?_eq_getElem hj]
  simp only [Option.getD_some]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  rfl

/-! ### Agreement with the real graph -/

variable {Φ : List Bool → CNF}

theorem baseAlg_numEdges_eq (hE' : E ∈ FP) (hE : ∀ x, E x = (Φ x).encode) (x : List Bool) :
    (baseAlg E hE').numEdges x = (baseCSP (Φ x)).numEdges := by
  rw [numEdges_baseAlg, baseEdgesU_eq E hE, List.length_replicate, numEdges_baseCSP]

theorem baseAlg_tail_eq (hE' : E ∈ FP) (hE : ∀ x, E x = (Φ x).encode)
    (h3 : ∀ x, CNF.Is3CNF (Φ x)) (x : List Bool) (e : ℕ)
    (he : e < (baseCSP (Φ x)).numEdges) :
    (baseAlg E hE').vert false x e = ((baseCSP (Φ x)).tail ⟨e, he⟩).val := by
  rw [numEdges_baseCSP] at he
  rw [vert_baseAlg_false, baseTailU_eq E hE h3]
  show _ = (clauseVertex (Φ x) (edgeClause e)).val
  rw [clauseVertex, edgeClause, dite_eq_left (by rw [numVerts]; omega)]

theorem baseAlg_head_eq (hE' : E ∈ FP) (hE : ∀ x, E x = (Φ x).encode)
    (h3 : ∀ x, CNF.Is3CNF (Φ x)) (x : List Bool) (e : ℕ)
    (he : e < (baseCSP (Φ x)).numEdges) :
    (baseAlg E hE').vert true x e = ((baseCSP (Φ x)).head ⟨e, he⟩).val := by
  rw [numEdges_baseCSP] at he
  have hj : e / 3 < (Φ x).length := by omega
  have hp : e % 3 < ((Φ x)[e / 3]'hj).length := by
    rw [h3 x _ (List.getElem_mem hj)]
    omega
  have hlit : litOf (Φ x) (e / 3) ⟨e % 3, Nat.mod_lt _ (by omega)⟩
      = ((Φ x)[e / 3]'hj)[e % 3]'hp := by
    rw [litOf, List.getElem?_eq_getElem hj]
    simp only [Option.getD_some]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
    rfl
  have hvar : (litOf (Φ x) (e / 3) ⟨e % 3, Nat.mod_lt _ (by omega)⟩).var ≤ (Φ x).maxVar := by
    rw [hlit]
    exact var_le_maxVar (Φ x) hj hp
  rw [vert_baseAlg_true, baseHeadU_eq E hE h3 x he]
  show _ = (varVertex (Φ x) (litOf (Φ x) (edgeClause e) (edgePos e)).var).val
  rw [varVertex, edgeClause, edgePos, dite_eq_left (by rw [numVerts]; omega)]

/-! ### The key on a well-formed argument -/

theorem baseSigns_pair (hE : ∀ x, E x = (Φ x).encode) (h3 : ∀ x, CNF.Is3CNF (Φ x))
    (x : List Bool) {e : ℕ} (he : e < 3 * (Φ x).length) (a : List Bool) :
    baseSigns E (pair (pair x (List.replicate e true)) a)
      = [(litOf (Φ x) (e / 3) 0).sign, (litOf (Φ x) (e / 3) 1).sign,
         (litOf (Φ x) (e / 3) 2).sign] := by
  have hj : e / 3 < (Φ x).length := by omega
  have hlen : ((Φ x)[e / 3]'hj).length = 3 := h3 x _ (List.getElem_mem hj)
  have hsign : ∀ q : Fin 3,
      litSignFn (pair (pair (List.replicate (e / 3) true)
        (List.replicate q.val true)) (E x)) = [(litOf (Φ x) (e / 3) q).sign] := by
    intro q
    have hq : q.val < ((Φ x)[e / 3]'hj).length := by
      rw [hlen]
      exact q.isLt
    rw [hE, litSignFn_encode (Φ x) hj hq, litOf_eq (Φ x) hj q hq]
  rw [baseSigns, pairFst_pair, pairSnd_pair, pairFst_pair,
    divFn_eq (by simp) (List.replicate e true), List.length_replicate,
    show ([false, false, false] : List Bool).length = 3 from rfl]
  have h0 : litSignFn (pair (pair (List.replicate (e / 3) true) []) (E x))
      = [(litOf (Φ x) (e / 3) 0).sign] := hsign 0
  have h1 : litSignFn (pair (pair (List.replicate (e / 3) true) [true]) (E x))
      = [(litOf (Φ x) (e / 3) 1).sign] := hsign 1
  have h2 : litSignFn (pair (pair (List.replicate (e / 3) true) [true, true]) (E x))
      = [(litOf (Φ x) (e / 3) 2).sign] := hsign 2
  rw [h0, h1, h2]
  rfl

theorem baseKey_pair (hE : ∀ x, E x = (Φ x).encode) (h3 : ∀ x, CNF.Is3CNF (Φ x))
    (x : List Bool) {e : ℕ} (he : e < 3 * (Φ x).length) {a : List Bool}
    (ha : a.length = 46) :
    baseKey E 23 (pair (pair x (List.replicate e true)) a)
      = pair (pair [(litOf (Φ x) (e / 3) 0).sign, (litOf (Φ x) (e / 3) 1).sign,
          (litOf (Φ x) (e / 3) 2).sign] (List.replicate (e % 3) true)) a := by
  rw [baseKey, baseSigns_pair E hE h3 x he a, pairFst_pair, pairSnd_pair,
    pairSnd_pair, modFn_eq (by simp) (List.replicate e true),
    List.length_replicate, show ([false, false, false] : List Bool).length = 3 from rfl,
    List.take_of_length_le (by omega)]

/-! ### The constraint agrees -/

set_option maxRecDepth 8000 in
theorem baseAlg_ok_iff (hE' : E ∈ FP) (hE : ∀ x, E x = (Φ x).encode)
    (h3 : ∀ x, CNF.Is3CNF (Φ x)) (x : List Bool) (e : ℕ)
    (he : e < (baseCSP (Φ x)).numEdges) (u v : List Bool)
    (hu : u.length = 23) (hv : v.length = 23) :
    pair (pair x (List.replicate e true)) (u ++ v) ∈ (baseAlg E hE').ok
      ↔ (baseCSP (Φ x)).rel ⟨e, he⟩ (symDec GapAlpha u) (symDec GapAlpha v) = true := by
  have he' : e < 3 * (Φ x).length := by
    rw [numEdges_baseCSP] at he
    exact he
  have ha : (u ++ v).length = 46 := by
    rw [List.length_append, hu, hv]
  have htake : (u ++ v).take 23 = u := by
    rw [← hu, List.take_left]
  have hdrop : (u ++ v).drop 23 = v := by
    rw [← hu, List.drop_left]
  have hmod : e % 3 % 3 = e % 3 := by omega
  show baseOkKey 23 (baseKey E 23 (pair (pair x (List.replicate e true)) (u ++ v))) ↔ _
  rw [baseKey_pair E hE h3 x he' ha]
  show _ ↔ (ConstraintGraph.lift (toGraph (Φ x)) alphaEmb).rel ⟨e, he⟩ _ _ = true
  rw [ConstraintGraph.rel_lift, decide_eq_true_iff]
  simp only [baseOkKey, pairSnd_pair, pairFst_pair, htake, hdrop,
    List.length_replicate, hmod]
  have hsign : ∀ q : Fin 3,
      ([(litOf (Φ x) (e / 3) 0).sign, (litOf (Φ x) (e / 3) 1).sign,
        (litOf (Φ x) (e / 3) 2).sign].getD q.val false) = (litOf (Φ x) (e / 3) q).sign := by
    intro q
    fin_cases q <;> rfl
  have hpos : edgePos e = ⟨e % 3, Nat.mod_lt _ (by omega)⟩ := rfl

  constructor
  · rintro ⟨a₁, a₂, h1, h2, ⟨q, hq⟩, hagree⟩
    refine ⟨a₁, a₂, h1, h2, ?_⟩
    show (clauseSat (Φ x) (edgeClause e) a₁ && (a₁ (edgePos e) == a₂ 0)) = true
    rw [Bool.and_eq_true, clauseSat_eq_true_iff, beq_iff_eq, hpos]
    exact ⟨⟨q, by rw [hq, hsign, edgeClause]⟩, hagree⟩
  · rintro ⟨a₁, a₂, h1, h2, hr⟩
    replace hr : (clauseSat (Φ x) (edgeClause e) a₁ && (a₁ (edgePos e) == a₂ 0)) = true := hr
    rw [Bool.and_eq_true, clauseSat_eq_true_iff, beq_iff_eq, hpos] at hr
    obtain ⟨⟨q, hq⟩, hagree⟩ := hr
    exact ⟨a₁, a₂, h1, h2, ⟨q, by rw [hq, hsign, edgeClause]⟩, hagree⟩

/-- **The base graph is modelled faithfully.** -/
theorem baseAlg_models (hE' : E ∈ FP) (hE : ∀ x, E x = (Φ x).encode)
    (h3 : ∀ x, CNF.Is3CNF (Φ x)) :
    (baseAlg E hE').Models (fun x => baseCSP (Φ x)) (symEnc GapAlpha 23)
      (symDec GapAlpha) where
  numEdges_eq := baseAlg_numEdges_eq E hE' hE
  tail_eq := baseAlg_tail_eq E hE' hE h3
  head_eq := baseAlg_head_eq E hE' hE h3
  length_enc := length_symEnc_gapAlpha
  dec_enc := symDec_symEnc_gapAlpha
  ok_iff := fun x e he u v hu hv => baseAlg_ok_iff E hE' hE h3 x e he u v hu hv

end Complexity
