/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.BaseAlg
public import Complexitylib.Classes.PCP.Internal.AlgGraph
public import Complexitylib.Classes.PCP.Internal.PadGraph

/-!
# The starting graph, written out

`BaseAlg` reads the starting graph's numbers straight off a formula, which is
all a verifier needs. Amplification needs more: the graph itself, as a string
the round function can consume. This module writes it, reusing that module's
readers.

An edge's constraint depends on the formula only through the three signs of its
clause and which of the three positions the edge checks — twelve bits in all.
That is what `baseCodeKey` extracts and `relOfSigns` turns back into a
constraint, so the constraint's code is written by a table lookup.

## Main definitions

- `Complexity.relOfSigns` — an edge's constraint, as a function of the signs
- `Complexity.baseCodeKey` — the bounded data an edge's constraint depends on
- `Complexity.baseGraphFn` — the starting graph, as a string

## Main results

- `Complexity.rel_baseCSP` — the constraint depends only on the signs
- `Complexity.baseGraphFn_mem_FP` — writing the graph is polynomial-time
- `Complexity.baseGraphFn_eq` — it writes the right graph
-/

@[expose] public section

namespace Complexity

open SAT ThreeSATCSP

variable (E : List Bool → List Bool)

/-! ### The constraint, from the signs alone -/

open Classical in
/-- The constraint of an edge that checks position `p` of a clause whose three
literals have signs `s`: both endpoints name triples in the image of the
alphabet embedding, the first satisfies the clause, and the two agree on the
checked position. -/
noncomputable def relOfSigns (s : Fin 3 → Bool) (p : Fin 3) : GapAlpha → GapAlpha → Bool :=
  fun u v => decide (∃ a₁ a₂ : Fin 3 → Bool, alphaEmb a₁ = u ∧ alphaEmb a₂ = v ∧
    (∃ q : Fin 3, a₁ q = s q) ∧ a₁ p = a₂ 0)

/-- **The constraint depends only on the signs.** -/
theorem rel_baseCSP (φ : CNF) (e : ℕ) (he : e < (baseCSP φ).numEdges) :
    (baseCSP φ).rel ⟨e, he⟩
      = relOfSigns (fun q => (litOf φ (e / 3) q).sign) ⟨e % 3, Nat.mod_lt _ (by omega)⟩ := by
  funext u v
  show (ConstraintGraph.lift (toGraph φ) alphaEmb).rel ⟨e, he⟩ u v = _
  rw [ConstraintGraph.rel_lift, relOfSigns]
  refine decide_eq_decide.mpr ⟨?_, ?_⟩
  · rintro ⟨a₁, a₂, h1, h2, hr⟩
    replace hr : (clauseSat φ (edgeClause e) a₁ && (a₁ (edgePos e) == a₂ 0)) = true := hr
    rw [Bool.and_eq_true, clauseSat_eq_true_iff, beq_iff_eq] at hr
    exact ⟨a₁, a₂, h1, h2, hr.1, hr.2⟩
  · rintro ⟨a₁, a₂, h1, h2, hq, hagree⟩
    refine ⟨a₁, a₂, h1, h2, ?_⟩
    show (clauseSat φ (edgeClause e) a₁ && (a₁ (edgePos e) == a₂ 0)) = true
    rw [Bool.and_eq_true, clauseSat_eq_true_iff, beq_iff_eq]
    exact ⟨hq, hagree⟩

/-! ### The key -/

/-- The data an edge's constraint depends on: the clause's three signs and
which of them the edge reads. -/
noncomputable def baseCodeKey (w : List Bool) : List Bool :=
  pair (baseSigns E (pair w []))
    (modFn [false, false, false] (pairSnd w))

theorem baseCodeKey_mem_FP (hE : E ∈ FP) : baseCodeKey E ∈ FP := by
  have harg : (fun w : List Bool => pair w []) ∈ FP :=
    Cobham.pairFn_mem_FP id_mem_FP (constFn_mem_FP [])
  have hsigns : (fun w : List Bool => baseSigns E (pair w [])) ∈ FP := by
    refine mem_FP_of_eq (mem_FP_comp harg (baseSigns_mem_FP E hE)) fun w => ?_
    rw [Function.comp_apply]
  have hmod : (fun w : List Bool => modFn [false, false, false] (pairSnd w)) ∈ FP := by
    refine mem_FP_of_eq (mem_FP_comp Cobham.sndBlock_mem_FP
      (modFn_mem_FP [false, false, false])) fun w => ?_
    rw [Function.comp_apply]
  exact Cobham.pairFn_mem_FP hsigns hmod

theorem baseCodeKey_length_le (w : List Bool) : (baseCodeKey E w).length ≤ 12 := by
  have hs : (baseSigns E (pair w [])).length ≤ 3 := length_baseSigns_le E _
  have hm : (modFn [false, false, false] (pairSnd w)).length ≤ 2 := by
    rw [modFn_eq (by simp), List.length_replicate]
    have : (pairSnd w).length % [false, false, false].length < 3 := by
      simpa using Nat.mod_lt _ (by omega)
    omega
  rw [baseCodeKey, pair_length]
  omega

variable {Φ : List Bool → CNF}

theorem baseCodeKey_pair (hE : ∀ x, E x = (Φ x).encode) (h3 : ∀ x, CNF.Is3CNF (Φ x))
    (x : List Bool) {e : ℕ} (he : e < 3 * (Φ x).length) :
    baseCodeKey E (pair x (List.replicate e true))
      = pair [(litOf (Φ x) (e / 3) 0).sign, (litOf (Φ x) (e / 3) 1).sign,
          (litOf (Φ x) (e / 3) 2).sign] (List.replicate (e % 3) true) := by
  rw [baseCodeKey, baseSigns_pair E hE h3 x he [], pairSnd_pair,
    modFn_eq (by simp) (List.replicate e true), List.length_replicate,
    show ([false, false, false] : List Bool).length = 3 from rfl]

/-! ### The constraint's code, from the key -/

/-- The constraint an edge's key stands for. -/
noncomputable def baseRelOfKey (k : List Bool) : GapAlpha → GapAlpha → Bool :=
  relOfSigns (fun q => (pairFst k).getD q.val false)
    ⟨(pairSnd k).length % 3, Nat.mod_lt _ (by omega)⟩

/-- The constraint's code, in unary, from the key. -/
noncomputable def baseCodeFn (k : List Bool) : List Bool :=
  List.replicate (codeOfRel (baseRelOfKey k)) true

theorem relOfSigns_congr {s t : Fin 3 → Bool} {m n : ℕ} (hm : m < 3) (hn : n < 3)
    (hs : s = t) (h : m = n) : relOfSigns s ⟨m, hm⟩ = relOfSigns t ⟨n, hn⟩ := by
  subst hs
  subst h
  rfl

theorem baseCodeFn_codeKey (hE : ∀ x, E x = (Φ x).encode) (h3 : ∀ x, CNF.Is3CNF (Φ x))
    (x : List Bool) (e : ℕ) (he : e < (baseCSP (Φ x)).numEdges) :
    baseCodeFn (baseCodeKey E (pair x (List.replicate e true)))
      = List.replicate (codeOfRel ((baseCSP (Φ x)).rel ⟨e, he⟩)) true := by
  have he' : e < 3 * (Φ x).length := by rwa [numEdges_baseCSP] at he
  have hrel : baseRelOfKey (baseCodeKey E (pair x (List.replicate e true)))
      = relOfSigns (fun q => (litOf (Φ x) (e / 3) q).sign)
          ⟨e % 3, Nat.mod_lt _ (by omega)⟩ := by
    rw [baseRelOfKey]
    refine relOfSigns_congr _ _ ?_ ?_
    · rw [baseCodeKey_pair E hE h3 x he', pairFst_pair]
      funext q
      fin_cases q <;> rfl
    · rw [baseCodeKey_pair E hE h3 x he', pairSnd_pair, List.length_replicate]
      omega
  rw [baseCodeFn, hrel, rel_baseCSP]

/-! ### The counts -/

/-- The number of vertices, in unary: one per variable, one per clause. -/
noncomputable def baseVertsU (z : List Bool) : List Bool :=
  marks (baseMaxU E z) ++ [true] ++ divC 3 (baseEdgesU E z)

theorem baseVertsU_mem_FP (hE : E ∈ FP) : baseVertsU E ∈ FP :=
  Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (marks_mem_FP (baseMaxU_mem_FP E hE)) (constFn_mem_FP [true]))
    (divC_mem_FP (baseEdgesU_mem_FP E hE) 3)

theorem baseVertsU_eq (hE : ∀ x, E x = (Φ x).encode) (h3 : ∀ x, CNF.Is3CNF (Φ x))
    (x : List Bool) :
    baseVertsU E x = List.replicate (baseCSP (Φ x)).numVerts true := by
  have hnv : (baseCSP (Φ x)).numVerts = ((Φ x).maxVar + 1) + (Φ x).length := rfl
  rw [baseVertsU, marks_eq, baseMaxU_eq E hE h3, baseEdgesU_eq E hE, divC_eq (by omega),
    List.length_replicate, Nat.mul_div_cancel_left _ (by omega), hnv]
  rw [show ([true] : List Bool) = List.replicate 1 true from rfl,
    ← List.replicate_add, ← List.replicate_add]

theorem baseEdgesU_count (hE : ∀ x, E x = (Φ x).encode) (x : List Bool) :
    baseEdgesU E x = List.replicate (baseCSP (Φ x)).numEdges true := by
  rw [baseEdgesU_eq E hE, numEdges_baseCSP]

/-! ### The endpoints -/

theorem baseTailU_val (hE : ∀ x, E x = (Φ x).encode) (h3 : ∀ x, CNF.Is3CNF (Φ x))
    (x : List Bool) (e : ℕ) (he : e < (baseCSP (Φ x)).numEdges) :
    (baseTailU E (pair x (List.replicate e true))).length
      = ((baseCSP (Φ x)).tail ⟨e, he⟩).val := by
  rw [numEdges_baseCSP] at he
  rw [baseTailU_eq E hE h3]
  show _ = (clauseVertex (Φ x) (edgeClause e)).val
  rw [clauseVertex, edgeClause, dite_eq_left (by rw [numVerts]; omega)]

theorem baseHeadU_val (hE : ∀ x, E x = (Φ x).encode) (h3 : ∀ x, CNF.Is3CNF (Φ x))
    (x : List Bool) (e : ℕ) (he : e < (baseCSP (Φ x)).numEdges) :
    (baseHeadU E (pair x (List.replicate e true))).length
      = ((baseCSP (Φ x)).head ⟨e, he⟩).val := by
  rw [numEdges_baseCSP] at he
  have hj : e / 3 < (Φ x).length := by omega
  have hp : e % 3 < ((Φ x)[e / 3]'hj).length := by
    rw [h3 x _ (List.getElem_mem hj)]
    omega
  have hvar : (litOf (Φ x) (e / 3) ⟨e % 3, Nat.mod_lt _ (by omega)⟩).var
      ≤ (Φ x).maxVar := by
    rw [litOf_eq (Φ x) hj _ hp]
    exact var_le_maxVar (Φ x) hj hp
  rw [baseHeadU_eq E hE h3 x he]
  show _ = (varVertex (Φ x) (litOf (Φ x) (edgeClause e) (edgePos e)).var).val
  rw [varVertex, edgeClause, edgePos, dite_eq_left (by rw [numVerts]; omega)]

/-! ### The graph -/

/-- **The starting graph, as a string.** -/
noncomputable def baseGraphFn (g : List Bool → List Bool) : List Bool → List Bool :=
  buildGraph (baseVertsU E) (baseEdgesU E)
    (fun w => encTriple (marks (baseTailU E w)) (marks (baseHeadU E w)) (g (baseCodeKey E w)))

theorem baseGraphFn_mem_FP (hE : E ∈ FP) (g : List Bool → List Bool) :
    baseGraphFn E g ∈ FP :=
  buildGraph_mem_FP (baseVertsU_mem_FP E hE) (baseEdgesU_mem_FP E hE)
    (encTriple_mem_FP (marks_mem_FP (baseTailU_mem_FP E hE))
      (marks_mem_FP (baseHeadU_mem_FP E hE))
      (mem_FP_of_bounded_key (baseCodeKey_mem_FP E hE) (baseCodeKey_length_le E) g))

/-- **The rule writes the starting graph.** -/
theorem baseGraphFn_eq (hE : ∀ x, E x = (Φ x).encode) (h3 : ∀ x, CNF.Is3CNF (Φ x))
    (x : List Bool) : baseGraphFn E baseCodeFn x = encGraph (baseCSP (Φ x)) := by
  refine buildGraph_eq (baseVertsU_eq E hE h3 x) (baseEdgesU_count E hE x) fun e he => ?_
  rw [marks_eq, marks_eq, baseTailU_val E hE h3 x e he, baseHeadU_val E hE h3 x e he,
    baseCodeFn_codeKey E hE h3 x e he]

/-! ### Padded to a fixed size -/

/-- The base graph always has a vertex. -/
theorem numVerts_baseCSP_pos (φ : CNF) : 0 < (baseCSP φ).numVerts := by
  show 0 < ((φ.maxVar + 1) + φ.length)
  omega

/-- The code of the constraint that is always true, in unary. -/
noncomputable def trivCode : List Bool :=
  List.replicate (codeOfRel (α := GapAlpha) (fun _ _ => true)) true

/-- **The starting graph, padded**: the edge count is whatever `padU` says, so it
can be made to depend on the input's length alone. -/
noncomputable def basePadFn (padU g : List Bool → List Bool) : List Bool → List Bool :=
  buildGraph (baseVertsU E) padU
    (fun w => ifLtLen (pairSnd w) (baseEdgesU E (pairFst w))
      (encTriple (marks (baseTailU E w)) (marks (baseHeadU E w)) (g (baseCodeKey E w)))
      (encTriple [] [] trivCode))

theorem basePadFn_mem_FP (hE : E ∈ FP) (hP : padU ∈ FP) (g : List Bool → List Bool) :
    basePadFn E padU g ∈ FP := by
  refine buildGraph_mem_FP (baseVertsU_mem_FP E hE) hP (ifLtLen_mem_FP Cobham.sndBlock_mem_FP
    ?_ (encTriple_mem_FP (marks_mem_FP (baseTailU_mem_FP E hE))
      (marks_mem_FP (baseHeadU_mem_FP E hE))
      (mem_FP_of_bounded_key (baseCodeKey_mem_FP E hE) (baseCodeKey_length_le E) g))
    (constFn_mem_FP _))
  exact mem_FP_of_eq (mem_FP_comp Cobham.fstBlock_mem_FP (baseEdgesU_mem_FP E hE))
    fun w => rfl

/-- **The rule writes the padded starting graph.** -/
theorem basePadFn_eq (hE : ∀ x, E x = (Φ x).encode) (h3 : ∀ x, CNF.Is3CNF (Φ x))
    (x : List Bool) (hPmark : padU x = List.replicate (padU x).length true)
    (hPle : 3 * (Φ x).length ≤ (padU x).length) :
    basePadFn E padU baseCodeFn x
      = encGraph ((baseCSP (Φ x)).padGraph (numVerts_baseCSP_pos (Φ x)) (padU x).length) := by
  have hmax : max (padU x).length (baseCSP (Φ x)).numEdges = (padU x).length := by
    rw [numEdges_baseCSP]
    omega
  refine buildGraph_eq (baseVertsU_eq E hE h3 x) ?_ fun e he => ?_
  · rw [ConstraintGraph.numEdges_padGraph, hmax]
    exact hPmark
  · rw [ConstraintGraph.numEdges_padGraph, hmax] at he
    have hcnt : (baseEdgesU E (pairFst (pair x (List.replicate e true)))).length
        = 3 * (Φ x).length := by
      rw [pairFst_pair, baseEdgesU_eq E hE, List.length_replicate]
    by_cases hlt : e < (baseCSP (Φ x)).numEdges
    · have hlt' : e < 3 * (Φ x).length := by rwa [numEdges_baseCSP] at hlt
      rw [ifLtLen_pos (by rw [pairSnd_pair, List.length_replicate, hcnt]; exact hlt')]
      rw [ConstraintGraph.tail_padGraph_of_lt _ hlt, ConstraintGraph.head_padGraph_of_lt _ hlt,
        ConstraintGraph.rel_padGraph_of_lt _ hlt]
      rw [marks_eq, marks_eq, baseTailU_val E hE h3 x e hlt, baseHeadU_val E hE h3 x e hlt,
        baseCodeFn_codeKey E hE h3 x e hlt]
    · rw [ifLtLen_neg (by rw [pairSnd_pair, List.length_replicate, hcnt,
        numEdges_baseCSP] at *; omega)]
      rw [ConstraintGraph.tail_padGraph_of_ge _ hlt, ConstraintGraph.head_padGraph_of_ge _ hlt,
        ConstraintGraph.rel_padGraph_of_ge _ hlt, trivCode]
      rfl

end Complexity
