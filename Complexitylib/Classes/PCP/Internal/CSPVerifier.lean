/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.PositionsFP
public import Complexitylib.Classes.PCP.Internal.SquareVerifier

/-!
# A verifier for a constraint graph

The verifier of a constraint graph picks an edge at random, reads the symbols
its two endpoints carry, and checks the constraint. The proof is the assignment,
written as one fixed-width block per vertex, so the queries are the two blocks.

This module packages the algorithmic content a graph must supply — how many
edges, the endpoints of an edge, and the constraint — and turns it into a
`PCPVerifier`. Nothing here is about the graph's *quality*: completeness and
soundness are hypotheses on the supplied data, discharged elsewhere by Dinur's
amplification.

## Main definitions

- `Complexity.AlgCSP` — a constraint graph presented algorithmically

## Main results

- `Complexity.AlgCSP.cntU_mem_FP`, `Complexity.AlgCSP.posU_mem_FP` — the query
  list is polynomial-time describable
- `Complexity.AlgCSP.verifier` — the verifier itself
- `Complexity.mem_PCP_of_algCSP` — a constraint graph with a gap puts its
  language in `PCP`
-/

@[expose] public section

namespace Complexity

/-- A constraint graph presented the way an algorithm sees it: a count of edges,
the endpoints of each edge, and a decidable constraint. Indices are handled in
unary, which is what a polynomial-time loop can carry. -/
structure AlgCSP where
  /-- How many edges the graph on this input has. -/
  numEdges : List Bool → ℕ
  /-- The edge count is polynomial-time computable in unary. -/
  numEdges_mem : (fun x : List Bool => List.replicate (numEdges x) true) ∈ FP
  /-- The number of bits a symbol occupies. -/
  width : ℕ
  /-- A symbol occupies at least one bit. -/
  width_pos : 0 < width
  /-- The endpoints of an edge: `false` for the first, `true` for the second. -/
  vert : Bool → List Bool → ℕ → ℕ
  /-- The endpoints are polynomial-time computable in unary. -/
  vert_mem : ∀ b, (fun w : List Bool => List.replicate
    (vert b (pairFst w) (pairSnd w).length) true) ∈ FP
  /-- The constraint, on `pair (pair x (unary e)) (the two symbol blocks)`. -/
  ok : Language
  /-- The constraint is polynomial-time decidable. -/
  ok_mem : ok ∈ P

namespace AlgCSP

variable (A : AlgCSP) (p : Polynomial ℕ)

/-- The edge a coin string names. -/
def edgeIdx (z : List Bool) : ℕ := binValLE (pairSnd z)

/-- That index in unary, as far as the clamp allows. -/
noncomputable def edgeU (z : List Bool) : List Bool := unaryVal p z

theorem edgeU_mem_FP : edgeU p ∈ FP := unaryVal_mem_FP p

theorem edgeU_eq {z : List Bool}
    (h : 2 ^ (pairSnd z).length ≤ p.eval z.length) :
    edgeU p z = List.replicate (edgeIdx z) true := unaryVal_eq h

/-- Is the named edge a real one? -/
noncomputable def inRange (z : List Bool) : List Bool :=
  Cobham.lenLeFlag (List.replicate (A.numEdges (pairFst z)) true)
    (true :: edgeU p z)

theorem inRange_mem_FP : A.inRange p ∈ FP := by
  have hn : (fun z : List Bool =>
      List.replicate (A.numEdges (pairFst z)) true) ∈ FP := by
    have := mem_FP_comp Cobham.fstBlock_mem_FP A.numEdges_mem
    exact this
  exact lenLeFlagFn_mem_FP hn (mem_FP_comp (edgeU_mem_FP p) (Cobham.cons_mem_FP true))

theorem inRange_eq_true_iff {z : List Bool}
    (h : 2 ^ (pairSnd z).length ≤ p.eval z.length) :
    A.inRange p z = [true] ↔ edgeIdx z < A.numEdges (pairFst z) := by
  rw [inRange, edgeU_eq p h,
    Cobham.lenLeFlag_eq_true_iff, List.length_cons, List.length_replicate,
    List.length_replicate]
  omega

/-- How many queries the verifier makes: both symbol blocks, or none when the
coin string names no edge. -/
noncomputable def cntU (z : List Bool) : List Bool :=
  Cobham.selectHead (A.inRange p z) (List.replicate (2 * A.width) true) []

theorem cntU_mem_FP : A.cntU p ∈ FP :=
  Cobham.selectHeadFn_mem_FP (A.inRange_mem_FP p)
    (constFn_mem_FP (List.replicate (2 * A.width) true)) (constFn_mem_FP [])

/-! ### Where the verifier looks -/

/-- The endpoint a query index refers to: the first for the low half of the
queries, the second for the high half. -/
noncomputable def vertU (b : Bool) (w : List Bool) : List Bool :=
  List.replicate (A.vert b (pairFst (pairFst w))
    (edgeU p (pairFst w)).length) true

theorem vertU_mem_FP (b : Bool) : A.vertU p b ∈ FP := by
  have hx : (fun w : List Bool => pairFst (pairFst w)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
  have he : (fun w : List Bool => edgeU p (pairFst w)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP (edgeU_mem_FP p)
  have := mem_FP_comp (Cobham.pairFn_mem_FP hx he) (A.vert_mem b)
  refine mem_FP_of_eq this fun w => ?_
  rw [vertU, Function.comp_apply, pairFst_pair, pairSnd_pair]

/-- Is this query in the low half? -/
def lowFlag (w : List Bool) : List Bool :=
  Cobham.lenLeFlag (List.replicate A.width true) (true :: pairSnd w)

theorem lowFlag_mem_FP : A.lowFlag ∈ FP :=
  lenLeFlagFn_mem_FP (constFn_mem_FP (List.replicate A.width true))
    (mem_FP_comp Cobham.sndBlock_mem_FP (Cobham.cons_mem_FP true))

theorem lowFlag_eq_true_iff (w : List Bool) :
    A.lowFlag w = [true] ↔ (pairSnd w).length < A.width := by
  rw [lowFlag, Cobham.lenLeFlag_eq_true_iff, List.length_cons, List.length_replicate]
  omega

/-- The offset inside the symbol block. -/
def offU (w : List Bool) : List Bool :=
  Cobham.selectHead (A.lowFlag w) (pairSnd w) ((pairSnd w).drop A.width)

theorem offU_mem_FP : A.offU ∈ FP := by
  refine Cobham.selectHeadFn_mem_FP A.lowFlag_mem_FP Cobham.sndBlock_mem_FP ?_
  have := dropLenFn_mem_FP (constFn_mem_FP (List.replicate A.width true))
    Cobham.sndBlock_mem_FP
  refine mem_FP_of_eq this fun w => ?_
  rw [List.length_replicate]

/-- **The position a query reads**, in unary. -/
noncomputable def posU (w : List Bool) : List Bool :=
  List.replicate
    ((Cobham.selectHead (A.lowFlag w) (A.vertU p false w) (A.vertU p true w)).length
      * A.width) true
    ++ List.replicate (A.offU w).length true

theorem posU_mem_FP : A.posU p ∈ FP := by
  have hv : (fun w => Cobham.selectHead (A.lowFlag w) (A.vertU p false w)
      (A.vertU p true w)) ∈ FP :=
    Cobham.selectHeadFn_mem_FP A.lowFlag_mem_FP (A.vertU_mem_FP p false)
      (A.vertU_mem_FP p true)
  have hmul : (fun w => List.replicate
      ((Cobham.selectHead (A.lowFlag w) (A.vertU p false w) (A.vertU p true w)).length
        * A.width) true) ∈ FP := by
    have hb : (fun _ : List Bool => List.replicate A.width false) ∈ FP :=
      Cobham.const_replicate_mem_FP A.width
    have hm := Cobham.mulLenFn_mem_FP hv hb
    have := mem_FP_comp hm unaryLength_mem_FP
    refine mem_FP_of_eq this fun w => ?_
    rw [Function.comp_apply, List.length_replicate, List.length_replicate]
  have hoff : (fun w => List.replicate (A.offU w).length true) ∈ FP := by
    have := mem_FP_comp A.offU_mem_FP unaryLength_mem_FP
    exact this
  exact Cobham.appendFn_mem_FP hmul hoff

theorem cntU_eq_replicate (z : List Bool) :
    A.cntU p z = List.replicate (A.cntU p z).length true := by
  rw [cntU]
  rcases Cobham.lenLeFlag_flag (List.replicate (A.numEdges (pairFst z)) true)
    (true :: edgeU p z) with h | h <;> rw [inRange, h]
  · rw [selectHead_cons_true, List.length_replicate]
  · rw [selectHead_cons_false]
    simp

theorem posU_eq_replicate (w : List Bool) :
    A.posU p w = List.replicate (A.posU p w).length true := by
  rw [posU, List.length_append, List.length_replicate, List.length_replicate,
    List.replicate_add]

/-! ### The verifier -/

/-- How many queries, as a number. -/
noncomputable def cnt (z : List Bool) : ℕ := (A.cntU p z).length

/-- The `i`-th query position, as a number. -/
noncomputable def pos (z : List Bool) (i : ℕ) : ℕ :=
  (A.posU p (pair z (List.replicate i true))).length

/-- The argument the constraint is asked about. -/
noncomputable def okArg (z : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst z)) (edgeU p (pairFst z)))
    (pairSnd z)

theorem okArg_mem_FP : okArg p ∈ FP := by
  have hx : (fun z : List Bool => pairFst (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
  have he : (fun z : List Bool => edgeU p (pairFst z)) ∈ FP :=
    mem_FP_comp Cobham.fstBlock_mem_FP (edgeU_mem_FP p)
  exact Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP hx he) Cobham.sndBlock_mem_FP

/-- The verdict: accept unless the coin string names a real edge whose
constraint fails. -/
noncomputable def verdictLang : Language :=
  {z | A.inRange p (pairFst z) = [true] → okArg p z ∈ A.ok}

theorem verdictLang_mem_P : A.verdictLang p ∈ P := by
  obtain ⟨g, hgFP, hg⟩ := exists_decisionFn_of_mem_P A.ok_mem
  have hin : (fun z : List Bool => A.inRange p (pairFst z)) ∈ FP := by
    have := mem_FP_comp Cobham.fstBlock_mem_FP (A.inRange_mem_FP p)
    exact this
  have hok : (fun z : List Bool => [g (okArg p z)]) ∈ FP := by
    have := mem_FP_comp (okArg_mem_FP p) hgFP
    exact this
  have hflag : (fun z : List Bool =>
      Cobham.selectHead (A.inRange p (pairFst z)) [g (okArg p z)] [true]) ∈ FP :=
    Cobham.selectHeadFn_mem_FP hin hok (constFn_mem_FP [true])
  refine mem_P_of_decisionFn hflag fun z => ?_
  show (A.inRange p (pairFst z) = [true] → okArg p z ∈ A.ok) ↔ _
  rcases Cobham.lenLeFlag_flag (List.replicate (A.numEdges
    (pairFst (pairFst z))) true)
    (true :: edgeU p (pairFst z)) with h | h
  · have hv : A.inRange p (pairFst z) = [true] := by rw [inRange]; exact h
    rw [hv, selectHead_cons_true]
    simp only [List.mem_singleton, exists_eq_left, forall_const]
    exact hg _
  · have hv : A.inRange p (pairFst z) = [false] := by rw [inRange]; exact h
    rw [hv, selectHead_cons_false]
    simp

theorem cnt_le (z : List Bool) : A.cnt p z ≤ 2 * A.width := by
  rw [cnt, cntU]
  rcases Cobham.lenLeFlag_flag (List.replicate (A.numEdges (pairFst z)) true)
    (true :: edgeU p z) with h | h <;> rw [inRange, h]
  · rw [selectHead_cons_true, List.length_replicate]
  · rw [selectHead_cons_false]
    simp

/-- **The verifier of a constraint graph.** -/
noncomputable def verifier : PCPVerifier where
  positions x ρ := (List.range (A.cnt p (pair x ρ))).map (A.pos p (pair x ρ))
  positions_mem := by
    have hcnt : (fun z : List Bool => List.replicate (A.cnt p z) true) ∈ FP := by
      refine mem_FP_of_eq (A.cntU_mem_FP p) fun z => ?_
      rw [cnt, ← cntU_eq_replicate]
    obtain ⟨g, hg, hgspec⟩ := positions_mem_of_unary hcnt (A.posU_mem_FP p)
      (fun z i => by
        show A.posU p (pair z (List.replicate i true))
          = List.replicate (A.posU p (pair z (List.replicate i true))).length true
        rw [← posU_eq_replicate])
    exact ⟨g, hg, fun x ρ => hgspec (pair x ρ)⟩
  verdict := A.verdictLang p
  verdict_mem := A.verdictLang_mem_P p

@[simp] theorem positions_verifier (x ρ : List Bool) :
    (A.verifier p).positions x ρ
      = (List.range (A.cnt p (pair x ρ))).map (A.pos p (pair x ρ)) := rfl

theorem verifier_queryBounded : (A.verifier p).QueryBounded (fun _ => 2 * A.width) := by
  intro x ρ
  rw [positions_verifier, List.length_map, List.length_range]
  exact A.cnt_le p _

theorem mem_verdict_verifier (z : List Bool) :
    z ∈ (A.verifier p).verdict
      ↔ (A.inRange p (pairFst z) = [true] → okArg p z ∈ A.ok) := Iff.rfl

/-! ### What the verifier reads and decides -/

/-- The position query `i` reads, as a function of the edge alone. -/
def posVal (x : List Bool) (e i : ℕ) : ℕ :=
  A.vert (decide (¬ i < A.width)) x e * A.width + (if i < A.width then i else i - A.width)

theorem pos_eq {x ρ : List Bool} (h : 2 ^ ρ.length ≤ p.eval (pair x ρ).length) (i : ℕ) :
    A.pos p (pair x ρ) i = A.posVal x (binValLE ρ) i := by
  have hz : pairSnd (pair x ρ) = ρ := pairSnd_pair x ρ
  have hE : edgeU p (pair x ρ) = List.replicate (binValLE ρ) true := by
    have := edgeU_eq (p := p) (z := pair x ρ) (by rw [hz]; exact h)
    rw [this, edgeIdx, hz]
  set w := pair (pair x ρ) (List.replicate i true) with hw
  have hsnd : pairSnd w = List.replicate i true := pairSnd_pair _ _
  have hfst : pairFst w = pair x ρ := pairFst_pair _ _
  have hlow : A.lowFlag w = if i < A.width then [true] else [false] := by
    rcases Cobham.lenLeFlag_flag (List.replicate A.width true)
      (true :: pairSnd w) with hf | hf
    · rw [lowFlag, hf, ite_eq_left]
      rw [← lowFlag, A.lowFlag_eq_true_iff w, hsnd, List.length_replicate] at hf
      exact hf
    · rw [lowFlag, hf, ite_eq_right]
      intro hcon
      have := (A.lowFlag_eq_true_iff w).mpr (by rw [hsnd, List.length_replicate]; exact hcon)
      rw [lowFlag, hf] at this
      simp at this
  have hv : ∀ b, (A.vertU p b w).length = A.vert b x (binValLE ρ) := by
    intro b
    rw [vertU, List.length_replicate, hfst, hE, List.length_replicate,
      pairFst_pair]
  have hoff : (A.offU w).length = if i < A.width then i else i - A.width := by
    rw [offU, hlow, hsnd]
    by_cases hi : i < A.width
    · rw [ite_eq_left hi, selectHead_cons_true, List.length_replicate, ite_eq_left hi]
    · rw [ite_eq_right hi, selectHead_cons_false, List.length_drop, List.length_replicate,
        ite_eq_right hi]
  show (A.posU p w).length = _
  rw [posU, List.length_append, List.length_replicate, List.length_replicate, hoff,
    posVal]
  congr 2
  rw [hlow]
  by_cases hi : i < A.width
  · rw [ite_eq_left hi, selectHead_cons_true, hv]
    simp [hi]
  · rw [ite_eq_right hi, selectHead_cons_false, hv]
    simp [hi]

/-- Edge `e` is satisfied by the proof `π`. -/
def Sat (x π : List Bool) (e : ℕ) : Prop :=
  pair (pair x (List.replicate e true))
    (PCPVerifier.answers π ((List.range (2 * A.width)).map (A.posVal x e))) ∈ A.ok

theorem cnt_eq_of_inRange {z : List Bool} (h : A.inRange p z = [true]) :
    A.cnt p z = 2 * A.width := by
  rw [cnt, cntU, h, selectHead_cons_true, List.length_replicate]

/-- **What the verifier decides.** It accepts unless the coin string names a
real edge that the proof fails to satisfy. -/
theorem accepts_verifier_iff {x ρ : List Bool}
    (h : 2 ^ ρ.length ≤ p.eval (pair x ρ).length) (π : List Bool) :
    (A.verifier p).Accepts x π ρ
      ↔ (binValLE ρ < A.numEdges x → A.Sat x π (binValLE ρ)) := by
  have hz : pairSnd (pair x ρ) = ρ := pairSnd_pair x ρ
  have hE : edgeU p (pair x ρ) = List.replicate (binValLE ρ) true := by
    have := edgeU_eq (p := p) (z := pair x ρ) (by rw [hz]; exact h)
    rw [this, edgeIdx, hz]
  have hin : A.inRange p (pair x ρ) = [true] ↔ binValLE ρ < A.numEdges x := by
    rw [A.inRange_eq_true_iff p (by rw [hz]; exact h), edgeIdx, hz, pairFst_pair]
  set a := PCPVerifier.answers π ((A.verifier p).positions x ρ) with ha
  have hacc : (A.verifier p).Accepts x π ρ
      ↔ (A.inRange p (pair x ρ) = [true] → okArg p (pair (pair x ρ) a) ∈ A.ok) := by
    rw [PCPVerifier.Accepts, mem_verdict_verifier, pairFst_pair]
  have haeq : binValLE ρ < A.numEdges x →
      a = PCPVerifier.answers π ((List.range (2 * A.width)).map (A.posVal x (binValLE ρ))) := by
    intro hlt
    rw [ha, positions_verifier, A.cnt_eq_of_inRange p (hin.mpr hlt)]
    congr 1
    exact List.map_congr_left fun i _ => A.pos_eq p h i
  rw [hacc, hin]
  constructor
  · intro hh hlt
    have hok := hh hlt
    rw [okArg, pairFst_pair, pairFst_pair, pairSnd_pair, hE] at hok
    rw [Sat, ← haeq hlt]
    exact hok
  · intro hh hlt
    have hs := hh hlt
    rw [Sat] at hs
    rw [okArg, pairFst_pair, pairFst_pair, pairSnd_pair, hE,
      haeq hlt]
    exact hs

/-! ### How often the verifier accepts -/

open Classical in
theorem acceptEvent_eq {x : List Bool} {T : ℕ}
    (h : 2 ^ T ≤ p.eval (2 * x.length + 2 + T)) (π : List Bool) :
    (A.verifier p).acceptEvent T x π
      = Finset.univ.filter (fun ρ : Fin T → Bool =>
          PCPVerifier.coinIndex ρ < A.numEdges x → A.Sat x π (PCPVerifier.coinIndex ρ)) := by
  ext ρ
  have hlen : (BitString.toList ρ).length = T := by simp
  have hclamp : 2 ^ (BitString.toList ρ).length
      ≤ p.eval (pair x (BitString.toList ρ)).length := by
    rw [hlen, pair_length, hlen]
    exact h
  simp only [PCPVerifier.acceptEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [A.accepts_verifier_iff p hclamp, binValLE_toList]

open Classical in
theorem card_reject {x : List Bool} {T : ℕ} (hN : A.numEdges x ≤ 2 ^ T) (π : List Bool) :
    ((Finset.univ.filter (fun ρ : Fin T → Bool =>
        PCPVerifier.coinIndex ρ < A.numEdges x → A.Sat x π (PCPVerifier.coinIndex ρ)))ᶜ).card
      = ((Finset.range (A.numEdges x)).filter (fun e => ¬ A.Sat x π e)).card := by
  classical
  have hcompl : (Finset.univ.filter (fun ρ : Fin T → Bool =>
      PCPVerifier.coinIndex ρ < A.numEdges x → A.Sat x π (PCPVerifier.coinIndex ρ)))ᶜ
      = Finset.univ.filter (fun ρ : Fin T → Bool =>
        ¬ (PCPVerifier.coinIndex ρ < A.numEdges x → A.Sat x π (PCPVerifier.coinIndex ρ))) := by
    ext ρ
    simp
  rw [hcompl, card_filter_coinIndex T (fun e => ¬ (e < A.numEdges x → A.Sat x π e))]
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_range, Classical.not_imp]
  constructor
  · rintro ⟨_, hlt, hns⟩
    exact ⟨hlt, hns⟩
  · rintro ⟨hlt, hns⟩
    exact ⟨lt_of_lt_of_le hlt hN, hlt, hns⟩

open Classical in
/-- **Perfect completeness.** A proof satisfying every edge is always
accepted. -/
theorem eventProb_eq_one {x : List Bool} {T : ℕ}
    (h : 2 ^ T ≤ p.eval (2 * x.length + 2 + T)) (hN : A.numEdges x ≤ 2 ^ T)
    {π : List Bool} (hsat : ∀ e < A.numEdges x, A.Sat x π e) :
    eventProb ((A.verifier p).acceptEvent T x π) = 1 := by
  classical
  have hrej : ((Finset.range (A.numEdges x)).filter (fun e => ¬ A.Sat x π e)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he
    exact not_not.mpr (hsat e (Finset.mem_range.mp he))
  have hc := A.card_reject hN π
  rw [hrej] at hc
  have hempty : (Finset.univ.filter (fun ρ : Fin T → Bool =>
      PCPVerifier.coinIndex ρ < A.numEdges x → A.Sat x π (PCPVerifier.coinIndex ρ)))ᶜ = ∅ :=
    Finset.card_eq_zero.mp hc
  have : eventProb ((Finset.univ.filter (fun ρ : Fin T → Bool =>
      PCPVerifier.coinIndex ρ < A.numEdges x → A.Sat x π (PCPVerifier.coinIndex ρ)))ᶜ) = 0 := by
    rw [hempty, eventProb_empty]
  rw [A.acceptEvent_eq p h π]
  rw [eventProb_compl] at this
  linarith

open Classical in
/-- **Soundness.** If no proof satisfies more than a `1 - gap` fraction of the
edges, the verifier accepts with probability at most `1 - gap / 2`. -/
theorem eventProb_le {x : List Bool} {T : ℕ} {gap : ℚ}
    (h : 2 ^ T ≤ p.eval (2 * x.length + 2 + T)) (hN : A.numEdges x ≤ 2 ^ T)
    (hT : 2 ^ T ≤ 2 * A.numEdges x) {π : List Bool}
    (hs : (((Finset.range (A.numEdges x)).filter (A.Sat x π)).card : ℚ)
      ≤ (1 - gap) * A.numEdges x) :
    eventProb ((A.verifier p).acceptEvent T x π) ≤ 1 - gap / 2 := by
  classical
  set N := A.numEdges x with hNdef
  set S := ((Finset.range N).filter (A.Sat x π)).card with hS
  set R := ((Finset.range N).filter (fun e => ¬ A.Sat x π e)).card with hR
  have hsum : S + R = N := by
    rw [hS, hR]
    have := Finset.card_filter_add_card_filter_not
      (s := Finset.range N) (p := A.Sat x π)
    simpa using this
  have hNpos : 0 < N := by
    have h2 : (0 : ℕ) < 2 ^ T := Nat.two_pow_pos T
    omega
  have hTQ : (0 : ℚ) < (2 : ℚ) ^ T := by positivity
  have hRQ : (R : ℚ) = (N : ℚ) - (S : ℚ) := by
    have : (S : ℚ) + (R : ℚ) = (N : ℚ) := by exact_mod_cast hsum
    linarith
  have hRge : gap * (N : ℚ) ≤ (R : ℚ) := by
    rw [hRQ]
    nlinarith [hs]
  have hTle : ((2 : ℚ) ^ T) ≤ 2 * (N : ℚ) := by
    have : ((2 ^ T : ℕ) : ℚ) ≤ ((2 * N : ℕ) : ℚ) := by exact_mod_cast hT
    push_cast at this
    linarith
  have hRnn : (0 : ℚ) ≤ (R : ℚ) := by positivity
  have hdiv : (R : ℚ) / (2 * (N : ℚ)) ≤ (R : ℚ) / (2 : ℚ) ^ T :=
    div_le_div_of_nonneg_left hRnn hTQ hTle
  have hgap : gap / 2 ≤ (R : ℚ) / (2 * (N : ℚ)) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith [hRge]
  rw [A.acceptEvent_eq p h π]
  set F := Finset.univ.filter (fun ρ : Fin T → Bool =>
    PCPVerifier.coinIndex ρ < N → A.Sat x π (PCPVerifier.coinIndex ρ)) with hF
  have hcompl : eventProb Fᶜ = 1 - eventProb F := eventProb_compl F
  have hcard : Fᶜ.card = R := A.card_reject hN π
  have hFc : eventProb Fᶜ = (R : ℚ) / 2 ^ T := by
    rw [eventProb, hcard]
  linarith [hgap, hdiv, hFc, hcompl]

end AlgCSP

open scoped Complexity in
open Classical in
/-- **A constraint graph with a gap puts its language in `PCP`.** Completeness
and soundness are hypotheses on the graph: a member has an assignment satisfying
every edge, and a non-member has none satisfying more than a `1 - gap`
fraction. -/
theorem mem_PCP_of_algCSP (A : AlgCSP) (p : Polynomial ℕ) (t : ℕ → ℕ)
    (ht : (fun x : List Bool => List.replicate (t x.length) true) ∈ FP)
    (hclamp : ∀ n : ℕ, 2 ^ t n ≤ p.eval (2 * n + 2 + t n))
    (hN : ∀ x : List Bool, A.numEdges x ≤ 2 ^ t x.length)
    (hT : ∀ x : List Bool, 2 ^ t x.length ≤ 2 * A.numEdges x)
    {L : Language} {gap : ℚ} (hgap0 : 0 < gap) (hgap1 : gap ≤ 1)
    (hcomp : ∀ x ∈ L, ∃ π : List Bool, ∀ e < A.numEdges x, A.Sat x π e)
    (hsound : ∀ x ∉ L, ∀ π : List Bool,
      (((Finset.range (A.numEdges x)).filter (A.Sat x π)).card : ℚ)
        ≤ (1 - gap) * A.numEdges x) :
    ∃ j : ℕ, L ∈ PCP (fun n => 2 ^ j * t n) (fun _ => 2 ^ j * (2 * A.width)) := by
  classical
  have hmem : L ∈ PCPWith t (fun _ => 2 * A.width) (1 - gap / 2) := by
    refine ⟨A.verifier p, A.verifier_queryBounded p, ?_, ?_⟩
    · intro x hx
      obtain ⟨π, hπ⟩ := hcomp x hx
      exact ⟨π, A.eventProb_eq_one p (hclamp x.length) (hN x) hπ⟩
    · intro x hx π
      exact A.eventProb_le p (hclamp x.length) (hN x) (hT x) (hsound x hx π)
  refine mem_PCP_of_PCPWith ?_ ?_ ht hmem
  · linarith
  · linarith

end Complexity
