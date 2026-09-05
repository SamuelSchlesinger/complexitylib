/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Cobham.Internal
public import Complexitylib.Classes.P.Cobham.Internal.Reverse
public import Complexitylib.Classes.P.UnaryLength
public import Complexitylib.Classes.Containments.Internal.BinArith
public import Complexitylib.Encoding.DataEncode
public import Complexitylib.Classes.PCP.Internal.DataScanSpec

/-!
# Scanning a serialized `Data` value

`Data.toBits` writes a value as balanced brackets: `false` opens a node, its
children follow in order, and `true` closes it. Reading one child back out of
such a string is a single left-to-right pass keeping a bracket depth and a count
of the children already passed, collecting bits only while inside the child
asked for.

This module writes that pass in the form `recFoldClamp` accepts, so that
polynomial-time computability comes from the general fold rather than from a
bespoke machine. The fold recurses head-then-tail, so it runs right to left; the
caller therefore hands it the reversed string.

The state is `pair (unary depth) (pair (unary count) collected)` and the
workspace is the requested index in unary. Every component stays below the
length of the string being scanned, so a linear clamp suffices.

## Main definitions

- `Complexity.DataScan.openStep`, `closeStep` — the two fold steps
- `Complexity.DataScan.childOf` — the scan, packaged as one function

## Main results

- `Complexity.DataScan.childOf_mem_FP` — the scan is polynomial time
- `Complexity.DataScan.recFoldClamp_eq_pack` — the fold runs the model
- `Complexity.DataScan.child_flatten` — the packaged scan extracts the child
- `Complexity.DataScan.childCount_flatten` — and counts the children
- `Complexity.DataScan.inner_toBits` — the bits between the outer brackets
-/

@[expose] public section

namespace Complexity

namespace DataScan

/-! ### Reading the packed fold argument

`recFoldClamp` hands each step `pair (pair W st) t`, with `W` the workspace, `st`
the state built so far and `t` the unscanned tail. -/

/-- The workspace: the index of the child being extracted, in unary. -/
def wsOf (z : List Bool) : List Bool := pairFst (pairFst z)

/-- The state carried by the scan. -/
def stOf (z : List Bool) : List Bool := pairSnd (pairFst z)

/-- The bracket depth, in unary. -/
def depthOf (z : List Bool) : List Bool := pairFst (stOf z)

/-- The number of children already passed, in unary. -/
def countOf (z : List Bool) : List Bool := pairFst (pairSnd (stOf z))

/-- The bits collected so far. -/
def accOf (z : List Bool) : List Bool := pairSnd (pairSnd (stOf z))

/-- Append the current bit, but only while inside the requested child. -/
def collect (z : List Bool) (b : Bool) : List Bool :=
  Cobham.selectHead (Cobham.eqFlag (countOf z) (wsOf z)) (accOf z ++ [b]) (accOf z)

/-! ### The two steps -/

/-- An opening bracket: descend one level. -/
def openStep (z : List Bool) : List Bool :=
  pair (true :: depthOf z) (pair (countOf z) (collect z false))

/-- A closing bracket: rise one level, and if that returns to the top level,
one more child has been passed. -/
def closeStep (z : List Bool) : List Bool :=
  pair (dropOne (depthOf z))
    (pair (Cobham.selectHead (emptyFlag (dropOne (depthOf z)))
        (true :: countOf z) (countOf z))
      (collect z true))

/-- The state a scan starts from. -/
def initState : List Bool := pair [] (pair [] [])

/-! ### Polynomial time -/

theorem wsOf_mem_FP : wsOf ∈ FP :=
  mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP

theorem stOf_mem_FP : stOf ∈ FP :=
  mem_FP_comp Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP

theorem depthOf_mem_FP : depthOf ∈ FP :=
  mem_FP_comp stOf_mem_FP Cobham.fstBlock_mem_FP

theorem countOf_mem_FP : countOf ∈ FP :=
  mem_FP_comp (mem_FP_comp stOf_mem_FP Cobham.sndBlock_mem_FP) Cobham.fstBlock_mem_FP

theorem accOf_mem_FP : accOf ∈ FP :=
  mem_FP_comp (mem_FP_comp stOf_mem_FP Cobham.sndBlock_mem_FP) Cobham.sndBlock_mem_FP

theorem collect_mem_FP (b : Bool) : (fun z => collect z b) ∈ FP :=
  Cobham.selectHeadFn_mem_FP (eqFlagFn_mem_FP countOf_mem_FP wsOf_mem_FP)
    (Cobham.appendFn_mem_FP accOf_mem_FP (constFn_mem_FP [b])) accOf_mem_FP

theorem openStep_mem_FP : openStep ∈ FP :=
  Cobham.pairFn_mem_FP (mem_FP_comp depthOf_mem_FP (Cobham.cons_mem_FP true))
    (Cobham.pairFn_mem_FP countOf_mem_FP (collect_mem_FP false))

theorem closeStep_mem_FP : closeStep ∈ FP := by
  have hdrop : (fun z => dropOne (depthOf z)) ∈ FP := dropOneFn_mem_FP depthOf_mem_FP
  refine Cobham.pairFn_mem_FP hdrop (Cobham.pairFn_mem_FP ?_ (collect_mem_FP true))
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hdrop)
    (mem_FP_comp countOf_mem_FP (Cobham.cons_mem_FP true)) countOf_mem_FP

/-- **The scan.** On `pair (unary i) s` it runs the two steps over `s`, keeping
every intermediate state within `p.eval` bits, and returns the collected bits. -/
def childOf (p : Polynomial ℕ) (z : List Bool) : List Bool :=
  pairSnd (pairSnd
    (Cobham.recFoldClamp openStep closeStep (p.eval z.length) initState
      (pairFst z) (pairSnd z)))

theorem childOf_mem_FP (p : Polynomial ℕ) : childOf p ∈ FP := by
  have hfold := Cobham.recFoldClamp_mem_FP openStep_mem_FP closeStep_mem_FP
    (constFn_mem_FP initState) p
  exact mem_FP_comp (mem_FP_comp hfold Cobham.sndBlock_mem_FP) Cobham.sndBlock_mem_FP

/-! ### The fold runs the model

The state the fold carries is the model's state written out: two unary counters
and the collected bits. Once that is checked step by step, the fold and the
model agree, provided the clamp is wide enough never to truncate. -/

/-- The model's state, written out as a bitstring. -/
def pack (st : ℕ × ℕ × List Bool) : List Bool :=
  pair (List.replicate st.1 true) (pair (List.replicate st.2.1 true) st.2.2)

theorem pack_length (st : ℕ × ℕ × List Bool) :
    (pack st).length = 2 * st.1 + 2 * st.2.1 + st.2.2.length + 4 := by
  rw [pack, pair_length, pair_length, List.length_replicate, List.length_replicate]
  omega

theorem pack_init : pack (0, 0, []) = initState := rfl

theorem eqFlag_replicate (c i : ℕ) :
    Cobham.eqFlag (List.replicate c true) (List.replicate i true)
      = if c = i then [true] else [false] := by
  by_cases h : c = i
  · rw [ite_eq_left h, h]
    exact (Cobham.eqFlag_eq_true_iff _ _).mpr rfl
  · rw [ite_eq_right h]
    rcases Cobham.eqFlag_flag (List.replicate c true) (List.replicate i true) with hf | hf
    · rw [Cobham.eqFlag_eq_true_iff] at hf
      exact absurd (by simpa using congrArg List.length hf) h
    · exact hf

theorem depthOf_pack (i : ℕ) (st : ℕ × ℕ × List Bool) (t : List Bool) :
    depthOf (pair (pair (List.replicate i true) (pack st)) t) = List.replicate st.1 true := by
  rw [depthOf, stOf, pairFst_pair, pairSnd_pair, pack, pairFst_pair]

theorem countOf_pack (i : ℕ) (st : ℕ × ℕ × List Bool) (t : List Bool) :
    countOf (pair (pair (List.replicate i true) (pack st)) t)
      = List.replicate st.2.1 true := by
  rw [countOf, stOf, pairFst_pair, pairSnd_pair, pack, pairSnd_pair,
    pairFst_pair]

theorem collect_pack (i : ℕ) (st : ℕ × ℕ × List Bool) (t : List Bool) (b : Bool) :
    collect (pair (pair (List.replicate i true) (pack st)) t) b
      = if st.2.1 = i then st.2.2 ++ [b] else st.2.2 := by
  rw [collect, countOf, accOf, wsOf, stOf, pairFst_pair, pairSnd_pair,
    pack, pairFst_pair, pairSnd_pair, pairFst_pair,
    pairSnd_pair, eqFlag_replicate]
  by_cases h : st.2.1 = i <;> simp [h]

theorem openStep_pack (i : ℕ) (st : ℕ × ℕ × List Bool) (t : List Bool) :
    openStep (pair (pair (List.replicate i true) (pack st)) t)
      = pack (stepSpec i st false) := by
  rw [openStep, depthOf_pack, countOf_pack, collect_pack, stepSpec, pack]
  simp [List.replicate_succ]

theorem closeStep_pack (i : ℕ) (st : ℕ × ℕ × List Bool) (t : List Bool) :
    closeStep (pair (pair (List.replicate i true) (pack st)) t)
      = pack (stepSpec i st true) := by
  have hdrop : dropOne (List.replicate st.1 true) = List.replicate (st.1 - 1) true := by
    cases st.1 with
    | zero => rfl
    | succ n => rw [List.replicate_succ]; rfl
  have hflag : emptyFlag (List.replicate (st.1 - 1) true)
      = if st.1 - 1 = 0 then [true] else [false] := by
    cases h : st.1 - 1 with
    | zero => simp
    | succ n => rw [List.replicate_succ, emptyFlag_cons]; simp
  rw [closeStep, depthOf_pack, countOf_pack, collect_pack, hdrop, hflag, stepSpec, pack]
  by_cases h : st.1 - 1 = 0 <;> simp [h, List.replicate_succ]

/-! ### The state stays small -/

theorem runSpec_bounds (i : ℕ) (s : List Bool) :
    ∀ (d c : ℕ) (acc : List Bool),
      (runSpec i (d, c, acc) s).1 ≤ d + s.length ∧
        (runSpec i (d, c, acc) s).2.1 ≤ c + s.length ∧
        (runSpec i (d, c, acc) s).2.2.length ≤ acc.length + s.length := by
  induction s with
  | nil => intro d c acc; simp
  | cons b s ih =>
      intro d c acc
      rw [runSpec_cons]
      have hstep : stepSpec i (d, c, acc) b
          = ((stepSpec i (d, c, acc) b).1, (stepSpec i (d, c, acc) b).2.1,
              (stepSpec i (d, c, acc) b).2.2) := rfl
      have h1 : (stepSpec i (d, c, acc) b).1 ≤ d + 1 := by
        cases b <;> simp [stepSpec]
        omega
      have h2 : (stepSpec i (d, c, acc) b).2.1 ≤ c + 1 := by
        cases b <;> simp [stepSpec]
        split <;> omega
      have h3 : (stepSpec i (d, c, acc) b).2.2.length ≤ acc.length + 1 := by
        have hb2 : (stepSpec i (d, c, acc) b).2.2 = if c = i then acc ++ [b] else acc := by
          cases b <;> rfl
        rw [hb2]
        by_cases hc : c = i <;> simp [hc]
      rw [hstep]
      obtain ⟨j1, j2, j3⟩ := ih (stepSpec i (d, c, acc) b).1 (stepSpec i (d, c, acc) b).2.1
        (stepSpec i (d, c, acc) b).2.2
      refine ⟨?_, ?_, ?_⟩
      · exact le_trans j1 (by simp [List.length_cons]; omega)
      · exact le_trans j2 (by simp [List.length_cons]; omega)
      · exact le_trans j3 (by simp [List.length_cons]; omega)

theorem pack_runSpec_length_le (i : ℕ) (s : List Bool) :
    (pack (runSpec i (0, 0, []) s)).length ≤ 5 * s.length + 4 := by
  obtain ⟨h1, h2, h3⟩ := runSpec_bounds i s 0 0 []
  rw [pack_length]
  simp only [List.length_nil, Nat.zero_add] at h1 h2 h3
  omega

/-- **The fold runs the model.** Reading the reversed string with the clamped
fold gives exactly the model's state, as long as the clamp is wide enough. -/
theorem recFoldClamp_eq_pack (i bound : ℕ) (l : List Bool)
    (hb : 5 * l.length + 4 ≤ bound) :
    Cobham.recFoldClamp openStep closeStep bound initState (List.replicate i true) l
      = pack (runSpec i (0, 0, []) l.reverse) := by
  induction l with
  | nil =>
      rw [Cobham.recFoldClamp, ← pack_init]
      simp only [List.reverse_nil, runSpec_nil]
      refine List.take_of_length_le ?_
      have := pack_runSpec_length_le i ([] : List Bool)
      simp only [runSpec_nil] at this
      simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at hb
      exact le_trans (by simpa using pack_length (0, 0, ([] : List Bool)) ▸ le_refl _) hb
  | cons b l ih =>
      have hb' : 5 * l.length + 4 ≤ bound := by
        simp only [List.length_cons] at hb
        omega
      rw [Cobham.recFoldClamp, ih hb']
      have hstep : (bif b then closeStep else openStep)
          (pair (pair (List.replicate i true) (pack (runSpec i (0, 0, []) l.reverse))) l)
          = pack (stepSpec i (runSpec i (0, 0, []) l.reverse) b) := by
        cases b
        · exact openStep_pack _ _ _
        · exact closeStep_pack _ _ _
      rw [hstep]
      have hval : pack (stepSpec i (runSpec i (0, 0, []) l.reverse) b)
          = pack (runSpec i (0, 0, []) (b :: l).reverse) := by
        rw [List.reverse_cons, runSpec_append]
        rfl
      rw [hval]
      refine List.take_of_length_le ?_
      exact le_trans (pack_runSpec_length_le i ((b :: l).reverse)) (by simpa using hb)

/-! ### The packaged scan -/

/-- A clamp wide enough for any scan: the state never exceeds `5 n + 4` bits. -/
noncomputable def scanPoly : Polynomial ℕ := Polynomial.C 5 * Polynomial.X + Polynomial.C 4

@[simp] theorem scanPoly_eval (n : ℕ) : scanPoly.eval n = 5 * n + 4 := by
  rw [scanPoly]
  simp

/-- The scan's argument: the index in unary paired with the reversed string, the
order the fold consumes. -/
def scanArg (i : ℕ) (s : List Bool) : List Bool := pair (List.replicate i true) s.reverse

theorem scanArg_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => scanArg (a z).length (b z)) ∈ FP := by
  have hrep : (fun z => List.replicate (a z).length true) ∈ FP := by
    have := mem_FP_comp ha unaryLength_mem_FP
    exact this
  have hrev : (fun z => (b z).reverse) ∈ FP := by
    have := mem_FP_comp hb reverse_mem_FP
    exact this
  exact Cobham.pairFn_mem_FP hrep hrev

/-- **The scan extracts the child.** Reading the concatenated serializations of
`xs` returns the `i`-th one, or nothing when there is no such child. -/
theorem child_flatten (i : ℕ) (xs : List Data) :
    childOf scanPoly (scanArg i ((xs.map Data.toBits).flatten))
      = ((xs[i]?).map Data.toBits).getD [] := by
  set F := (xs.map Data.toBits).flatten with hF
  have hlen : (scanArg i F).length = 2 * i + 2 + F.length := by
    rw [scanArg, pair_length, List.length_replicate, List.length_reverse]
  rw [childOf, scanArg, pairFst_pair, pairSnd_pair, ← scanArg, hlen,
    scanPoly_eval, recFoldClamp_eq_pack i _ F.reverse (by simp),
    List.reverse_reverse, hF, runSpec_inner, pack, pairSnd_pair,
    pairSnd_pair]

/-- **How many children there are**, in unary: the same pass, reading off the
counter instead of the collected bits. -/
def childCount (p : Polynomial ℕ) (z : List Bool) : List Bool :=
  pairFst (pairSnd
    (Cobham.recFoldClamp openStep closeStep (p.eval z.length) initState
      (pairFst z) (pairSnd z)))

theorem childCount_mem_FP (p : Polynomial ℕ) : childCount p ∈ FP := by
  have hfold := Cobham.recFoldClamp_mem_FP openStep_mem_FP closeStep_mem_FP
    (constFn_mem_FP initState) p
  exact mem_FP_comp (mem_FP_comp hfold Cobham.sndBlock_mem_FP) Cobham.fstBlock_mem_FP

theorem childCount_flatten (i : ℕ) (xs : List Data) :
    childCount scanPoly (scanArg i ((xs.map Data.toBits).flatten))
      = List.replicate xs.length true := by
  set F := (xs.map Data.toBits).flatten with hF
  have hlen : (scanArg i F).length = 2 * i + 2 + F.length := by
    rw [scanArg, pair_length, List.length_replicate, List.length_reverse]
  rw [childCount, scanArg, pairFst_pair, pairSnd_pair, ← scanArg, hlen,
    scanPoly_eval, recFoldClamp_eq_pack i _ F.reverse (by simp),
    List.reverse_reverse, hF, runSpec_inner, pack, pairSnd_pair,
    pairFst_pair]

/-- The bits strictly between the outer brackets of a serialized list. -/
theorem inner_toBits (xs : List Data) :
    ((Data.l xs).toBits.drop 1).take ((Data.l xs).toBits.length - 2)
      = (xs.map Data.toBits).flatten := by
  have hb : (Data.l xs).toBits
      = false :: ((xs.map Data.toBits).flatten ++ [true]) := Data.toBits_l xs
  rw [hb]
  simp

end DataScan

end Complexity
