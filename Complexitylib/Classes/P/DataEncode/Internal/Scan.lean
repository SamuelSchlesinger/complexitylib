/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/
module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Encoding.DataScan
public import Complexitylib.Classes.P.Bridge
import Complexitylib.Classes.P.Iterate
import Complexitylib.Classes.P.Unary.Internal.Basic
import Complexitylib.Classes.P.UnaryLength
import Complexitylib.Classes.P.Cobham.Internal.Reverse

/-!
# Reading encoded lists — the scan as a fold

The bracket scan `DataScan.runSpec` of `Complexitylib.Encoding.DataScan`, run as
a polynomial-time fold. The fold's state is the scan's state written out:
`pair (unary depth) (pair (unary count) collected)`, with the index of the child
sought, in unary, as the workspace. Checking that the two fold steps act on that
state as the scan does (`openStep_pack`, `closeStep_pack`) is the whole proof;
the state stays linear in the length of the string, so
`recFold_mem_FP_of_bound` applies. The fold reads its string from the last bit
to the first, so it is handed the string reversed.

## Contents

- `DataScan.openStep`, `DataScan.closeStep` — the two fold steps
- `DataScan.pack` — the scan's state as a string
- `DataScan.openStep_pack`, `DataScan.closeStep_pack` — the steps run the scan
- `DataScan.pack_runSpec_length_le` — the state stays linear
- `DataScan.scan_mem_FP` — running the scan is polynomial-time
-/

@[expose] public section

namespace Complexity

namespace DataScan

/-! ### Reading the packed fold argument

The fold hands each step `pair (pair W st) t`, with `W` the workspace, `st` the
state built so far and `t` the unscanned tail. -/

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

/-! ### The steps run the scan -/

/-- The scan's state, written out as a bitstring. -/
def pack (st : ℕ × ℕ × List Bool) : List Bool :=
  pair (List.replicate st.1 true) (pair (List.replicate st.2.1 true) st.2.2)

theorem pack_length (st : ℕ × ℕ × List Bool) :
    (pack st).length = 2 * st.1 + 2 * st.2.1 + st.2.2.length + 4 := by
  rw [pack, pair_length, pair_length, List.length_replicate, List.length_replicate]
  omega

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
  by_cases h : st.2.1 = i <;> simp [h, selectHead_singleton]

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
  by_cases h : st.1 - 1 = 0 <;> simp [h, List.replicate_succ, selectHead_singleton]

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

/-! ### The scan in polynomial time -/

/-- **Running the scan is polynomial-time.** The scan for the child `|a z|` over
`s z`, as its packed state, is polynomial-time when `a` and `s` are: it is the
fold of the two steps over the reversed string, whose state never exceeds
`5 |s z| + 4` bits. -/
theorem scan_mem_FP {a s : List Bool → List Bool} (ha : a ∈ FP) (hs : s ∈ FP) :
    (fun z => pack (runSpec (a z).length (0, 0, []) (s z))) ∈ FP := by
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hs
  have hw : (fun z => List.replicate (a z).length true) ∈ FP := mem_FP_comp ha unaryLength_mem_FP
  have hrev : (fun z => (s z).reverse) ∈ FP := mem_FP_comp hs reverse_mem_FP
  have hfold := recFold_mem_FP_of_bound
    (g := fun z t => pack (runSpec (a z).length (0, 0, []) t.reverse))
    openStep_mem_FP closeStep_mem_FP (constFn_mem_FP initState) hw hrev (fun _ => rfl)
    (fun z t => by
      rw [List.reverse_cons, runSpec_append, openStep_pack]
      rfl)
    (fun z t => by
      rw [List.reverse_cons, runSpec_append, closeStep_pack]
      rfl)
    (((PolyBound.const 5).mul (PolyBound.eval p)).add (PolyBound.const 4))
    fun z t ht => by
      have hlen := pack_runSpec_length_le (a z).length t.reverse
      have hsuf := ht.length_le
      have hpz := hp z
      simp only [List.length_reverse] at hlen hsuf ⊢
      omega
  exact mem_FP_of_eq hfold fun z => by
    simp only [List.reverse_reverse]

end DataScan

end Complexity
