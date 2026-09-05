/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.BodyAssembly
public import Complexitylib.Models.TuringMachine.UTM.Internal.BodyLookup

/-!
# Body machine: the match-loop induction

The final piece of the body correctness: from `cmpQ f` at the start of the
entry region, the machine walks the `takeField` segment split exactly as
`machFind` does (`BodyLookup.lean`) — per segment either the full
key-and-value scan succeeds (`cmpQ` → `cmpS` → `copyQ'` → `copyAct` →
`appRewScr`), or the first failure point diverts to the uniform mismatch
path (`skipSeg` → `segCheck` → `mmScr` → `rewindSt`) and the loop resumes
at the next segment; an empty next segment sends the machine to the
default path (`dfScr`) with the sanitized default moves applied (trick 4).

`matchLoop` packages both outcomes against `machFind`:

* `machFind … = some seg` — the machine reaches `appRewScr f` with the
  matched segment's value slice on the scratch tape;
* `machFind … = none` — the machine reaches `dfScr` having applied the
  default moves, scratch confined and blank beyond its head.

**Corner (empty first segment).** `machFind`/`parseEntries` treat a region
that *starts* with `□` as an exhausted table. The machine, started at
`cmpQ` on such a region, instead steps past the empty segment
(`cmpQ`→`skipSeg`→`segCheck` at the *next* cell) — it only recognizes the
table terminator as a `□` read by `segCheck`. On `R = □ :: s :: …` with
`s ≠ □` the two genuinely diverge: the machine goes on to scan the
segments after the empty one while `machFind` returns `none`. `matchLoop`
therefore carries the hypothesis that an empty head segment is a real
terminator (`R = □ :: s :: … → s = □`). Every region the loop actually
sees satisfies it: canonical descriptions (`TMDesc.syms`) have entry
regions of the form `entry □ ⋯ □ □` (head symbol is an entry bit) or `□`
(empty table), and the loop re-enters `cmpQ` only through `segCheck`,
which has just read the next region's head symbol and found it non-`□`.
-/


public section

namespace Complexity

namespace TM.UTMBody

open BodyQ

-- ════════════════════════════════════════════════════════════════════════
-- List-level helpers: the segment view of the entry region
-- ════════════════════════════════════════════════════════════════════════

/-- A tape whose head is known equals the literal rebuild. -/
private theorem tape_mk_eq {t : Tape} {h : ℕ} (hh : t.head = h) :
    (⟨h, t.cells⟩ : Tape) = t := by
  cases t
  subst hh
  rfl

private theorem takeField_fst_le (l : List Γw) :
    (takeField l).1.length ≤ l.length := by
  rcases takeField_structure l with hsp | ⟨hsp, -⟩
  · have := congrArg List.length hsp
    simp only [List.length_append, List.length_cons] at this
    omega
  · exact le_of_eq (congrArg List.length hsp)

/-- If the rest after the first field is nonempty, the separator was real:
    the input splits exactly. -/
private theorem takeField_split_of_snd_ne_nil {l : List Γw}
    (h : (takeField l).2 ≠ []) :
    l = (takeField l).1 ++ Γw.blank :: (takeField l).2 := by
  rcases takeField_structure l with hsp | ⟨-, h2⟩
  · exact hsp
  · exact absurd h2 h

private theorem getD_lt {l : List Γw} {j : ℕ} (hj : j < l.length) :
    (l[j]?).getD Γw.blank = l[j] := by
  rw [List.getElem?_eq_getElem hj, Option.getD_some]

private theorem getD_ge {l : List Γw} {j : ℕ} (hj : l.length ≤ j) :
    (l[j]?).getD Γw.blank = Γw.blank := by
  rw [List.getElem?_eq_none hj]
  rfl

private theorem lt_of_getD_ne_blank {l : List Γw} {j : ℕ}
    (h : (l[j]?).getD Γw.blank ≠ Γw.blank) : j < l.length := by
  by_contra hcon
  exact h (getD_ge (by omega))

private theorem getD_append_lt {seg : List Γw} (rest : List Γw) {j : ℕ}
    (hj : j < seg.length) :
    ((seg ++ Γw.blank :: rest)[j]?).getD Γw.blank = seg[j] := by
  rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj,
    Option.getD_some]

private theorem getD_append_sep (seg rest : List Γw) :
    ((seg ++ Γw.blank :: rest)[seg.length]?).getD Γw.blank = Γw.blank := by
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

private theorem getD_append_rest (seg rest : List Γw) (j : ℕ) :
    ((seg ++ Γw.blank :: rest)[seg.length + 1 + j]?).getD Γw.blank
      = (rest[j]?).getD Γw.blank := by
  rw [List.getElem?_append_right (by omega),
    show seg.length + 1 + j - seg.length = j + 1 by omega,
    List.getElem?_cons_succ]

/-- Blank-default cell view inside the first field. -/
private theorem getD_field_lt {R : List Γw} {j : ℕ}
    (hj : j < (takeField R).1.length) :
    (R[j]?).getD Γw.blank = (takeField R).1[j] := by
  rcases takeField_structure R with hsp | ⟨h1, -⟩
  · have h := getD_append_lt (takeField R).2 hj
    rw [← hsp] at h
    exact h
  · have hj' : j < R.length := by
      have := congrArg List.length h1
      omega
    rw [List.getElem?_eq_getElem hj', Option.getD_some]
    exact (List.getElem_of_eq h1 hj).symm

/-- Blank-default cell view at the separator position. -/
private theorem getD_field_sep (R : List Γw) :
    (R[(takeField R).1.length]?).getD Γw.blank = Γw.blank := by
  rcases takeField_structure R with hsp | ⟨h1, -⟩
  · have h := getD_append_sep (takeField R).1 (takeField R).2
    rw [← hsp] at h
    exact h
  · rw [List.getElem?_eq_none (by
      have := congrArg List.length h1
      omega)]
    rfl

/-- Blank-default cell view beyond the separator: the rest of the split. -/
private theorem getD_field_rest (R : List Γw) (j : ℕ) :
    (R[(takeField R).1.length + 1 + j]?).getD Γw.blank
      = ((takeField R).2[j]?).getD Γw.blank := by
  rcases takeField_structure R with hsp | ⟨h1, h2⟩
  · have h := getD_append_rest (takeField R).1 (takeField R).2 j
    rw [← hsp] at h
    exact h
  · rw [List.getElem?_eq_none (by
        have := congrArg List.length h1
        omega),
      h2, List.getElem?_eq_none (by simp)]

/-- The key cells are blank-free. -/
private theorem keyCells_ne_blank (f : VFlags) (v0 v1 v2 : Γ) :
    ∀ s ∈ keyCells f v0 v1 v2, s ≠ Γw.blank := by
  intro s hs
  unfold keyCells at hs
  exact bitsToSyms_ne_blank hs

-- ════════════════════════════════════════════════════════════════════════
-- One round, match case: cmpQ → cmpS → copyQ' → copyAct → appRewScr
-- ════════════════════════════════════════════════════════════════════════

/-- **Matching round**: from `cmpQ f` at the start of a `MachMatch`-ing
    segment (cells `pos..pos+|seg|-1`), the machine scans the key and copies
    the value slice to scratch, reaching `appRewScr f` in exactly
    `2·w + 18` steps. State tape and virtual tapes exactly restored, desc
    cells unchanged. -/
private theorem roundMatch (f : VFlags) (v0 v1 v2 : Γ) (stSyms seg : List Γw)
    (hst_nb : ∀ s ∈ stSyms, s ≠ Γw.blank)
    (hseg_nb : ∀ s ∈ seg, s ≠ Γw.blank)
    (hMM : MachMatch stSyms.length stSyms (keyCells f v0 v1 v2) seg)
    (pos : ℕ) (hpos : 1 ≤ pos) (c : Cfg 6 bodyTM.Q)
    (hst : c.state = cmpQ f)
    (hview : ∀ j, (hj : j < seg.length) →
      (c.work dsT).cells (pos + j) = (seg[j]).toΓ)
    (hdhead : (c.work dsT).head = pos)
    (hWns : ∀ j, 1 ≤ j → (c.work dsT).cells j ≠ Γ.start)
    (hSt : (c.work stT).HoldsExact stSyms) (hsthead : (c.work stT).head = 1)
    (hSc : (c.work scT).HoldsExact []) (hschead : (c.work scT).head = 1)
    (hv0 : (c.work vIn).read = v0) (hv1 : (c.work vWk).read = v1)
    (hv2 : (c.work vOut).read = v2)
    (hv0s : (c.work vIn).read ≠ Γ.start) (hv1s : (c.work vWk).read ≠ Γ.start)
    (hv2s : (c.work vOut).read ≠ Γ.start)
    (hin : c.input.read ≠ Γ.start) (hout : c.output.read ≠ Γ.start) :
    ∃ c' t, t ≤ 2 * stSyms.length + 18 ∧
      bodyTM.reachesIn t c c' ∧
      c'.state = appRewScr f ∧
      (c'.work scT).HoldsExact
        ((seg.drop (stSyms.length + 6)).take (stSyms.length + 10)) ∧
      (c'.work scT).head = stSyms.length + 10 + 1 ∧
      c'.work stT = c.work stT ∧
      (c'.work dsT).cells = (c.work dsT).cells ∧
      (c'.work dsT).head = pos + (2 * stSyms.length + 16) ∧
      c'.work vIn = c.work vIn ∧ c'.work vWk = c.work vWk ∧
      c'.work vOut = c.work vOut ∧
      c'.input = c.input ∧ c'.output = c.output := by
  obtain ⟨hc1, hc2, hlen⟩ := hMM
  have hS_wns := (Tape.HoldsExact.startInvariant hSt).2
  have hE_wns := (Tape.HoldsExact.startInvariant hSc).2
  have hsc_read : (c.work scT).read ≠ Γ.start :=
    SimInv.read_ne_start_of_holdsExact hSc (by rw [hschead])
  have hoth6 : ∀ i : Fin 6, i ≠ stT → i ≠ dsT → (c.work i).read ≠ Γ.start := by
    intro i hiS hiD
    rcases i with ⟨iv, hv⟩
    rcases iv with _ | _ | _ | _ | _ | _ | n
    · exact hv0s
    · exact hv1s
    · exact hv2s
    · exact absurd rfl hiS
    · exact absurd rfl hiD
    · exact hsc_read
    · exact absurd hv (by omega)
  -- key-field cell identifications
  have hseg_st : ∀ j, (hj : j < stSyms.length) →
      seg[j]'(by omega) = stSyms[j] := by
    intro j hj
    have h2 : j < (seg.take stSyms.length).length := by
      rw [List.length_take]; omega
    have h1 : (seg.take stSyms.length)[j]'h2 = seg[j]'(by omega) :=
      List.getElem_take
    exact h1.symm.trans (List.getElem_of_eq hc1 h2)
  have hkey_st : ∀ i, (hi : i < 6) →
      seg[stSyms.length + i]'(by omega)
        = (keyCells f v0 v1 v2)[i]'(by rw [keyCells_length]; omega) := by
    intro i hi
    have h2 : i < ((seg.drop stSyms.length).take 6).length := by
      rw [List.length_take, List.length_drop]; omega
    have h1 : ((seg.drop stSyms.length).take 6)[i]'h2
        = seg[stSyms.length + i]'(by omega) := by
      rw [List.getElem_take, List.getElem_drop]
    exact h1.symm.trans (List.getElem_of_eq hc2 h2)
  -- Phase 1: cmpQ lockstep over the state field
  obtain ⟨c₁, hr₁, hst₁, hwtS₁, hwtD₁, hin₁, hout₁, hoth₁⟩ :=
    cmpQ_match_loop f (c.work stT).cells (c.work dsT).cells hS_wns hWns
      stSyms.length 1 pos (by omega) hpos
      (fun j hj => by
        have hS : (c.work stT).cells (1 + j) = (stSyms[j]).toΓ := by
          rw [show 1 + j = j + 1 by omega]
          exact Tape.HoldsExact.cells_lt hSt hj
        refine ⟨?_, ?_⟩
        · rw [hS, hview j (by omega), hseg_st j hj]
        · rw [hS]
          intro hcon
          exact hst_nb _ (List.getElem_mem hj) (Γw.toΓ_eq_blank.mp hcon))
      (by
        rw [show 1 + stSyms.length = stSyms.length + 1 by omega]
        exact Tape.HoldsExact.cells_ge hSt (Nat.le_refl _))
      c hst rfl hsthead rfl hdhead hin hout hoth6
  -- Phase 2: cmpS over the six key cells
  obtain ⟨c₂, hr₂, hst₂, hwtS₂, hwtD₂, hin₂, hout₂, hoth₂⟩ :=
    cmpS_match_loop f v0 v1 v2 (c.work dsT).cells (c.work stT).cells
      hWns hS_wns 5 0 rfl (1 + stSyms.length) (pos + stSyms.length)
      (by omega) (by omega)
      (fun j hj hj6 => by
        have hjm : stSyms.length + j < seg.length := by omega
        have hW : (c.work dsT).cells (pos + stSyms.length + j)
            = (seg[stSyms.length + j]'hjm).toΓ := by
          rw [show pos + stSyms.length + j = pos + (stSyms.length + j) by omega]
          exact hview _ hjm
        have hkc := keyCells_get f v0 v1 v2 ⟨j, by omega⟩
        refine ⟨?_, ?_⟩
        · rw [hW, hkey_st j (by omega), hkc]
          exact congrArg (keyCell f v0 v1 v2) (Fin.ext (by simp))
        · rw [hW]
          intro hcon
          exact hseg_nb _ (List.getElem_mem hjm) (Γw.toΓ_eq_blank.mp hcon))
      c₁ hst₁
      (by rw [hoth₁ vIn (by decide) (by decide)]; exact hv0)
      (by rw [hoth₁ vWk (by decide) (by decide)]; exact hv1)
      (by rw [hoth₁ vOut (by decide) (by decide)]; exact hv2)
      (by rw [hwtS₁]) (by rw [hwtS₁])
      (by rw [hwtD₁]) (by rw [hwtD₁])
      (by rw [hin₁]; exact hin) (by rw [hout₁]; exact hout)
      (fun i hiS hiD => by
        rw [hoth₁ i hiS hiD]
        exact hoth6 i hiS hiD)
  -- Phase 3: copyQ' — the w-cell value state field, counting down
  obtain ⟨c₃, hr₃, hst₃, hwtS₃, hwtD₃, hwtE₃, hin₃, hout₃, hoth₃⟩ :=
    copyQ'_copy_loop f (c.work stT).cells (c.work dsT).cells hSt.1 hS_wns hWns
      stSyms.length (c.work scT).cells hE_wns
      (pos + stSyms.length + 6) 1 (by omega) (by omega)
      (fun j hj => by
        rw [show pos + stSyms.length + 6 + j = pos + (stSyms.length + 6 + j)
          by omega, hview (stSyms.length + 6 + j) (by omega)]
        intro hcon
        exact hseg_nb _ (List.getElem_mem (by omega)) (Γw.toΓ_eq_blank.mp hcon))
      c₂ hst₂
      (by rw [hwtS₂]) (by rw [hwtS₂]; show 1 + stSyms.length - 1 = _; omega)
      (by rw [hwtD₂]) (by rw [hwtD₂])
      (by rw [hoth₂ scT (by decide) (by decide),
        hoth₁ scT (by decide) (by decide)])
      (by rw [hoth₂ scT (by decide) (by decide),
        hoth₁ scT (by decide) (by decide)]; exact hschead)
      (by rw [hin₂, hin₁]; exact hin) (by rw [hout₂, hout₁]; exact hout)
      (fun i hiS hiD hiE => by
        rw [hoth₂ i hiS hiD, hoth₁ i hiS hiD]
        exact hoth6 i hiS hiD)
  -- Phase 4: copyAct — the ten action cells
  obtain ⟨c₄, hr₄, hst₄, hwtD₄, hwtE₄, hin₄, hout₄, hoth₄⟩ :=
    copyAct_copy_loop f (c.work dsT).cells hWns 9 0 rfl
      (fun j => if 1 ≤ j ∧ j < 1 + stSyms.length then
          (c.work dsT).cells (pos + stSyms.length + 6 + (j - 1))
        else (c.work scT).cells j)
      (by
        intro i hi
        by_cases hcase : 1 ≤ i ∧ i < 1 + stSyms.length
        · rw [ite_eq_left hcase]
          exact hWns _ (by omega)
        · rw [ite_eq_right hcase]
          exact hE_wns i hi)
      (pos + stSyms.length + 6 + stSyms.length) (1 + stSyms.length)
      (by omega) (by omega)
      (fun i hi => by
        rw [show pos + stSyms.length + 6 + stSyms.length + i
            = pos + (stSyms.length + 6 + stSyms.length + i) by omega,
          hview (stSyms.length + 6 + stSyms.length + i) (by omega)]
        intro hcon
        exact hseg_nb _ (List.getElem_mem (by omega)) (Γw.toΓ_eq_blank.mp hcon))
      c₃ hst₃
      (by rw [hwtD₃]) (by rw [hwtD₃])
      (by rw [hwtE₃]) (by rw [hwtE₃])
      (by rw [hin₃, hin₂, hin₁]; exact hin)
      (by rw [hout₃, hout₂, hout₁]; exact hout)
      (fun i hiD hiE => by
        by_cases hiS : i = stT
        · subst hiS
          rw [hwtS₃, Tape.read]
          exact hS_wns 1 (by omega)
        · rw [hoth₃ i hiS hiD hiE, hoth₂ i hiS hiD, hoth₁ i hiS hiD]
          exact hoth6 i hiS hiD)
  -- assemble
  have hE₂ : ∀ i, (c₄.work scT).cells i
      = if 1 + stSyms.length ≤ i ∧ i < 1 + stSyms.length + 9 + 1 then
          (c.work dsT).cells
            (pos + stSyms.length + 6 + stSyms.length + (i - (1 + stSyms.length)))
        else if 1 ≤ i ∧ i < 1 + stSyms.length then
          (c.work dsT).cells (pos + stSyms.length + 6 + (i - 1))
        else (c.work scT).cells i := by
    intro i
    rw [hwtE₄]
  have hslice_len :
      ((seg.drop (stSyms.length + 6)).take (stSyms.length + 10)).length
        = stSyms.length + 10 := by
    rw [List.length_take, List.length_drop]
    omega
  refine ⟨c₄, stSyms.length + 1 + (5 + 1) + (stSyms.length + 1) + (9 + 1),
    by omega,
    reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _ hr₁ hr₂) hr₃) hr₄,
    hst₄, ⟨?_, fun i => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- scratch cell 0
    rw [hE₂ 0, ite_eq_right (by omega), ite_eq_right (by omega)]
    exact hSc.1
  · -- scratch cells: the value slice
    rw [hE₂ (i + 1)]
    by_cases hi : i < stSyms.length + 10
    · rw [dite_eq_left (by rw [hslice_len]; omega)]
      have hcell : (c.work dsT).cells (pos + (stSyms.length + 6 + i))
          = (seg[stSyms.length + 6 + i]'(by omega)).toΓ := hview _ (by omega)
      have hsliceval :
          ((seg.drop (stSyms.length + 6)).take (stSyms.length + 10))[i]'(by
            rw [hslice_len]; omega)
            = seg[stSyms.length + 6 + i]'(by omega) := by
        rw [List.getElem_take, List.getElem_drop]
      by_cases hiw : stSyms.length ≤ i
      · rw [ite_eq_left (by omega),
          show pos + stSyms.length + 6 + stSyms.length + (i + 1 - (1 + stSyms.length))
            = pos + (stSyms.length + 6 + i) by omega,
          hcell]
        exact (congrArg Γw.toΓ hsliceval).symm
      · rw [ite_eq_right (by omega), ite_eq_left (by omega),
          show pos + stSyms.length + 6 + (i + 1 - 1)
            = pos + (stSyms.length + 6 + i) by omega,
          hcell]
        exact (congrArg Γw.toΓ hsliceval).symm
    · rw [dite_eq_right (by rw [hslice_len]; omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
      exact Tape.HoldsExact.cells_ge hSc (Nat.zero_le _)
  · -- scratch head
    rw [hwtE₄]
    show 1 + stSyms.length + 9 + 1 = _
    omega
  · -- state tape restored
    rw [hoth₄ stT (by decide) (by decide), hwtS₃]
    exact tape_mk_eq hsthead
  · -- desc cells
    rw [hwtD₄]
  · -- desc head
    rw [hwtD₄]
    show pos + stSyms.length + 6 + stSyms.length + 9 + 1 = _
    omega
  · rw [hoth₄ vIn (by decide) (by decide), hoth₃ vIn (by decide) (by decide)
      (by decide), hoth₂ vIn (by decide) (by decide),
      hoth₁ vIn (by decide) (by decide)]
  · rw [hoth₄ vWk (by decide) (by decide), hoth₃ vWk (by decide) (by decide)
      (by decide), hoth₂ vWk (by decide) (by decide),
      hoth₁ vWk (by decide) (by decide)]
  · rw [hoth₄ vOut (by decide) (by decide), hoth₃ vOut (by decide) (by decide)
      (by decide), hoth₂ vOut (by decide) (by decide),
      hoth₁ vOut (by decide) (by decide)]
  · rw [hin₄, hin₃, hin₂, hin₁]
  · rw [hout₄, hout₃, hout₂, hout₁]

-- ════════════════════════════════════════════════════════════════════════
-- One round, mismatch case: cmpQ → … → skipSeg → segCheck
-- ════════════════════════════════════════════════════════════════════════

/-- **Mismatching round**: from `cmpQ f` at the start of a segment that
    fails `MachMatch`, the machine detects the first failure point (state
    field, key cell, or short value), diverts to `skipSeg f`, walks to the
    segment's terminating `□` and steps past it, stopping in `segCheck f`
    at `pos + |seg| + 1`. State and desc cells unchanged, virtual tapes
    exactly preserved, scratch confined: `▷`-free, blank at and beyond its
    head, head ≤ `w + 11`. -/
private theorem roundMismatch (f : VFlags) (v0 v1 v2 : Γ) (stSyms seg : List Γw)
    (hst_nb : ∀ s ∈ stSyms, s ≠ Γw.blank)
    (hseg_nb : ∀ s ∈ seg, s ≠ Γw.blank)
    (hMM : ¬ MachMatch stSyms.length stSyms (keyCells f v0 v1 v2) seg)
    (pos : ℕ) (hpos : 1 ≤ pos) (c : Cfg 6 bodyTM.Q)
    (hst : c.state = cmpQ f)
    (hview : ∀ j, (hj : j < seg.length) →
      (c.work dsT).cells (pos + j) = (seg[j]).toΓ)
    (hviewE : (c.work dsT).cells (pos + seg.length) = Γ.blank)
    (hdhead : (c.work dsT).head = pos)
    (hWns : ∀ j, 1 ≤ j → (c.work dsT).cells j ≠ Γ.start)
    (hSt : (c.work stT).HoldsExact stSyms) (hsthead : (c.work stT).head = 1)
    (hSc : (c.work scT).HoldsExact []) (hschead : (c.work scT).head = 1)
    (hv0 : (c.work vIn).read = v0) (hv1 : (c.work vWk).read = v1)
    (hv2 : (c.work vOut).read = v2)
    (hv0s : (c.work vIn).read ≠ Γ.start) (hv1s : (c.work vWk).read ≠ Γ.start)
    (hv2s : (c.work vOut).read ≠ Γ.start)
    (hin : c.input.read ≠ Γ.start) (hout : c.output.read ≠ Γ.start) :
    ∃ c' t, t ≤ 2 * stSyms.length + seg.length + 19 ∧
      bodyTM.reachesIn t c c' ∧
      c'.state = segCheck f ∧
      (c'.work stT).cells = (c.work stT).cells ∧
      1 ≤ (c'.work stT).head ∧ (c'.work stT).head ≤ stSyms.length + 1 ∧
      (c'.work dsT).cells = (c.work dsT).cells ∧
      (c'.work dsT).head = pos + seg.length + 1 ∧
      (c'.work scT).cells 0 = Γ.start ∧
      (∀ j, 1 ≤ j → (c'.work scT).cells j ≠ Γ.start) ∧
      1 ≤ (c'.work scT).head ∧ (c'.work scT).head ≤ stSyms.length + 11 ∧
      (∀ j, (c'.work scT).head ≤ j → (c'.work scT).cells j = Γ.blank) ∧
      c'.work vIn = c.work vIn ∧ c'.work vWk = c.work vWk ∧
      c'.work vOut = c.work vOut ∧
      c'.input = c.input ∧ c'.output = c.output := by
  have hS_wns := (Tape.HoldsExact.startInvariant hSt).2
  have hE_wns := (Tape.HoldsExact.startInvariant hSc).2
  have hsc_read : (c.work scT).read ≠ Γ.start :=
    SimInv.read_ne_start_of_holdsExact hSc (by rw [hschead])
  have hsc_blank : ∀ j, 1 ≤ j → (c.work scT).cells j = Γ.blank := by
    intro j hj
    rw [show j = (j - 1) + 1 by omega]
    exact Tape.HoldsExact.cells_ge hSc (Nat.zero_le _)
  have hoth6 : ∀ i : Fin 6, i ≠ stT → i ≠ dsT → (c.work i).read ≠ Γ.start := by
    intro i hiS hiD
    rcases i with ⟨iv, hv⟩
    rcases iv with _ | _ | _ | _ | _ | _ | n
    · exact hv0s
    · exact hv1s
    · exact hv2s
    · exact absurd rfl hiS
    · exact absurd rfl hiD
    · exact hsc_read
    · exact absurd hv (by omega)
  -- Reduce to reaching skipSeg at some offset `nd ≤ |seg|` of the segment.
  suffices h : ∃ (cₘ : Cfg 6 bodyTM.Q) (tₘ nd : ℕ),
      tₘ + (seg.length - nd) + 1 ≤ 2 * stSyms.length + seg.length + 19 ∧
      nd ≤ seg.length ∧
      bodyTM.reachesIn tₘ c cₘ ∧
      cₘ.state = skipSeg f ∧
      (cₘ.work stT).cells = (c.work stT).cells ∧
      1 ≤ (cₘ.work stT).head ∧ (cₘ.work stT).head ≤ stSyms.length + 1 ∧
      (cₘ.work dsT).cells = (c.work dsT).cells ∧
      (cₘ.work dsT).head = pos + nd ∧
      (cₘ.work scT).cells 0 = Γ.start ∧
      (∀ j, 1 ≤ j → (cₘ.work scT).cells j ≠ Γ.start) ∧
      1 ≤ (cₘ.work scT).head ∧ (cₘ.work scT).head ≤ stSyms.length + 11 ∧
      (∀ j, (cₘ.work scT).head ≤ j → (cₘ.work scT).cells j = Γ.blank) ∧
      cₘ.work vIn = c.work vIn ∧ cₘ.work vWk = c.work vWk ∧
      cₘ.work vOut = c.work vOut ∧
      cₘ.input = c.input ∧ cₘ.output = c.output by
    obtain ⟨cₘ, tₘ, nd, htb, hnd, hrₘ, hstₘ, hstC, hsh1, hsh2, hdsC, hdsH,
      hsc0, hscns, hsch1, hsch2, hscbl, hvi, hvw, hvo, hii, hoo⟩ := h
    have hv0r : (cₘ.work vIn).read ≠ Γ.start := by rw [hvi]; exact hv0s
    have hv1r : (cₘ.work vWk).read ≠ Γ.start := by rw [hvw]; exact hv1s
    have hv2r : (cₘ.work vOut).read ≠ Γ.start := by rw [hvo]; exact hv2s
    have hstr : (cₘ.work stT).read ≠ Γ.start := by
      show (cₘ.work stT).cells (cₘ.work stT).head ≠ Γ.start
      rw [hstC]
      exact hS_wns _ hsh1
    have hscr : (cₘ.work scT).read ≠ Γ.start := by
      show (cₘ.work scT).cells (cₘ.work scT).head ≠ Γ.start
      exact hscns _ hsch1
    obtain ⟨c', hr', hst', hwtD', hin', hout', hoth'⟩ :=
      scanRight_loop (cur := skipSeg f) (next := segCheck f) (t := dsT)
        (fun hcon => nomatch hcon) (arm_skipSeg · · · f)
        (c.work dsT).cells hWns (seg.length - nd) (pos + nd) (by omega)
        (fun j hj => by
          rw [show pos + nd + j = pos + (nd + j) by omega,
            hview (nd + j) (by omega)]
          intro hcon
          exact hseg_nb _ (List.getElem_mem (by omega)) (Γw.toΓ_eq_blank.mp hcon))
        (by rw [show pos + nd + (seg.length - nd) = pos + seg.length by omega]
            exact hviewE)
        cₘ hstₘ hdsC hdsH
        (by rw [hii]; exact hin) (by rw [hoo]; exact hout)
        (fun i hiD => by
          rcases i with ⟨iv, hv⟩
          rcases iv with _ | _ | _ | _ | _ | _ | n
          · exact hv0r
          · exact hv1r
          · exact hv2r
          · exact hstr
          · exact absurd rfl hiD
          · exact hscr
          · exact absurd hv (by omega))
    have hscF : c'.work scT = cₘ.work scT := hoth' scT (by decide)
    have hstF : c'.work stT = cₘ.work stT := hoth' stT (by decide)
    refine ⟨c', tₘ + (seg.length - nd + 1), by omega,
      reachesIn_trans _ hrₘ hr', hst',
      by rw [hstF]; exact hstC, by rw [hstF]; exact hsh1,
      by rw [hstF]; exact hsh2,
      by rw [hwtD'], by rw [hwtD']; show pos + nd + (seg.length - nd) + 1 = _; omega,
      by rw [hscF]; exact hsc0, by rw [hscF]; exact hscns,
      by rw [hscF]; exact hsch1, by rw [hscF]; exact hsch2,
      by rw [hscF]; exact hscbl,
      by rw [hoth' vIn (by decide)]; exact hvi,
      by rw [hoth' vWk (by decide)]; exact hvw,
      by rw [hoth' vOut (by decide)]; exact hvo,
      by rw [hin']; exact hii, by rw [hout']; exact hoo⟩
  -- Find the first failure point.
  by_cases hc1 : seg.take stSyms.length = stSyms
  case neg =>
    -- Path A: the state field fails (symbol mismatch or short segment).
    obtain ⟨n, hnA, hnB, hagree, hmmn⟩ :=
      exists_first_mismatch hst_nb
        (fun s hs => hseg_nb s (List.mem_of_mem_take hs))
        (fun h => hc1 h.symm)
    have hnw : n < stSyms.length := by
      by_contra hcon
      have h1 : (stSyms[n]?).getD Γw.blank = Γw.blank := getD_ge (by omega)
      have h2 : ((seg.take stSyms.length)[n]?).getD Γw.blank = Γw.blank :=
        getD_ge (by rw [List.length_take]; omega)
      exact hmmn (h1.trans h2.symm)
    have hnm : n ≤ seg.length := by
      rw [List.length_take] at hnB
      omega
    have hWn : (c.work dsT).cells (pos + n)
        = (((seg.take stSyms.length)[n]?).getD Γw.blank).toΓ := by
      rcases Nat.lt_or_ge n (seg.take stSyms.length).length with hlt | hge
      · have hnm' : n < seg.length := by rw [List.length_take] at hlt; omega
        rw [getD_lt hlt, hview n hnm']
        exact congrArg Γw.toΓ (List.getElem_take).symm
      · have hnm' : n = seg.length := by rw [List.length_take] at hge; omega
        rw [getD_ge hge, hnm']
        exact hviewE
    have hSn : (c.work stT).cells (1 + n) = (stSyms[n]).toΓ := by
      rw [show 1 + n = n + 1 by omega]
      exact Tape.HoldsExact.cells_lt hSt hnw
    obtain ⟨c₁, hr₁, hst₁, hwtS₁, hwtD₁, hin₁, hout₁, hoth₁⟩ :=
      cmpQ_mismatch_loop f (c.work stT).cells (c.work dsT).cells hS_wns hWns
        n 1 pos (by omega) hpos
        (fun j hj => by
          obtain ⟨hje, hjb⟩ := hagree j hj
          have hjw : j < stSyms.length := by omega
          have hjm : j < seg.length := by
            have hb : ((seg.take stSyms.length)[j]?).getD Γw.blank
                ≠ Γw.blank := by rw [← hje]; exact hjb
            have := lt_of_getD_ne_blank hb
            rw [List.length_take] at this
            omega
          have hS : (c.work stT).cells (1 + j) = (stSyms[j]).toΓ := by
            rw [show 1 + j = j + 1 by omega]
            exact Tape.HoldsExact.cells_lt hSt hjw
          refine ⟨?_, ?_⟩
          · rw [hS, hview j hjm]
            refine congrArg Γw.toΓ ?_
            rw [← getD_lt hjw, hje, getD_lt (by rw [List.length_take]; omega)]
            exact List.getElem_take
          · rw [hS]
            intro hcon
            exact hst_nb _ (List.getElem_mem hjw) (Γw.toΓ_eq_blank.mp hcon))
        (by
          rw [hSn]
          intro hcon
          exact hst_nb _ (List.getElem_mem hnw) (Γw.toΓ_eq_blank.mp hcon))
        (by
          rintro ⟨-, heq⟩
          rw [hSn, hWn] at heq
          exact hmmn (by rw [getD_lt hnw]; exact Γw.toΓ_inj heq))
        c hst rfl hsthead rfl hdhead hin hout hoth6
    exact ⟨c₁, n + 1, n, by omega, hnm, hr₁, hst₁,
      by rw [hwtS₁], by rw [hwtS₁]; show 1 ≤ 1 + n; omega,
      by rw [hwtS₁]; show 1 + n ≤ _; omega,
      by rw [hwtD₁], by rw [hwtD₁],
      by rw [hoth₁ scT (by decide) (by decide)]; exact hSc.1,
      by rw [hoth₁ scT (by decide) (by decide)]; exact hE_wns,
      by rw [hoth₁ scT (by decide) (by decide)]; omega,
      by rw [hoth₁ scT (by decide) (by decide), hschead]; omega,
      by rw [hoth₁ scT (by decide) (by decide), hschead]
         exact fun j hj => hsc_blank j hj,
      hoth₁ vIn (by decide) (by decide), hoth₁ vWk (by decide) (by decide),
      hoth₁ vOut (by decide) (by decide), hin₁, hout₁⟩
  case pos =>
    -- The state field matches: run the cmpQ match exit.
    have hwm : stSyms.length ≤ seg.length := by
      have := congrArg List.length hc1
      rw [List.length_take] at this
      omega
    have hseg_st : ∀ j, (hj : j < stSyms.length) →
        seg[j]'(by omega) = stSyms[j] := by
      intro j hj
      have h2 : j < (seg.take stSyms.length).length := by
        rw [List.length_take]; omega
      have h1 : (seg.take stSyms.length)[j]'h2 = seg[j]'(by omega) :=
        List.getElem_take
      exact h1.symm.trans (List.getElem_of_eq hc1 h2)
    obtain ⟨c₁, hr₁, hst₁, hwtS₁, hwtD₁, hin₁, hout₁, hoth₁⟩ :=
      cmpQ_match_loop f (c.work stT).cells (c.work dsT).cells hS_wns hWns
        stSyms.length 1 pos (by omega) hpos
        (fun j hj => by
          have hS : (c.work stT).cells (1 + j) = (stSyms[j]).toΓ := by
            rw [show 1 + j = j + 1 by omega]
            exact Tape.HoldsExact.cells_lt hSt hj
          refine ⟨?_, ?_⟩
          · rw [hS, hview j (by omega), hseg_st j hj]
          · rw [hS]
            intro hcon
            exact hst_nb _ (List.getElem_mem hj) (Γw.toΓ_eq_blank.mp hcon))
        (by
          rw [show 1 + stSyms.length = stSyms.length + 1 by omega]
          exact Tape.HoldsExact.cells_ge hSt (Nat.le_refl _))
        c hst rfl hsthead rfl hdhead hin hout hoth6
    by_cases hc2 : (seg.drop stSyms.length).take 6 = keyCells f v0 v1 v2
    case neg =>
      -- Path B: a key-symbol cell fails (or the segment ends inside the key).
      obtain ⟨n, hnA, hnB, hagree, hmmn⟩ :=
        exists_first_mismatch (keyCells_ne_blank f v0 v1 v2)
          (fun s hs => hseg_nb s (List.mem_of_mem_drop (List.mem_of_mem_take hs)))
          (fun h => hc2 h.symm)
      rw [keyCells_length] at hnA
      have hn6 : n < 6 := by
        by_contra hcon
        have h1 : ((keyCells f v0 v1 v2)[n]?).getD Γw.blank = Γw.blank :=
          getD_ge (by rw [keyCells_length]; omega)
        have h2 : (((seg.drop stSyms.length).take 6)[n]?).getD Γw.blank
            = Γw.blank :=
          getD_ge (by rw [List.length_take]; omega)
        exact hmmn (h1.trans h2.symm)
      have hnm : stSyms.length + n ≤ seg.length := by
        rw [List.length_take, List.length_drop] at hnB
        omega
      have hWn : (c.work dsT).cells (pos + stSyms.length + n)
          = ((((seg.drop stSyms.length).take 6)[n]?).getD Γw.blank).toΓ := by
        rcases Nat.lt_or_ge n ((seg.drop stSyms.length).take 6).length
          with hlt | hge
        · have hnm' : stSyms.length + n < seg.length := by
            rw [List.length_take, List.length_drop] at hlt; omega
          rw [getD_lt hlt,
            show pos + stSyms.length + n = pos + (stSyms.length + n) by omega,
            hview _ hnm']
          refine congrArg Γw.toΓ ?_
          rw [List.getElem_take, List.getElem_drop]
        · have hnm' : stSyms.length + n = seg.length := by
            rw [List.length_take, List.length_drop] at hge; omega
          rw [getD_ge hge,
            show pos + stSyms.length + n = pos + (stSyms.length + n) by omega,
            hnm']
          exact hviewE
      obtain ⟨c₂, hr₂, hst₂, hwtD₂, hin₂, hout₂, hoth₂⟩ :=
        cmpS_mismatch_loop f v0 v1 v2 (c.work dsT).cells hWns
          n 0 (by simp; omega) (pos + stSyms.length) (by omega)
          (fun j hj hj6 => by
            obtain ⟨hje, hjb⟩ := hagree j hj
            have hjm : stSyms.length + j < seg.length := by
              have hb : (((seg.drop stSyms.length).take 6)[j]?).getD Γw.blank
                  ≠ Γw.blank := by rw [← hje]; exact hjb
              have := lt_of_getD_ne_blank hb
              rw [List.length_take, List.length_drop] at this
              omega
            have hW : (c.work dsT).cells (pos + stSyms.length + j)
                = (seg[stSyms.length + j]'hjm).toΓ := by
              rw [show pos + stSyms.length + j = pos + (stSyms.length + j)
                by omega]
              exact hview _ hjm
            have hkc := keyCells_get f v0 v1 v2 ⟨j, by omega⟩
            refine ⟨?_, ?_⟩
            · rw [hW]
              have hBA : seg[stSyms.length + j]'hjm
                  = (keyCells f v0 v1 v2)[j]'(by rw [keyCells_length]; omega) := by
                have hB : (((seg.drop stSyms.length).take 6)[j]?).getD Γw.blank
                    = seg[stSyms.length + j]'hjm := by
                  rw [getD_lt (by rw [List.length_take, List.length_drop]; omega)]
                  rw [List.getElem_take, List.getElem_drop]
                rw [← hB, ← hje]
                exact getD_lt (by rw [keyCells_length]; omega)
              rw [hBA, hkc]
              exact congrArg (keyCell f v0 v1 v2) (Fin.ext (by simp))
            · rw [hW]
              intro hcon
              exact hseg_nb _ (List.getElem_mem hjm) (Γw.toΓ_eq_blank.mp hcon))
          (fun hn6' => by
            rintro ⟨heq, hnbW⟩
            have hkc := keyCells_get f v0 v1 v2 ⟨n, hn6⟩
            have hidx : keyCell f v0 v1 v2 ⟨(0 : Fin 6).val + n, hn6'⟩
                = keyCell f v0 v1 v2 ⟨n, hn6⟩ :=
              congrArg (keyCell f v0 v1 v2) (Fin.ext (by simp))
            rw [hWn, hidx, ← hkc] at heq
            exact hmmn ((getD_lt (by rw [keyCells_length]; omega)).trans
              (Γw.toΓ_inj heq).symm))
          c₁ hst₁
          (by rw [hoth₁ vIn (by decide) (by decide)]; exact hv0)
          (by rw [hoth₁ vWk (by decide) (by decide)]; exact hv1)
          (by rw [hoth₁ vOut (by decide) (by decide)]; exact hv2)
          (by rw [hwtD₁]) (by rw [hwtD₁])
          (by rw [hin₁]; exact hin) (by rw [hout₁]; exact hout)
          (fun i hiD => by
            by_cases hiS : i = stT
            · subst hiS
              rw [hwtS₁, Tape.read]
              exact hS_wns (1 + stSyms.length) (by omega)
            · rw [hoth₁ i hiS hiD]
              exact hoth6 i hiS hiD)
      refine ⟨c₂, (stSyms.length + 1) + (n + 1), stSyms.length + n,
        by omega, hnm, reachesIn_trans _ hr₁ hr₂, hst₂, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hoth₂ stT (by decide), hwtS₁]
      · rw [hoth₂ stT (by decide), hwtS₁]
        show 1 ≤ 1 + stSyms.length; omega
      · rw [hoth₂ stT (by decide), hwtS₁]
        show 1 + stSyms.length ≤ _; omega
      · rw [hwtD₂]
      · rw [hwtD₂]
        show pos + stSyms.length + n = _; omega
      · rw [hoth₂ scT (by decide), hoth₁ scT (by decide) (by decide)]
        exact hSc.1
      · rw [hoth₂ scT (by decide), hoth₁ scT (by decide) (by decide)]
        exact hE_wns
      · rw [hoth₂ scT (by decide), hoth₁ scT (by decide) (by decide), hschead]
      · rw [hoth₂ scT (by decide), hoth₁ scT (by decide) (by decide), hschead]
        omega
      · rw [hoth₂ scT (by decide), hoth₁ scT (by decide) (by decide), hschead]
        exact fun j hj => hsc_blank j hj
      · rw [hoth₂ vIn (by decide), hoth₁ vIn (by decide) (by decide)]
      · rw [hoth₂ vWk (by decide), hoth₁ vWk (by decide) (by decide)]
      · rw [hoth₂ vOut (by decide), hoth₁ vOut (by decide) (by decide)]
      · rw [hin₂, hin₁]
      · rw [hout₂, hout₁]
    case pos =>
      -- The key matches fully: run the cmpS match exit, then the value copy
      -- hits the segment's end early (the value is short — MachMatch fails
      -- exactly on its length conjunct).
      have hw6 : stSyms.length + 6 ≤ seg.length := by
        have := congrArg List.length hc2
        rw [List.length_take, List.length_drop, keyCells_length] at this
        omega
      have hm16 : seg.length < 2 * stSyms.length + 16 := by
        by_contra hcon
        exact hMM ⟨hc1, hc2, by omega⟩
      have hkey_st : ∀ i, (hi : i < 6) →
          seg[stSyms.length + i]'(by omega)
            = (keyCells f v0 v1 v2)[i]'(by rw [keyCells_length]; omega) := by
        intro i hi
        have h2 : i < ((seg.drop stSyms.length).take 6).length := by
          rw [List.length_take, List.length_drop]; omega
        have h1 : ((seg.drop stSyms.length).take 6)[i]'h2
            = seg[stSyms.length + i]'(by omega) := by
          rw [List.getElem_take, List.getElem_drop]
        exact h1.symm.trans (List.getElem_of_eq hc2 h2)
      obtain ⟨c₂, hr₂, hst₂, hwtS₂, hwtD₂, hin₂, hout₂, hoth₂⟩ :=
        cmpS_match_loop f v0 v1 v2 (c.work dsT).cells (c.work stT).cells
          hWns hS_wns 5 0 rfl (1 + stSyms.length) (pos + stSyms.length)
          (by omega) (by omega)
          (fun j hj hj6 => by
            have hjm : stSyms.length + j < seg.length := by omega
            have hW : (c.work dsT).cells (pos + stSyms.length + j)
                = (seg[stSyms.length + j]'hjm).toΓ := by
              rw [show pos + stSyms.length + j = pos + (stSyms.length + j)
                by omega]
              exact hview _ hjm
            have hkc := keyCells_get f v0 v1 v2 ⟨j, by omega⟩
            refine ⟨?_, ?_⟩
            · rw [hW, hkey_st j (by omega), hkc]
              exact congrArg (keyCell f v0 v1 v2) (Fin.ext (by simp))
            · rw [hW]
              intro hcon
              exact hseg_nb _ (List.getElem_mem hjm) (Γw.toΓ_eq_blank.mp hcon))
          c₁ hst₁
          (by rw [hoth₁ vIn (by decide) (by decide)]; exact hv0)
          (by rw [hoth₁ vWk (by decide) (by decide)]; exact hv1)
          (by rw [hoth₁ vOut (by decide) (by decide)]; exact hv2)
          (by rw [hwtS₁]) (by rw [hwtS₁])
          (by rw [hwtD₁]) (by rw [hwtD₁])
          (by rw [hin₁]; exact hin) (by rw [hout₁]; exact hout)
          (fun i hiS hiD => by
            rw [hoth₁ i hiS hiD]
            exact hoth6 i hiS hiD)
      by_cases hc3 : seg.length < 2 * stSyms.length + 6
      case pos =>
        -- Path C: the □ lands inside the q'-field copy.
        obtain ⟨c₃, hr₃, hst₃, hwtS₃, hwtD₃, hwtE₃, hin₃, hout₃, hoth₃⟩ :=
          copyQ'_blank_loop f (c.work stT).cells (c.work dsT).cells
            hS_wns hWns (seg.length - (stSyms.length + 6)) (c.work scT).cells
            hE_wns stSyms.length (pos + stSyms.length + 6) 1
            (by omega) (by omega) (by omega)
            (fun j hj => by
              rw [show pos + stSyms.length + 6 + j
                  = pos + (stSyms.length + 6 + j) by omega,
                hview (stSyms.length + 6 + j) (by omega)]
              intro hcon
              exact hseg_nb _ (List.getElem_mem (by omega))
                (Γw.toΓ_eq_blank.mp hcon))
            (by
              rw [show pos + stSyms.length + 6 + (seg.length - (stSyms.length + 6))
                  = pos + seg.length by omega]
              exact hviewE)
            c₂ hst₂
            (by rw [hwtS₂]) (by rw [hwtS₂]; show 1 + stSyms.length - 1 = _; omega)
            (by rw [hwtD₂]) (by rw [hwtD₂])
            (by rw [hoth₂ scT (by decide) (by decide),
              hoth₁ scT (by decide) (by decide)])
            (by rw [hoth₂ scT (by decide) (by decide),
              hoth₁ scT (by decide) (by decide)]; exact hschead)
            (by rw [hin₂, hin₁]; exact hin) (by rw [hout₂, hout₁]; exact hout)
            (fun i hiS hiD hiE => by
              rw [hoth₂ i hiS hiD, hoth₁ i hiS hiD]
              exact hoth6 i hiS hiD)
        have hE₁ : ∀ i, (c₃.work scT).cells i
            = if 1 ≤ i ∧ i < 1 + (seg.length - (stSyms.length + 6)) then
                (c.work dsT).cells (pos + stSyms.length + 6 + (i - 1))
              else (c.work scT).cells i := by
          intro i
          rw [hwtE₃]
        refine ⟨c₃, (stSyms.length + 1) + (5 + 1)
            + (seg.length - (stSyms.length + 6) + 1), seg.length,
          by omega, Nat.le_refl _,
          reachesIn_trans _ (reachesIn_trans _ hr₁ hr₂) hr₃, hst₃,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hwtS₃]
        · rw [hwtS₃]
          show 1 ≤ stSyms.length - (seg.length - (stSyms.length + 6)); omega
        · rw [hwtS₃]
          show stSyms.length - (seg.length - (stSyms.length + 6)) ≤ _; omega
        · rw [hwtD₃]
        · rw [hwtD₃]
          show pos + stSyms.length + 6 + (seg.length - (stSyms.length + 6)) = _
          omega
        · rw [hE₁ 0, ite_eq_right (by omega)]
          exact hSc.1
        · intro j hj
          rw [hE₁ j]
          by_cases hcase : 1 ≤ j ∧ j < 1 + (seg.length - (stSyms.length + 6))
          · rw [ite_eq_left hcase]
            exact hWns _ (by omega)
          · rw [ite_eq_right hcase]
            exact hE_wns j hj
        · rw [hwtE₃]
          show 1 ≤ 1 + (seg.length - (stSyms.length + 6)); omega
        · rw [hwtE₃]
          show 1 + (seg.length - (stSyms.length + 6)) ≤ _; omega
        · intro j hj
          have hj' : 1 + (seg.length - (stSyms.length + 6)) ≤ j := by
            rw [hwtE₃] at hj
            exact hj
          rw [hE₁ j, ite_eq_right (by omega)]
          exact hsc_blank j (by omega)
        · rw [hoth₃ vIn (by decide) (by decide) (by decide),
            hoth₂ vIn (by decide) (by decide),
            hoth₁ vIn (by decide) (by decide)]
        · rw [hoth₃ vWk (by decide) (by decide) (by decide),
            hoth₂ vWk (by decide) (by decide),
            hoth₁ vWk (by decide) (by decide)]
        · rw [hoth₃ vOut (by decide) (by decide) (by decide),
            hoth₂ vOut (by decide) (by decide),
            hoth₁ vOut (by decide) (by decide)]
        · rw [hin₃, hin₂, hin₁]
        · rw [hout₃, hout₂, hout₁]
      case neg =>
        -- Path D: the q' copy completes; the □ lands among the action cells.
        obtain ⟨c₃, hr₃, hst₃, hwtS₃, hwtD₃, hwtE₃, hin₃, hout₃, hoth₃⟩ :=
          copyQ'_copy_loop f (c.work stT).cells (c.work dsT).cells hSt.1
            hS_wns hWns stSyms.length (c.work scT).cells hE_wns
            (pos + stSyms.length + 6) 1 (by omega) (by omega)
            (fun j hj => by
              rw [show pos + stSyms.length + 6 + j
                  = pos + (stSyms.length + 6 + j) by omega,
                hview (stSyms.length + 6 + j) (by omega)]
              intro hcon
              exact hseg_nb _ (List.getElem_mem (by omega))
                (Γw.toΓ_eq_blank.mp hcon))
            c₂ hst₂
            (by rw [hwtS₂]) (by rw [hwtS₂]; show 1 + stSyms.length - 1 = _; omega)
            (by rw [hwtD₂]) (by rw [hwtD₂])
            (by rw [hoth₂ scT (by decide) (by decide),
              hoth₁ scT (by decide) (by decide)])
            (by rw [hoth₂ scT (by decide) (by decide),
              hoth₁ scT (by decide) (by decide)]; exact hschead)
            (by rw [hin₂, hin₁]; exact hin) (by rw [hout₂, hout₁]; exact hout)
            (fun i hiS hiD hiE => by
              rw [hoth₂ i hiS hiD, hoth₁ i hiS hiD]
              exact hoth6 i hiS hiD)
        obtain ⟨c₄, hr₄, hst₄, hwtD₄, hwtE₄, hin₄, hout₄, hoth₄⟩ :=
          copyAct_blank_loop f (c.work dsT).cells hWns
            (seg.length - (2 * stSyms.length + 6)) 0 (by simp; omega)
            (fun j => if 1 ≤ j ∧ j < 1 + stSyms.length then
                (c.work dsT).cells (pos + stSyms.length + 6 + (j - 1))
              else (c.work scT).cells j)
            (by
              intro i hi
              by_cases hcase : 1 ≤ i ∧ i < 1 + stSyms.length
              · rw [ite_eq_left hcase]
                exact hWns _ (by omega)
              · rw [ite_eq_right hcase]
                exact hE_wns i hi)
            (pos + stSyms.length + 6 + stSyms.length) (1 + stSyms.length)
            (by omega) (by omega)
            (fun i hi => by
              rw [show pos + stSyms.length + 6 + stSyms.length + i
                  = pos + (stSyms.length + 6 + stSyms.length + i) by omega,
                hview (stSyms.length + 6 + stSyms.length + i) (by omega)]
              intro hcon
              exact hseg_nb _ (List.getElem_mem (by omega))
                (Γw.toΓ_eq_blank.mp hcon))
            (by
              rw [show pos + stSyms.length + 6 + stSyms.length
                    + (seg.length - (2 * stSyms.length + 6))
                  = pos + seg.length by omega]
              exact hviewE)
            c₃ hst₃
            (by rw [hwtD₃]) (by rw [hwtD₃])
            (by rw [hwtE₃]) (by rw [hwtE₃])
            (by rw [hin₃, hin₂, hin₁]; exact hin)
            (by rw [hout₃, hout₂, hout₁]; exact hout)
            (fun i hiD hiE => by
              by_cases hiS : i = stT
              · subst hiS
                rw [hwtS₃, Tape.read]
                exact hS_wns 1 (by omega)
              · rw [hoth₃ i hiS hiD hiE, hoth₂ i hiS hiD, hoth₁ i hiS hiD]
                exact hoth6 i hiS hiD)
        have hE₂ : ∀ i, (c₄.work scT).cells i
            = if 1 + stSyms.length ≤ i ∧
                  i < 1 + stSyms.length + (seg.length - (2 * stSyms.length + 6)) then
                (c.work dsT).cells (pos + stSyms.length + 6 + stSyms.length
                  + (i - (1 + stSyms.length)))
              else if 1 ≤ i ∧ i < 1 + stSyms.length then
                (c.work dsT).cells (pos + stSyms.length + 6 + (i - 1))
              else (c.work scT).cells i := by
          intro i
          rw [hwtE₄]
        refine ⟨c₄, (stSyms.length + 1) + (5 + 1) + (stSyms.length + 1)
            + (seg.length - (2 * stSyms.length + 6) + 1), seg.length,
          by omega, Nat.le_refl _,
          reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _ hr₁ hr₂) hr₃)
            hr₄,
          hst₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hoth₄ stT (by decide) (by decide), hwtS₃]
        · rw [hoth₄ stT (by decide) (by decide), hwtS₃]
        · rw [hoth₄ stT (by decide) (by decide), hwtS₃]
          show (1 : ℕ) ≤ _; omega
        · rw [hwtD₄]
        · rw [hwtD₄]
          show pos + stSyms.length + 6 + stSyms.length
              + (seg.length - (2 * stSyms.length + 6)) = _
          omega
        · rw [hE₂ 0, ite_eq_right (by omega), ite_eq_right (by omega)]
          exact hSc.1
        · intro j hj
          rw [hE₂ j]
          by_cases hcase : 1 + stSyms.length ≤ j ∧
              j < 1 + stSyms.length + (seg.length - (2 * stSyms.length + 6))
          · rw [ite_eq_left hcase]
            exact hWns _ (by omega)
          · rw [ite_eq_right hcase]
            by_cases hcase' : 1 ≤ j ∧ j < 1 + stSyms.length
            · rw [ite_eq_left hcase']
              exact hWns _ (by omega)
            · rw [ite_eq_right hcase']
              exact hE_wns j hj
        · rw [hwtE₄]
          show 1 ≤ 1 + stSyms.length + (seg.length - (2 * stSyms.length + 6))
          omega
        · rw [hwtE₄]
          show 1 + stSyms.length + (seg.length - (2 * stSyms.length + 6)) ≤ _
          omega
        · intro j hj
          have hj' : 1 + stSyms.length + (seg.length - (2 * stSyms.length + 6))
              ≤ j := by
            rw [hwtE₄] at hj
            exact hj
          rw [hE₂ j, ite_eq_right (by omega), ite_eq_right (by omega)]
          exact hsc_blank j (by omega)
        · rw [hoth₄ vIn (by decide) (by decide),
            hoth₃ vIn (by decide) (by decide) (by decide),
            hoth₂ vIn (by decide) (by decide),
            hoth₁ vIn (by decide) (by decide)]
        · rw [hoth₄ vWk (by decide) (by decide),
            hoth₃ vWk (by decide) (by decide) (by decide),
            hoth₂ vWk (by decide) (by decide),
            hoth₁ vWk (by decide) (by decide)]
        · rw [hoth₄ vOut (by decide) (by decide),
            hoth₃ vOut (by decide) (by decide) (by decide),
            hoth₂ vOut (by decide) (by decide),
            hoth₁ vOut (by decide) (by decide)]
        · rw [hin₄, hin₃, hin₂, hin₁]
        · rw [hout₄, hout₃, hout₂, hout₁]

-- ════════════════════════════════════════════════════════════════════════
-- The default step, and machFind terminators
-- ════════════════════════════════════════════════════════════════════════

/-- **The default step packaged for the loop**: from `segCheck f` reading
    `□` on the desc tape, one step to `dfScr` applying the sanitized
    default moves (trick 4) to the three virtual tapes; every other tape
    exactly preserved. -/
private theorem segCheck_blank_step {c : Cfg 6 bodyTM.Q} {f : VFlags}
    (hst : c.state = segCheck f)
    (hdc : (c.work dsT).read = Γ.blank)
    (hv0s : (c.work vIn).read ≠ Γ.start) (hv1s : (c.work vWk).read ≠ Γ.start)
    (hv2s : (c.work vOut).read ≠ Γ.start)
    (hstT : (c.work stT).read ≠ Γ.start) (hscT : (c.work scT).read ≠ Γ.start)
    (hin : c.input.read ≠ Γ.start) (hout : c.output.read ≠ Γ.start) :
    ∃ c', bodyTM.reachesIn 1 c c' ∧ c'.state = dfScr ∧
      c'.work vIn = (c.work vIn).writeAndMove
        (readBackWrite ((c.work vIn).read)).toΓ
        (if f.1 then Dir3.right else Dir3.stay) ∧
      c'.work vWk = (c.work vWk).writeAndMove
        (readBackWrite ((c.work vWk).read)).toΓ
        (if f.2.1 then Dir3.right else Dir3.stay) ∧
      c'.work vOut = (c.work vOut).writeAndMove
        (readBackWrite ((c.work vOut).read)).toΓ
        (if f.2.2 then Dir3.right else Dir3.stay) ∧
      (∀ i, i ≠ vIn → i ≠ vWk → i ≠ vOut → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output := by
  have hdsT : (c.work dsT).read ≠ Γ.start := by
    rw [hdc]; exact fun h => nomatch h
  have harm := arm_segCheck c.input.read (fun i => (c.work i).read)
    c.output.read f
  rw [ite_eq_left hdc] at harm
  have hstep := step_act3 (by rw [hst]; exact fun h => nomatch h)
    (by rw [hst]; exact harm)
  refine ⟨_, .step hstep .zero, rfl, ?_, ?_, ?_, ?_,
    idle_input_id hin, idle_tape_id hout⟩
  · show (c.work vIn).writeAndMove (readBackWrite ((c.work vIn).read)).toΓ
      (if (c.work vIn).read = Γ.start then Dir3.right
        else if f.1 then Dir3.right else Dir3.stay) = _
    rw [ite_eq_right hv0s]
  · show (c.work vWk).writeAndMove (readBackWrite ((c.work vWk).read)).toΓ
      (if (c.work vWk).read = Γ.start then Dir3.right
        else if f.2.1 then Dir3.right else Dir3.stay) = _
    rw [ite_eq_right hv1s]
  · show (c.work vOut).writeAndMove (readBackWrite ((c.work vOut).read)).toΓ
      (if (c.work vOut).read = Γ.start then Dir3.right
        else if f.2.2 then Dir3.right else Dir3.stay) = _
    rw [ite_eq_right hv2s]
  · intro i hi0 hi1 hi2
    show (if i = vIn then _ else if i = vWk then _ else if i = vOut then _
      else _) = _
    rw [ite_eq_right hi0, ite_eq_right hi1, ite_eq_right hi2]
    refine idle_tape_id ?_
    rcases i with ⟨iv, hv⟩
    rcases iv with _ | _ | _ | _ | _ | _ | n
    · exact absurd rfl hi0
    · exact absurd rfl hi1
    · exact absurd rfl hi2
    · exact hstT
    · exact hdsT
    · exact hscT
    · exact absurd hv (by omega)

/-- A region whose head cell is `□` (or which is empty) is an exhausted
    table for `machFind`. -/
private theorem machFind_none_of_head_blank {w : ℕ} {a b : List Γw}
    {R : List Γw} (h : (R[0]?).getD Γw.blank = Γw.blank) :
    machFind w a b R = none := by
  cases R with
  | nil => simp [machFind]
  | cons s rest =>
    have hs : s = Γw.blank := by simpa using h
    subst hs
    simp [machFind]

-- ════════════════════════════════════════════════════════════════════════
-- Time-bound arithmetic (products kept out of omega)
-- ════════════════════════════════════════════════════════════════════════

private theorem le_mul_time {w r a : ℕ} (ha : a ≤ 2 * w + r + 20) :
    a ≤ (r + 2) * (4 * w + 60) := by
  calc a ≤ (2 * w + 20) + r := by omega
    _ ≤ 2 * (4 * w + 60) + r * (4 * w + 60) :=
        Nat.add_le_add (by omega) (Nat.le_mul_of_pos_right _ (by omega))
    _ = (r + 2) * (4 * w + 60) := by
        rw [Nat.add_mul]
        exact Nat.add_comm _ _

private theorem time_bound_step {w m r' a b : ℕ}
    (ha : a ≤ 4 * w + m + 34) (hb : b ≤ (r' + 2) * (4 * w + 60)) :
    a + b ≤ (m + 1 + r' + 2) * (4 * w + 60) := by
  refine le_trans (Nat.add_le_add ha hb) ?_
  have hsplit : (m + 1 + (r' + 2)) * (4 * w + 60)
      = (m + 1) * (4 * w + 60) + (r' + 2) * (4 * w + 60) :=
    Nat.add_mul _ _ _
  rw [show m + 1 + r' + 2 = m + 1 + (r' + 2) from by omega, hsplit]
  refine Nat.add_le_add ?_ (Nat.le_refl _)
  calc 4 * w + m + 34 ≤ (4 * w + 60) + m := by omega
    _ ≤ (4 * w + 60) + m * (4 * w + 60) :=
        Nat.add_le_add (Nat.le_refl _) (Nat.le_mul_of_pos_right _ (by omega))
    _ = (m + 1) * (4 * w + 60) := by
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.add_comm _ _

-- ════════════════════════════════════════════════════════════════════════
-- The match-loop induction
-- ════════════════════════════════════════════════════════════════════════

/-- The per-region statement of the match-loop induction (see `matchLoop`
    for the full reading), as a predicate on the remaining entry region. -/
private def MatchLoopStmt (f : VFlags) (v0 v1 v2 : Γ) (stSyms R : List Γw) :
    Prop :=
  ∀ (pos : ℕ) (c : Cfg 6 bodyTM.Q),
    (∀ s rest, R = Γw.blank :: s :: rest → s = Γw.blank) →
    c.state = cmpQ f →
    (∀ j, (c.work dsT).cells (pos + j) = ((R[j]?).getD Γw.blank).toΓ) →
    (c.work dsT).head = pos → 1 ≤ pos →
    (∀ j, 1 ≤ j → (c.work dsT).cells j ≠ Γ.start) →
    (c.work stT).HoldsExact stSyms → (c.work stT).head = 1 →
    (c.work scT).HoldsExact [] → (c.work scT).head = 1 →
    (c.work vIn).read = v0 → (c.work vWk).read = v1 → (c.work vOut).read = v2 →
    (c.work vIn).read ≠ Γ.start → (c.work vWk).read ≠ Γ.start →
    (c.work vOut).read ≠ Γ.start →
    c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
    ((∀ seg, machFind stSyms.length stSyms (keyCells f v0 v1 v2) R = some seg →
        ∃ c' t, t ≤ (R.length + 2) * (4 * stSyms.length + 60) ∧
          bodyTM.reachesIn t c c' ∧
          c'.state = appRewScr f ∧
          (c'.work scT).HoldsExact
            ((seg.drop (stSyms.length + 6)).take (stSyms.length + 10)) ∧
          (c'.work scT).head = stSyms.length + 10 + 1 ∧
          c'.work stT = c.work stT ∧
          (c'.work dsT).cells = (c.work dsT).cells ∧
          1 ≤ (c'.work dsT).head ∧ (c'.work dsT).head ≤ pos + R.length + 1 ∧
          c'.work vIn = c.work vIn ∧ c'.work vWk = c.work vWk ∧
          c'.work vOut = c.work vOut ∧
          c'.input = c.input ∧ c'.output = c.output) ∧
     (machFind stSyms.length stSyms (keyCells f v0 v1 v2) R = none →
        ∃ c' t, t ≤ (R.length + 2) * (4 * stSyms.length + 60) ∧
          bodyTM.reachesIn t c c' ∧
          c'.state = dfScr ∧
          c'.work vIn = (c.work vIn).writeAndMove (readBackWrite v0).toΓ
            (if f.1 then Dir3.right else Dir3.stay) ∧
          c'.work vWk = (c.work vWk).writeAndMove (readBackWrite v1).toΓ
            (if f.2.1 then Dir3.right else Dir3.stay) ∧
          c'.work vOut = (c.work vOut).writeAndMove (readBackWrite v2).toΓ
            (if f.2.2 then Dir3.right else Dir3.stay) ∧
          (c'.work stT).cells = (c.work stT).cells ∧
          1 ≤ (c'.work stT).head ∧ (c'.work stT).head ≤ stSyms.length + 1 ∧
          (c'.work dsT).cells = (c.work dsT).cells ∧
          1 ≤ (c'.work dsT).head ∧ (c'.work dsT).head ≤ pos + R.length + 1 ∧
          (c'.work scT).cells 0 = Γ.start ∧
          (∀ j, 1 ≤ j → (c'.work scT).cells j ≠ Γ.start) ∧
          1 ≤ (c'.work scT).head ∧ (c'.work scT).head ≤ stSyms.length + 11 ∧
          (∀ j, (c'.work scT).head ≤ j → 1 ≤ j →
            (c'.work scT).cells j = Γ.blank) ∧
          c'.input = c.input ∧ c'.output = c.output))

/-- One unfolding of the loop: handle the head segment, recursing (via the
    abstract induction hypothesis `ih`) on the rest of the region. -/
private theorem matchLoop_go (f : VFlags) (v0 v1 v2 : Γ) (stSyms : List Γw)
    (hst_nb : ∀ s ∈ stSyms, s ≠ Γw.blank) (R : List Γw)
    (ih : ∀ R' : List Γw, R'.length < R.length →
      MatchLoopStmt f v0 v1 v2 stSyms R') :
    MatchLoopStmt f v0 v1 v2 stSyms R := by
  intro pos c hRhd hst hcells hdhead hpos hWns hSt hsthead hSc hschead
    hv0 hv1 hv2 hv0s hv1s hv2s hin hout
  have hS_wns := (Tape.HoldsExact.startInvariant hSt).2
  -- the uniform segment view of the region
  have hview : ∀ j, (hj : j < (takeField R).1.length) →
      (c.work dsT).cells (pos + j) = ((takeField R).1[j]).toΓ := by
    intro j hj
    rw [hcells j, getD_field_lt hj]
  have hviewE : (c.work dsT).cells (pos + (takeField R).1.length)
      = Γ.blank := by
    rw [hcells (takeField R).1.length, getD_field_sep]
    rfl
  have hviewR : ∀ j,
      (c.work dsT).cells (pos + (takeField R).1.length + 1 + j)
        = (((takeField R).2[j]?).getD Γw.blank).toΓ := by
    intro j
    rw [show pos + (takeField R).1.length + 1 + j
        = pos + ((takeField R).1.length + 1 + j) by omega,
      hcells, getD_field_rest]
  have hseg_nb : ∀ s ∈ (takeField R).1, s ≠ Γw.blank :=
    takeField_fst_ne_blank R
  have hm_le : (takeField R).1.length ≤ R.length := takeField_fst_le R
  by_cases hMM : MachMatch stSyms.length stSyms (keyCells f v0 v1 v2)
    (takeField R).1
  · -- The head segment matches: `machFind` returns it; run the match round.
    obtain ⟨s, rest, rfl, hs⟩ : ∃ s rest, R = s :: rest ∧ s ≠ Γw.blank := by
      cases R with
      | nil =>
        exfalso
        obtain ⟨-, -, h22⟩ := hMM
        simp [takeField] at h22
      | cons s rest =>
        refine ⟨s, rest, rfl, fun hcon => ?_⟩
        subst hcon
        obtain ⟨-, -, h22⟩ := hMM
        simp [takeField] at h22
    have hfindR : machFind stSyms.length stSyms (keyCells f v0 v1 v2)
        (s :: rest) = some (takeField (s :: rest)).1 := by
      rw [machFind_cons_of_ne_blank hs, ite_eq_left hMM]
    obtain ⟨hMM1, hMM2, h22⟩ := hMM
    constructor
    · intro seg hfind'
      rw [hfindR] at hfind'
      injection hfind' with hseg
      subst hseg
      obtain ⟨c', t, ht, hr, hst', hscH, hscHd, hstF, hdsC, hdsH, hviF, hvwF,
        hvoF, hiF, hoF⟩ :=
        roundMatch f v0 v1 v2 stSyms (takeField (s :: rest)).1 hst_nb hseg_nb
          ⟨hMM1, hMM2, h22⟩ pos hpos c hst hview hdhead hWns
          hSt hsthead hSc hschead hv0 hv1 hv2 hv0s hv1s hv2s hin hout
      refine ⟨c', t, le_mul_time (by omega), hr, hst', hscH, hscHd, hstF,
        hdsC, ?_, ?_, hviF, hvwF, hvoF, hiF, hoF⟩
      · rw [hdsH]; omega
      · rw [hdsH]; omega
    · intro hfind'
      rw [hfindR] at hfind'
      exact absurd hfind' (by simp)
  · -- The head segment fails: mismatch round to `segCheck`.
    obtain ⟨c₁, t₁, ht₁, hr₁, hst₁, hstC₁, hsh1, hsh2, hdsC₁, hdsH₁, hsc0₁,
      hscns₁, hsch1, hsch2, hscbl₁, hvi₁, hvw₁, hvo₁, hii₁, hoo₁⟩ :=
      roundMismatch f v0 v1 v2 stSyms (takeField R).1 hst_nb hseg_nb hMM
        pos hpos c hst hview hviewE hdhead hWns hSt hsthead hSc hschead
        hv0 hv1 hv2 hv0s hv1s hv2s hin hout
    have hread₁ : (c₁.work dsT).read
        = (((takeField R).2[0]?).getD Γw.blank).toΓ := by
      show (c₁.work dsT).cells (c₁.work dsT).head = _
      rw [hdsH₁, hdsC₁,
        show pos + (takeField R).1.length + 1
          = pos + (takeField R).1.length + 1 + 0 by omega]
      exact hviewR 0
    have hv0r₁ : (c₁.work vIn).read ≠ Γ.start := by rw [hvi₁]; exact hv0s
    have hv1r₁ : (c₁.work vWk).read ≠ Γ.start := by rw [hvw₁]; exact hv1s
    have hv2r₁ : (c₁.work vOut).read ≠ Γ.start := by rw [hvo₁]; exact hv2s
    have hstr₁ : (c₁.work stT).read ≠ Γ.start := by
      show (c₁.work stT).cells (c₁.work stT).head ≠ Γ.start
      rw [hstC₁]
      exact hS_wns _ hsh1
    have hscr₁ : (c₁.work scT).read ≠ Γ.start := by
      show (c₁.work scT).cells (c₁.work scT).head ≠ Γ.start
      exact hscns₁ _ hsch1
    have hdsr₁ : (c₁.work dsT).read ≠ Γ.start := by
      show (c₁.work dsT).cells (c₁.work dsT).head ≠ Γ.start
      rw [hdsC₁]
      exact hWns _ (by rw [hdsH₁]; omega)
    by_cases hrest0 : ((takeField R).2[0]?).getD Γw.blank = Γw.blank
    · -- Terminator: the next cell is `□` — one default step; no match.
      have hdc₁ : (c₁.work dsT).read = Γ.blank := by
        rw [hread₁, hrest0]
        rfl
      obtain ⟨c₂, hr₂, hst₂, hvi₂, hvw₂, hvo₂, hoth₂, hii₂, hoo₂⟩ :=
        segCheck_blank_step hst₁ hdc₁ hv0r₁ hv1r₁ hv2r₁ hstr₁ hscr₁
          (by rw [hii₁]; exact hin) (by rw [hoo₁]; exact hout)
      have hfindR : machFind stSyms.length stSyms (keyCells f v0 v1 v2) R
          = none := by
        cases R with
        | nil => simp [machFind]
        | cons s rest =>
          by_cases hs : s = Γw.blank
          · subst hs
            simp [machFind]
          · rw [machFind_cons_of_ne_blank hs, ite_eq_right hMM]
            exact machFind_none_of_head_blank hrest0
      refine ⟨?_, ?_⟩
      · intro seg hfind'
        rw [hfindR] at hfind'
        exact absurd hfind' (by simp)
      · intro _
        refine ⟨c₂, t₁ + 1, le_mul_time (by omega),
          reachesIn_trans _ hr₁ hr₂, hst₂,
          by rw [hvi₂, hvi₁, hv0], by rw [hvw₂, hvw₁, hv1],
          by rw [hvo₂, hvo₁, hv2],
          by rw [hoth₂ stT (by decide) (by decide) (by decide)]; exact hstC₁,
          by rw [hoth₂ stT (by decide) (by decide) (by decide)]; exact hsh1,
          by rw [hoth₂ stT (by decide) (by decide) (by decide)]; exact hsh2,
          by rw [hoth₂ dsT (by decide) (by decide) (by decide)]; exact hdsC₁,
          by rw [hoth₂ dsT (by decide) (by decide) (by decide), hdsH₁]; omega,
          by rw [hoth₂ dsT (by decide) (by decide) (by decide), hdsH₁]; omega,
          by rw [hoth₂ scT (by decide) (by decide) (by decide)]; exact hsc0₁,
          by rw [hoth₂ scT (by decide) (by decide) (by decide)]; exact hscns₁,
          by rw [hoth₂ scT (by decide) (by decide) (by decide)]; exact hsch1,
          by rw [hoth₂ scT (by decide) (by decide) (by decide)]; exact hsch2,
          by rw [hoth₂ scT (by decide) (by decide) (by decide)]
             exact fun j hj _ => hscbl₁ j hj,
          by rw [hii₂, hii₁], by rw [hoo₂, hoo₁]⟩
    · -- The next segment is live: clean up (mmScr, rewindSt) and recurse.
      obtain ⟨s, rest, rfl⟩ : ∃ s rest, R = s :: rest := by
        cases R with
        | nil =>
          exfalso
          exact hrest0 (by simp [takeField])
        | cons s rest => exact ⟨s, rest, rfl⟩
      obtain ⟨s', rest'', hR2⟩ : ∃ s' rest'',
          (takeField (s :: rest)).2 = s' :: rest'' := by
        cases h2 : (takeField (s :: rest)).2 with
        | nil => exact absurd (by rw [h2]; rfl) hrest0
        | cons a b => exact ⟨a, b, rfl⟩
      have hs'_nb : s' ≠ Γw.blank :=
        fun hcon => hrest0 (by rw [hR2, hcon]; rfl)
      have hs : s ≠ Γw.blank := by
        intro hcon
        subst hcon
        rw [show (takeField (Γw.blank :: rest)).2 = rest from rfl] at hR2
        exact hs'_nb (hRhd s' rest'' (by rw [hR2]))
      have hlenR : (s :: rest).length
          = (takeField (s :: rest)).1.length + 1
            + (takeField (s :: rest)).2.length := by
        have h := congrArg List.length (takeField_split_of_snd_ne_nil
          (show (takeField (s :: rest)).2 ≠ [] by
            rw [hR2]; exact fun h => nomatch h))
        simp only [List.length_append, List.length_cons] at h ⊢
        omega
      -- segCheck sees a live cell: continue to mmScr
      obtain ⟨c₂, hr₂, hst₂, hall₂, hii₂, hoo₂⟩ :=
        segCheck_continue_step hst₁
          (by
            rw [hread₁]
            intro hcon
            exact hrest0 (Γw.toΓ_eq_blank.mp hcon))
          (fun i => by
            rcases i with ⟨iv, hv⟩
            rcases iv with _ | _ | _ | _ | _ | _ | n
            · exact hv0r₁
            · exact hv1r₁
            · exact hv2r₁
            · exact hstr₁
            · exact hdsr₁
            · exact hscr₁
            · exact absurd hv (by omega))
          (by rw [hii₁]; exact hin) (by rw [hoo₁]; exact hout)
      -- mmScr: blank-rewind the scratch
      obtain ⟨c₃, hr₃, hst₃, hwtSc₃, hin₃, hout₃, hoth₃⟩ :=
        blankRewStep_loop (cur := mmScr f) (next := rewindSt f) (t := scT)
          (fun hcon => nomatch hcon) (arm_mmScr · · · f)
          (c₁.work scT).head (c₁.work scT).cells hsc0₁ hscns₁
          c₂ hst₂ (by rw [hall₂ scT]) (by rw [hall₂ scT])
          (by rw [hii₂, hii₁]; exact hin) (by rw [hoo₂, hoo₁]; exact hout)
          (fun i hi => by
            have h := hall₂ i
            rw [h]
            rcases i with ⟨iv, hv⟩
            rcases iv with _ | _ | _ | _ | _ | _ | n
            · exact hv0r₁
            · exact hv1r₁
            · exact hv2r₁
            · exact hstr₁
            · exact hdsr₁
            · exact absurd rfl hi
            · exact absurd hv (by omega))
      have hscr₃ : (c₃.work scT).read ≠ Γ.start := by
        show (c₃.work scT).cells (c₃.work scT).head ≠ Γ.start
        rw [hwtSc₃]
        show (if 1 ≤ 1 ∧ 1 ≤ (c₁.work scT).head then Γ.blank
          else (c₁.work scT).cells 1) ≠ Γ.start
        rw [ite_eq_left ⟨Nat.le_refl _, hsch1⟩]
        exact fun h => nomatch h
      -- rewindSt: rewind the state head
      obtain ⟨c₄, hr₄, hst₄, hwtS₄, hin₄, hout₄, hoth₄⟩ :=
        rewStep_loop (cur := rewindSt f) (next := cmpQ f) (t := stT)
          (fun hcon => nomatch hcon) (arm_rewindSt · · · f)
          (c.work stT).cells hSt.1 hS_wns
          (c₁.work stT).head c₃ hst₃
          (by rw [hoth₃ stT (by decide), hall₂ stT]; exact hstC₁)
          (by rw [hoth₃ stT (by decide), hall₂ stT])
          (by rw [hin₃, hii₂, hii₁]; exact hin)
          (by rw [hout₃, hoo₂, hoo₁]; exact hout)
          (fun i hi => by
            by_cases hiSc : i = scT
            · subst hiSc
              exact hscr₃
            · have h3 := hoth₃ i hiSc
              have h2 := hall₂ i
              rw [h3, h2]
              rcases i with ⟨iv, hv⟩
              rcases iv with _ | _ | _ | _ | _ | _ | n
              · exact hv0r₁
              · exact hv1r₁
              · exact hv2r₁
              · exact absurd rfl hi
              · exact hdsr₁
              · exact absurd rfl hiSc
              · exact absurd hv (by omega))
      -- the fresh loop state at the next segment
      have hSc₄ : (c₄.work scT).HoldsExact [] := by
        rw [hoth₄ scT (by decide), hwtSc₃]
        refine Tape.HoldsExact.nil_iff.mpr ⟨?_, ?_⟩
        · show (if 1 ≤ 0 ∧ 0 ≤ (c₁.work scT).head then Γ.blank
            else (c₁.work scT).cells 0) = Γ.start
          rw [ite_eq_right (by omega)]
          exact hsc0₁
        · intro i
          show (if 1 ≤ i + 1 ∧ i + 1 ≤ (c₁.work scT).head then Γ.blank
            else (c₁.work scT).cells (i + 1)) = Γ.blank
          by_cases hcase : 1 ≤ i + 1 ∧ i + 1 ≤ (c₁.work scT).head
          · rw [ite_eq_left hcase]
          · rw [ite_eq_right hcase]
            exact hscbl₁ (i + 1) (by omega)
      have hschead₄ : (c₄.work scT).head = 1 := by
        rw [hoth₄ scT (by decide), hwtSc₃]
      have hdsF₄ : c₄.work dsT = c₁.work dsT := by
        rw [hoth₄ dsT (by decide), hoth₃ dsT (by decide), hall₂ dsT]
      have hviF₄ : c₄.work vIn = c.work vIn := by
        rw [hoth₄ vIn (by decide), hoth₃ vIn (by decide), hall₂ vIn, hvi₁]
      have hvwF₄ : c₄.work vWk = c.work vWk := by
        rw [hoth₄ vWk (by decide), hoth₃ vWk (by decide), hall₂ vWk, hvw₁]
      have hvoF₄ : c₄.work vOut = c.work vOut := by
        rw [hoth₄ vOut (by decide), hoth₃ vOut (by decide), hall₂ vOut, hvo₁]
      have hiF₄ : c₄.input = c.input := by rw [hin₄, hin₃, hii₂, hii₁]
      have hoF₄ : c₄.output = c.output := by rw [hout₄, hout₃, hoo₂, hoo₁]
      -- recurse on the rest of the region
      have hIH := ih (takeField (s :: rest)).2 (by omega)
        (pos + (takeField (s :: rest)).1.length + 1) c₄
        (fun a b hab => by
          rw [hR2] at hab
          injection hab with h1 h2
          exact absurd h1 hs'_nb)
        hst₄
        (fun j => by
          rw [hdsF₄, hdsC₁]
          exact hviewR j)
        (by rw [hdsF₄]; exact hdsH₁) (by omega)
        (fun j hj => by rw [hdsF₄, hdsC₁]; exact hWns j hj)
        (by rw [hwtS₄]; exact ⟨hSt.1, hSt.2⟩)
        (by rw [hwtS₄])
        hSc₄ hschead₄
        (by rw [hviF₄]; exact hv0) (by rw [hvwF₄]; exact hv1)
        (by rw [hvoF₄]; exact hv2)
        (by rw [hviF₄]; exact hv0s) (by rw [hvwF₄]; exact hv1s)
        (by rw [hvoF₄]; exact hv2s)
        (by rw [hiF₄]; exact hin) (by rw [hoF₄]; exact hout)
      have hprefix : bodyTM.reachesIn
          (t₁ + 1 + ((c₁.work scT).head + 1) + ((c₁.work stT).head + 1))
          c c₄ :=
        reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _ hr₁ hr₂) hr₃)
          hr₄
      have hfindR : machFind stSyms.length stSyms (keyCells f v0 v1 v2)
          (s :: rest)
          = machFind stSyms.length stSyms (keyCells f v0 v1 v2)
              (takeField (s :: rest)).2 := by
        rw [machFind_cons_of_ne_blank hs, ite_eq_right hMM]
      have hpre_le : t₁ + 1 + ((c₁.work scT).head + 1)
          + ((c₁.work stT).head + 1)
          ≤ 4 * stSyms.length + (takeField (s :: rest)).1.length + 34 := by
        omega
      refine ⟨?_, ?_⟩
      · intro seg hfind'
        rw [hfindR] at hfind'
        obtain ⟨c', t', ht', hr', hst', hscH', hscHd', hstF', hdsC', hdsH1',
          hdsH2', hviF', hvwF', hvoF', hiF', hoF'⟩ := hIH.1 seg hfind'
        refine ⟨c', _ + t', ?_, reachesIn_trans _ hprefix hr', hst', hscH',
          hscHd', ?_, ?_, hdsH1', ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [show (s :: rest).length + 2
            = (takeField (s :: rest)).1.length + 1
              + (takeField (s :: rest)).2.length + 2 from by omega]
          exact time_bound_step hpre_le ht'
        · rw [hstF', hwtS₄]
          exact tape_mk_eq hsthead
        · rw [hdsC', hdsF₄, hdsC₁]
        · omega
        · rw [hviF', hviF₄]
        · rw [hvwF', hvwF₄]
        · rw [hvoF', hvoF₄]
        · rw [hiF', hiF₄]
        · rw [hoF', hoF₄]
      · intro hfind'
        rw [hfindR] at hfind'
        obtain ⟨c', t', ht', hr', hst', hviW', hvwW', hvoW', hstC', hsh1',
          hsh2', hdsC', hdsH1', hdsH2', hsc0', hscns', hsch1', hsch2',
          hscbl', hiF', hoF'⟩ := hIH.2 hfind'
        refine ⟨c', _ + t', ?_, reachesIn_trans _ hprefix hr', hst',
          ?_, ?_, ?_, ?_, hsh1', hsh2', ?_, hdsH1', ?_, hsc0', hscns',
          hsch1', hsch2', hscbl', ?_, ?_⟩
        · rw [show (s :: rest).length + 2
            = (takeField (s :: rest)).1.length + 1
              + (takeField (s :: rest)).2.length + 2 from by omega]
          exact time_bound_step hpre_le ht'
        · rw [hviW', hviF₄]
        · rw [hvwW', hvwF₄]
        · rw [hvoW', hvoF₄]
        · rw [hstC', hwtS₄]
        · rw [hdsC', hdsF₄, hdsC₁]
        · omega
        · rw [hiF', hiF₄]
        · rw [hoF', hoF₄]

/-- **The match-loop induction** (design appendix 2, machine side): from
    `cmpQ f` at the start of the entry region suffix `R` (desc cells at
    `pos + j` hold `R`'s symbols, blank-padded; an empty head segment of
    `R`, if any, is a real terminator — see the module docstring), with
    the state tape holding `stSyms` at head 1, a clean scratch tape, and
    the three virtual tapes stationary with live reads `v0`/`v1`/`v2`:

    * if `machFind` accepts a segment `seg`, the machine reaches
      `appRewScr f` with `seg`'s value slice (the `w + 10` cells after its
      key) on the scratch tape, the state tape restored, desc cells
      unchanged, and the virtual tapes untouched;
    * if `machFind` rejects (`none`), the machine reaches `dfScr` having
      applied the sanitized default moves (trick 4) to the three virtual
      tapes, with state and desc cells unchanged and the scratch confined
      (`▷`-free, blank at and beyond its head, head ≤ `w + 11`) — the shape
      `defaultTail` consumes;

    in either case within `(|R| + 2)·(4·|stSyms| + 60)` steps. -/
theorem matchLoop (f : VFlags) (v0 v1 v2 : Γ) (stSyms : List Γw)
    (hst_nb : ∀ s ∈ stSyms, s ≠ Γw.blank) :
    ∀ (R : List Γw) (pos : ℕ) (c : Cfg 6 bodyTM.Q),
      (∀ s rest, R = Γw.blank :: s :: rest → s = Γw.blank) →
      c.state = cmpQ f →
      (∀ j, (c.work dsT).cells (pos + j) = ((R[j]?).getD Γw.blank).toΓ) →
      (c.work dsT).head = pos → 1 ≤ pos →
      (∀ j, 1 ≤ j → (c.work dsT).cells j ≠ Γ.start) →
      (c.work stT).HoldsExact stSyms → (c.work stT).head = 1 →
      (c.work scT).HoldsExact [] → (c.work scT).head = 1 →
      (c.work vIn).read = v0 → (c.work vWk).read = v1 →
      (c.work vOut).read = v2 →
      (c.work vIn).read ≠ Γ.start → (c.work vWk).read ≠ Γ.start →
      (c.work vOut).read ≠ Γ.start →
      c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
      ((∀ seg,
          machFind stSyms.length stSyms (keyCells f v0 v1 v2) R = some seg →
          ∃ c' t, t ≤ (R.length + 2) * (4 * stSyms.length + 60) ∧
            bodyTM.reachesIn t c c' ∧
            c'.state = appRewScr f ∧
            (c'.work scT).HoldsExact
              ((seg.drop (stSyms.length + 6)).take (stSyms.length + 10)) ∧
            (c'.work scT).head = stSyms.length + 10 + 1 ∧
            c'.work stT = c.work stT ∧
            (c'.work dsT).cells = (c.work dsT).cells ∧
            1 ≤ (c'.work dsT).head ∧ (c'.work dsT).head ≤ pos + R.length + 1 ∧
            c'.work vIn = c.work vIn ∧ c'.work vWk = c.work vWk ∧
            c'.work vOut = c.work vOut ∧
            c'.input = c.input ∧ c'.output = c.output) ∧
       (machFind stSyms.length stSyms (keyCells f v0 v1 v2) R = none →
          ∃ c' t, t ≤ (R.length + 2) * (4 * stSyms.length + 60) ∧
            bodyTM.reachesIn t c c' ∧
            c'.state = dfScr ∧
            c'.work vIn = (c.work vIn).writeAndMove (readBackWrite v0).toΓ
              (if f.1 then Dir3.right else Dir3.stay) ∧
            c'.work vWk = (c.work vWk).writeAndMove (readBackWrite v1).toΓ
              (if f.2.1 then Dir3.right else Dir3.stay) ∧
            c'.work vOut = (c.work vOut).writeAndMove (readBackWrite v2).toΓ
              (if f.2.2 then Dir3.right else Dir3.stay) ∧
            (c'.work stT).cells = (c.work stT).cells ∧
            1 ≤ (c'.work stT).head ∧ (c'.work stT).head ≤ stSyms.length + 1 ∧
            (c'.work dsT).cells = (c.work dsT).cells ∧
            1 ≤ (c'.work dsT).head ∧ (c'.work dsT).head ≤ pos + R.length + 1 ∧
            (c'.work scT).cells 0 = Γ.start ∧
            (∀ j, 1 ≤ j → (c'.work scT).cells j ≠ Γ.start) ∧
            1 ≤ (c'.work scT).head ∧ (c'.work scT).head ≤ stSyms.length + 11 ∧
            (∀ j, (c'.work scT).head ≤ j → 1 ≤ j →
              (c'.work scT).cells j = Γ.blank) ∧
            c'.input = c.input ∧ c'.output = c.output)) := by
  have main : ∀ (N : ℕ) (R : List Γw), R.length ≤ N →
      MatchLoopStmt f v0 v1 v2 stSyms R := by
    intro N
    induction N with
    | zero =>
      intro R hR
      exact matchLoop_go f v0 v1 v2 stSyms hst_nb R
        (fun R' hR' => absurd hR' (by omega))
    | succ N ihN =>
      intro R hR
      exact matchLoop_go f v0 v1 v2 stSyms hst_nb R
        (fun R' hR' => ihN R' (by omega))
  exact fun R => main R.length R (Nat.le_refl _)

end TM.UTMBody

end Complexity
