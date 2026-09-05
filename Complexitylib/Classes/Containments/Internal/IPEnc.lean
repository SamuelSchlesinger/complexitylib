/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.IPSem

/-!
# The walk's state on a bitstring

⚠️ Unreviewed by Bolton

`Complexitylib.Classes.Containments.Internal.IPSem` walks the game tree on an inductive state.
A machine has to hold that state on a tape, so this file writes it as a bitstring — a frame is
five blocks, the stack a right-nested chain of pairs — and records the invariant the encoding
needs: a returning value is a *count*, so it is never empty, which is what tells `some` from
`none`.

## Main definitions

- `Complexity.IPM.encFrm`, `Complexity.IPM.encStk`, `Complexity.IPM.encSst` — the encoding
- `Complexity.IPM.EncOk` — the invariant the encoding relies on

## Main results

- `Complexity.IPM.step_encOk` — the invariant is preserved
-/

@[expose] public section

namespace Complexity

namespace IPM

open Cobham

/-! ## The encoding -/

/-- A frame on the tape: five blocks. -/
def encFrm (f : Frm) : List Bool :=
  pair f.lvl (pair f.v (pair f.a (pair f.sum (pair f.best f.body))))

/-- The stack on the tape: a right-nested chain of pairs, empty stack being the empty string. -/
def encStk : List Frm → List Bool
  | [] => []
  | f :: fs => pair (encFrm f) (encStk fs)

@[simp] theorem encStk_nil : encStk [] = [] := rfl

@[simp] theorem encStk_cons (f : Frm) (fs : List Frm) :
    encStk (f :: fs) = pair (encFrm f) (encStk fs) := rfl

/-- A returning value on the tape. A count is never empty, so the empty string means *nothing is
returning*. -/
def encRet : Option (List Bool) → List Bool
  | none => []
  | some w => w

@[simp] theorem encRet_none : encRet none = [] := rfl

@[simp] theorem encRet_some (w : List Bool) : encRet (some w) = w := rfl

/-- The state on the tape. -/
def encSst (s : Sst) : List Bool :=
  pair [s.done] (pair [s.ansBit] (pair (encRet s.ret) (encStk s.stk)))

theorem encSst_ne_nil (s : Sst) : encSst s ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [encSst, pair_length] at this
  simp at this

theorem encSst_headD (s : Sst) : (encSst s).headD false = s.done := by
  rw [encSst, pair_cons_eq]
  rfl

theorem headD_pair_encSst (s : Sst) (x : List Bool) :
    (pair (encSst s) x).headD false = s.done := by
  rw [encSst, pair_cons_eq, pair_cons_eq]
  rfl

/-! ## The invariant the encoding relies on -/
/-- Every frame carries the body of the rounds below it. -/
def BodyOk : List Frm → Prop
  | [] => True
  | f :: fs => f.body = encBodyR (roundsOf fs) ∧ BodyOk fs

@[simp] theorem bodyOk_nil : BodyOk [] := trivial

theorem bodyOk_cons {f : Frm} {fs : List Frm} (h : f.body = encBodyR (roundsOf fs))
    (h' : BodyOk fs) : BodyOk (f :: fs) := ⟨h, h'⟩

/-- The stack descends exactly one level per frame, so its depth is the level it started at. -/
def StkDepth (D : ℕ) : List Frm → Prop
  | [] => True
  | f :: fs => fs.length + f.lvl.length + 1 = D ∧ StkDepth D fs

theorem StkDepth.length_le {D : ℕ} : ∀ {stk : List Frm}, StkDepth D stk → stk.length ≤ D
  | [], _ => by simp
  | f :: fs, h => by
      rw [List.length_cons]
      have := h.1
      omega


/-- The encoding is faithful when nothing is returning while the stack is empty, and every count
on the state has the width a count is held in — so that a returning value is never empty. -/
structure EncOk (P : Params) (D : ℕ) (s : Sst) : Prop where
  /-- Nothing returns to an empty stack. -/
  stkOk : s.stk = [] → s.ret ≠ none
  /-- A returning value is a count. -/
  retLen : ∀ w, s.ret = some w → w.length = P.t + 1
  /-- So are the accumulators on the stack. -/
  frmLen : ∀ f ∈ s.stk, f.sum.length = P.t + 1 ∧ f.best.length = P.t + 1
  /-- Every frame carries the body of the rounds below it. -/
  bodyOk : BodyOk s.stk
  /-- The stack is no deeper than the level it started at. -/
  depthOk : StkDepth D s.stk

theorem encRet_ne_nil {P : Params} {D : ℕ} {s : Sst} (h : EncOk P D s) {w : List Bool}
    (hw : s.ret = some w) : w ≠ [] := by
  intro hc
  have := h.retLen w hw
  rw [hc] at this
  simp at this

theorem zeroCount_length (P : Params) : (zeroCount P).length = P.t + 1 := by
  rw [zeroCount, List.length_replicate]

theorem freshFrm_len (P : Params) (body lvl : List Bool) :
    (freshFrm P body lvl).sum.length = P.t + 1 ∧ (freshFrm P body lvl).best.length = P.t + 1 :=
  ⟨zeroCount_length P, zeroCount_length P⟩


/-- **The invariant is preserved.** -/
theorem step_encOk (P : Params) (D : ℕ) {s : Sst} (h : EncOk P D s) :
    EncOk P D (step P s) := by
  obtain ⟨d, a, r, stk⟩ := s
  cases d
  · cases stk with
    | nil =>
        obtain ⟨b, rfl⟩ : ∃ b, r = some b := by
          cases r with
          | none => exact absurd rfl (h.stkOk rfl)
          | some b => exact ⟨b, rfl⟩
        rw [step_of_empty]
        exact { stkOk := fun _ => by simp
                retLen := fun w hw => h.retLen w hw
                frmLen := fun f hf => by simp at hf
                bodyOk := trivial
                depthOk := trivial }
    | cons f fs =>
      have hfl := h.frmLen f (List.mem_cons_self)
      have hrest : ∀ g ∈ fs, g.sum.length = P.t + 1 ∧ g.best.length = P.t + 1 :=
        fun g hg => h.frmLen g (List.mem_cons_of_mem _ hg)
      cases r with
      | none =>
          by_cases hl : f.lvl = []
          · by_cases hov : bumpOver f.a = true
            · rw [step_leaf_last P a f fs hl hov]
              refine { stkOk := fun _ => by simp
                       retLen := fun w hw => ?_
                       frmLen := fun g hg => hrest g hg
                       bodyOk := h.bodyOk.2
                       depthOk := h.depthOk.2 }
              simp only [Option.some.injEq] at hw
              rw [← hw]
              by_cases hokb : P.ok (roundsOf fs) f.a
              · rw [ite_eq_left hokb, bumpBits_length]
                exact hfl.1
              · rw [ite_eq_right hokb]
                exact hfl.1
            · rw [step_leaf_next P a f fs hl (by simpa using hov)]
              refine { stkOk := fun hc => by simp at hc
                       retLen := fun w hw => by simp at hw
                       frmLen := fun g hg => ?_
                       bodyOk := ⟨h.bodyOk.1, h.bodyOk.2⟩
                       depthOk := ⟨h.depthOk.1, h.depthOk.2⟩ }
              rcases List.mem_cons.mp hg with rfl | hg
              · refine ⟨?_, hfl.2⟩
                show (if P.ok (roundsOf fs) f.a then bumpBits f.sum else f.sum).length = P.t + 1
                by_cases hokb : P.ok (roundsOf fs) f.a
                · rw [ite_eq_left hokb, bumpBits_length]
                  exact hfl.1
                · rw [ite_eq_right hokb]
                  exact hfl.1
              · exact hrest g hg
          · rw [step_push P a f fs hl]
            refine { stkOk := fun hc => by simp at hc
                     retLen := fun w hw => by simp at hw
                     frmLen := fun g hg => ?_
                     bodyOk := ⟨?_, h.bodyOk⟩
                     depthOk := ⟨?_, h.depthOk⟩ }
            · rcases List.mem_cons.mp hg with rfl | hg
              · exact freshFrm_len P _ _
              · exact h.frmLen g hg
            · show f.body ++ encMsg f.v ++ encMsg f.a = encBodyR (roundsOf (f :: fs))
              rw [roundsOf_cons, encBodyR_append, h.bodyOk.1]
            · have hpos : 1 ≤ f.lvl.length := by
                cases hlv : f.lvl with
                | nil => exact absurd hlv hl
                | cons _ t => simp
              have hd := h.depthOk.1
              show (f :: fs).length + (f.lvl.drop 1).length + 1 = D
              rw [List.length_cons, List.length_drop]
              omega
      | some r =>
          have hrlen : r.length = P.t + 1 := h.retLen r rfl
          have hmaxlen : (maxBits f.best r).length = P.t + 1 := by
            rw [maxBits_length _ _ (by rw [hrlen, hfl.2]), hfl.2]
          have haddlen : (addBits f.sum (maxBits f.best r)).length = P.t + 1 := by
            rw [addBits_length _ _ (by rw [hmaxlen, hfl.1]), hfl.1]
          by_cases ha : (nextStr f.a).length ≤ P.m
          · rw [step_ret_more_a P a f fs r ha]
            refine { stkOk := fun hc => by simp at hc
                     retLen := fun w hw => by simp at hw
                     frmLen := fun g hg => ?_
                     bodyOk := ⟨h.bodyOk.1, h.bodyOk.2⟩
                     depthOk := ⟨h.depthOk.1, h.depthOk.2⟩ }
            rcases List.mem_cons.mp hg with rfl | hg
            · exact ⟨hfl.1, hmaxlen⟩
            · exact hrest g hg
          · by_cases hv : (nextStr f.v).length ≤ P.m
            · rw [step_ret_more_v P a f fs r ha hv]
              refine { stkOk := fun hc => by simp at hc
                       retLen := fun w hw => by simp at hw
                       frmLen := fun g hg => ?_
                       bodyOk := ⟨h.bodyOk.1, h.bodyOk.2⟩
                       depthOk := ⟨h.depthOk.1, h.depthOk.2⟩ }
              rcases List.mem_cons.mp hg with rfl | hg
              · exact ⟨haddlen, zeroCount_length P⟩
              · exact hrest g hg
            · rw [step_ret_pop P a f fs r ha hv]
              exact { stkOk := fun _ => by simp
                      retLen := fun w hw => by
                        simp only [Option.some.injEq] at hw
                        rw [← hw]
                        exact haddlen
                      frmLen := fun g hg => hrest g hg
                      bodyOk := h.bodyOk.2
                      depthOk := h.depthOk.2 }
  · rw [step_of_done]
    exact { stkOk := h.stkOk
            retLen := h.retLen
            frmLen := h.frmLen
            bodyOk := h.bodyOk
            depthOk := h.depthOk }

theorem iterate_encOk (P : Params) (D : ℕ) :
    ∀ (j : ℕ) (s : Sst), EncOk P D s → EncOk P D ((step P)^[j] s) := by
  intro j
  induction j with
  | zero => intro s h; exact h
  | succ j ih =>
      intro s h
      rw [Function.iterate_succ_apply]
      exact ih _ (step_encOk P D h)

theorem encOk_start (P : Params) (lvl : List Bool) :
    EncOk P (lvl.length + 1) ⟨false, false, none, [freshFrm P [] lvl]⟩ :=
  { stkOk := fun hc => by simp at hc
    retLen := fun w hw => by simp at hw
    frmLen := fun f hf => by
      rcases List.mem_cons.mp hf with rfl | hf
      · exact freshFrm_len P [] lvl
      · simp at hf
    bodyOk := ⟨rfl, trivial⟩
    depthOk := ⟨by
      show [].length + (freshFrm P [] lvl).lvl.length + 1 = lvl.length + 1
      simp [freshFrm], trivial⟩ }

/-! ## How long an encoded state is -/

/-- The width a message counter can reach. -/
def msgW (P : Params) : ℕ := max P.m P.t

/-- Every frame's counters are within the widths the walk uses. -/
def SizeOk (P : Params) : List Frm → Prop
  | [] => True
  | f :: fs => f.v.length ≤ P.m ∧ f.a.length ≤ msgW P ∧ SizeOk P fs

theorem step_sizeOk (P : Params) {s : Sst} (h : SizeOk P s.stk) : SizeOk P (step P s).stk := by
  obtain ⟨d, a, r, stk⟩ := s
  cases d
  · cases stk with
    | nil =>
        cases r with
        | none => exact trivial
        | some b => exact trivial
    | cons f fs =>
      obtain ⟨hv, ha, hrest⟩ := h
      cases r with
      | none =>
          by_cases hl : f.lvl = []
          · by_cases hov : bumpOver f.a = true
            · rw [step_leaf_last P a f fs hl hov]
              exact hrest
            · rw [step_leaf_next P a f fs hl (by simpa using hov)]
              refine ⟨hv, ?_, hrest⟩
              show (bumpBits f.a).length ≤ msgW P
              rw [bumpBits_length]
              exact ha
          · rw [step_push P a f fs hl]
            refine ⟨?_, ?_, hv, ha, hrest⟩
            · show ([] : List Bool).length ≤ P.m
              simp
            · show (if f.lvl.drop 1 = [] then zeroCoin P else []).length ≤ msgW P
              split
              · rw [zeroCoin, List.length_replicate]
                exact le_max_right _ _
              · simp
      | some r =>
          by_cases hA : (nextStr f.a).length ≤ P.m
          · rw [step_ret_more_a P a f fs r hA]
            exact ⟨hv, le_trans hA (le_max_left _ _), hrest⟩
          · by_cases hV : (nextStr f.v).length ≤ P.m
            · rw [step_ret_more_v P a f fs r hA hV]
              refine ⟨hV, ?_, hrest⟩
              show ([] : List Bool).length ≤ msgW P
              simp
            · rw [step_ret_pop P a f fs r hA hV]
              exact hrest
  · rw [step_of_done]
    exact h

theorem iterate_sizeOk (P : Params) :
    ∀ (j : ℕ) (s : Sst), SizeOk P s.stk → SizeOk P ((step P)^[j] s).stk := by
  intro j
  induction j with
  | zero => intro s h; exact h
  | succ j ih =>
      intro s h
      rw [Function.iterate_succ_apply]
      exact ih _ (step_sizeOk P h)

theorem sizeOk_start (P : Params) (lvl : List Bool) :
    SizeOk P [freshFrm P [] lvl] := by
  refine ⟨?_, ?_, trivial⟩
  · show ([] : List Bool).length ≤ P.m
    simp
  · show (if lvl = [] then zeroCoin P else []).length ≤ msgW P
    split
    · rw [zeroCoin, List.length_replicate]
      exact le_max_right _ _
    · simp

/-- **The transcript body a stack records is polynomially long.** -/
theorem body_length_le (P : Params) :
    ∀ fs : List Frm, SizeOk P fs →
      (encBodyR (roundsOf fs)).length ≤ fs.length * (8 * msgW P + 4) := by
  intro fs
  induction fs with
  | nil => intro _; simp
  | cons f fs ih =>
      intro h
      obtain ⟨hv, ha, hrest⟩ := h
      have hv' : f.v.length ≤ msgW P := le_trans hv (le_max_left _ _)
      have h1 := encMsg_length_le f.v
      have h2 := encMsg_length_le f.a
      have := ih hrest
      have hexp : (fs.length + 1) * (8 * msgW P + 4)
          = fs.length * (8 * msgW P + 4) + (8 * msgW P + 4) := by ring
      rw [roundsOf_cons, encBodyR_append, List.length_append, List.length_append,
        List.length_cons]
      omega

theorem encFrm_length_le (P : Params) (D B : ℕ) (f : Frm) (hl : f.lvl.length + 1 ≤ D)
    (hv : f.v.length ≤ P.m) (ha : f.a.length ≤ msgW P) (hs : f.sum.length = P.t + 1)
    (hb : f.best.length = P.t + 1) (hbody : f.body.length ≤ B) :
    (encFrm f).length ≤ 2 * D + 2 * P.m + 2 * msgW P + 4 * (P.t + 1) + B + 10 := by
  rw [encFrm, pair_length, pair_length, pair_length, pair_length, pair_length, hs, hb]
  omega

theorem encStk_length_le : ∀ (fs : List Frm) (B : ℕ),
    (∀ g ∈ fs, (encFrm g).length ≤ B) → (encStk fs).length ≤ fs.length * (2 * B + 2)
  | [], _, _ => by simp
  | f :: fs, B, h => by
      have hf : (encFrm f).length ≤ B := h f List.mem_cons_self
      have hrest := encStk_length_le fs B fun g hg => h g (List.mem_cons_of_mem _ hg)
      rw [encStk_cons, pair_length, List.length_cons,
        show (fs.length + 1) * (2 * B + 2) = fs.length * (2 * B + 2) + (2 * B + 2) from by ring]
      omega

theorem StkDepth.mem_le {D : ℕ} : ∀ {stk : List Frm}, StkDepth D stk →
    ∀ f ∈ stk, f.lvl.length + 1 ≤ D
  | [], _ => by simp
  | g :: gs, h => by
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · have := h.1
        omega
      · exact StkDepth.mem_le h.2 f hf

theorem SizeOk.mem {P : Params} : ∀ {stk : List Frm}, SizeOk P stk →
    ∀ f ∈ stk, f.v.length ≤ P.m ∧ f.a.length ≤ msgW P
  | [], _ => by simp
  | g :: gs, h => by
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨h.1, h.2.1⟩
      · exact SizeOk.mem h.2.2 f hf

theorem SizeOk.tail {P : Params} {g : Frm} {gs : List Frm} (h : SizeOk P (g :: gs)) :
    SizeOk P gs := h.2.2

theorem body_bound_mem (P : Params) (D : ℕ) : ∀ stk : List Frm, BodyOk stk → SizeOk P stk →
    StkDepth D stk → ∀ g ∈ stk, g.body.length ≤ D * (8 * msgW P + 4)
  | [], _, _, _ => by simp
  | f :: fs, hb, hs, hd => by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · rw [hb.1]
        refine le_trans (body_length_le P fs hs.tail) ?_
        have := hd.1
        exact Nat.mul_le_mul_right _ (by omega)
      · exact body_bound_mem P D fs hb.2 hs.tail hd.2 g hg

/-- The width the encoded state stays inside. -/
def stateBound (P : Params) (D : ℕ) : ℕ :=
  2 * (P.t + 1)
    + D * (2 * (2 * D + 2 * P.m + 2 * msgW P + 4 * (P.t + 1)
        + D * (8 * msgW P + 4) + 10) + 2) + 10

theorem stateBound_le (P : Params) (D M : ℕ) (hM : msgW P ≤ M) :
    stateBound P D
      ≤ 2 * (P.t + 1) + D * (2 * (2 * D + 2 * P.m + 2 * M + 4 * (P.t + 1)
          + D * (8 * M + 4) + 10) + 2) + 10 := by
  rw [stateBound]
  gcongr

/-- **An encoded state is polynomially long.** -/
theorem encSst_length_le (P : Params) (D : ℕ) (s : Sst) (h : EncOk P D s)
    (hsz : SizeOk P s.stk) : (encSst s).length ≤ stateBound P D := by
  have hret : (encRet s.ret).length ≤ P.t + 1 := by
    cases hr : s.ret with
    | none => simp
    | some w =>
        rw [encRet_some]
        exact le_of_eq (h.retLen w hr)
  have hframe : ∀ g ∈ s.stk, (encFrm g).length
      ≤ 2 * D + 2 * P.m + 2 * msgW P + 4 * (P.t + 1) + D * (8 * msgW P + 4) + 10 := by
    intro g hg
    obtain ⟨hv, ha⟩ := SizeOk.mem hsz g hg
    obtain ⟨hs, hb⟩ := h.frmLen g hg
    exact encFrm_length_le P D _ g (StkDepth.mem_le h.depthOk g hg) hv ha hs hb
      (body_bound_mem P D s.stk h.bodyOk hsz h.depthOk g hg)
  have hstk := encStk_length_le s.stk _ hframe
  have hdepth : s.stk.length ≤ D := StkDepth.length_le h.depthOk
  have hmul := Nat.mul_le_mul_right
    (2 * (2 * D + 2 * P.m + 2 * msgW P + 4 * (P.t + 1) + D * (8 * msgW P + 4) + 10) + 2) hdepth
  have hnil : ([] : List Bool).length = 0 := rfl
  rw [encSst, pair_length, pair_length, pair_length, stateBound]
  simp only [List.length_cons]
  omega

end IPM

end Complexity
