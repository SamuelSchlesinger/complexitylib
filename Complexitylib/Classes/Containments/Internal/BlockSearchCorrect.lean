/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.CodeStep

/-!
# What the worklist search finds

⚠️ Unreviewed by Bolton

The invariant of the search: the visited string is a list of distinct records,
each the code of a configuration reachable from the initial one; the initial
code is among them; and every record the counter has passed has both of its
successors recorded.

Once the counter has passed every record — which it has after as many steps as
there are configurations, since the records are distinct — the recorded codes
are closed under the graph's steps, so every reachable configuration's code is
there.

## Main definitions

- `Complexity.recordWidth` — the width of one record
- `Complexity.SearchOk` — the invariant

## Main results

- `Complexity.memFlag_records` — the scan decides membership in the record list
- `Complexity.searchStepPair_ok` — one step preserves the invariant
- `Complexity.SearchOk.mem_of_reachesCfg` — a saturated search has found
  everything
-/

@[expose] public section

namespace Complexity

open Cobham

variable {k : ℕ}

/-! ## Records -/

/-- The width of one record: a whole code. -/
def recordWidth (k W : ℕ) : ℕ := codeBlocks k * (blockRuler W).length

theorem recordWidth_pos (k W : ℕ) : 0 < recordWidth k W := by
  rw [recordWidth, blockRuler_length, blockWidth, codeBlocks]
  positivity

theorem wideRuler_blockRuler_length (k W : ℕ) :
    (wideRuler (codeBlocks k) (blockRuler W)).length = recordWidth k W := by
  rw [wideRuler_length, recordWidth]

/-- The records of a concatenation are its blocks. -/
theorem blockAt_records (k W : ℕ) (bs : List (List Bool))
    (hbs : ∀ b ∈ bs, b.length = recordWidth k W) (i : ℕ) (hi : i < bs.length) :
    blockAt (wideRuler (codeBlocks k) (blockRuler W)) bs.flatten i = bs[i] :=
  blockAt_flatten _ _ (fun b hb => by
    rw [hbs b hb, wideRuler_blockRuler_length]) i hi

theorem length_flatten_records (k W : ℕ) (bs : List (List Bool))
    (hbs : ∀ b ∈ bs, b.length = recordWidth k W) :
    bs.flatten.length = bs.length * recordWidth k W := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      rw [List.flatten_cons, List.length_append, hbs b List.mem_cons_self,
        ih (fun c hc => hbs c (List.mem_cons_of_mem _ hc)), List.length_cons, Nat.succ_mul]
      omega

/-- **The scan decides membership in the record list.** -/
theorem memFlag_records (k W : ℕ) (bs : List (List Bool))
    (hbs : ∀ b ∈ bs, b.length = recordWidth k W) (u : List Bool) :
    memFlag (wideRuler (codeBlocks k) (blockRuler W)) u bs.flatten = [true] ↔ u ∈ bs := by
  have hw : 0 < (wideRuler (codeBlocks k) (blockRuler W)).length := by
    rw [wideRuler_blockRuler_length]
    exact recordWidth_pos k W
  rw [memFlag_eq_true_iff _ _ _ hw, wideRuler_blockRuler_length,
    length_flatten_records k W bs hbs]
  constructor
  · rintro ⟨i, hlen, hblk⟩
    have hi : i < bs.length := by
      by_contra hcon
      have : bs.length * recordWidth k W ≤ i * recordWidth k W :=
        Nat.mul_le_mul_right _ (by omega)
      have := recordWidth_pos k W
      omega
    rw [blockAt_records k W bs hbs i hi] at hblk
    exact hblk ▸ List.getElem_mem hi
  · intro hu
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hu
    refine ⟨i, ?_, ?_⟩
    · have : (i + 1) * recordWidth k W ≤ bs.length * recordWidth k W :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at this
      omega
    · rw [blockAt_records k W bs hbs i hi]
      exact hbi

/-! ## Appending a record -/

/-- The appended record was not there before. -/
theorem addBlock_nodup (k W : ℕ) (bs : List (List Bool))
    (hbs : ∀ b ∈ bs, b.length = recordWidth k W) (b : List Bool) (hnd : bs.Nodup)
    (hm : memFlag (wideRuler (codeBlocks k) (blockRuler W)) b bs.flatten = [false]) :
    (bs ++ [b]).Nodup := by
  have hnb : b ∉ bs := by
    intro hmem
    have := (memFlag_records k W bs hbs b).mpr hmem
    rw [hm] at this
    simp at this
  rw [List.nodup_append]
  exact ⟨hnd, List.nodup_singleton b, by
    intro a ha c hc
    rw [List.mem_singleton] at hc
    rintro rfl
    exact hnb (hc ▸ ha)⟩

/-! ## The invariant -/

/-- The records of a list of configurations. -/
noncomputable def codesOf {Q : Type} [Fintype Q] [DecidableEq Q] (W : ℕ)
    (cs : List (Cfg k Q)) : List (List Bool) :=
  cs.map (Cobham.cfgCode W)

theorem codesOf_recordWidth {Q : Type} [Fintype Q] [DecidableEq Q] (W : ℕ)
    (cs : List (Cfg k Q)) : ∀ b ∈ codesOf W cs, b.length = recordWidth k W := by
  intro b hb
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb
  rw [cfgCode_length, recordWidth]

@[simp] theorem codesOf_length {Q : Type} [Fintype Q] [DecidableEq Q] (W : ℕ)
    (cs : List (Cfg k Q)) : (codesOf W cs).length = cs.length := by
  rw [codesOf, List.length_map]

theorem codesOf_getElem {Q : Type} [Fintype Q] [DecidableEq Q] (W : ℕ)
    (cs : List (Cfg k Q)) (i : ℕ) (hi : i < cs.length) :
    (codesOf W cs)[i]'(by rwa [codesOf_length]) = Cobham.cfgCode W cs[i] :=
  List.getElem_map _

@[simp] theorem codesOf_append {Q : Type} [Fintype Q] [DecidableEq Q] (W : ℕ)
    (cs : List (Cfg k Q)) (c : Cfg k Q) :
    codesOf W (cs ++ [c]) = codesOf W cs ++ [Cobham.cfgCode W c] := by
  rw [codesOf, codesOf, List.map_append, List.map_singleton]

/-- The search state is sound: the visited string is the concatenation of the codes
of finitely many reachable configurations, no two of them coded alike; the initial
code is there; and every record the counter has passed has both successors
recorded. -/
def SearchOk (tm : NTM k) (x : List Bool) (W : ℕ) (r V : List Bool) : Prop :=
  ∃ cs : List (Cfg k tm.Q),
    V = (codesOf W cs).flatten ∧ (codesOf W cs).Nodup ∧
      (∀ c ∈ cs, tm.ReachesCfg (tm.initCfg x) c) ∧
      Cobham.cfgCode W (tm.initCfg x) ∈ codesOf W cs ∧
      ∀ i, i < r.length → ∀ hi : i < cs.length, ∀ β : Bool,
        nstepFn tm β (blockRuler W) (Cobham.cfgCode W cs[i]) ∈ codesOf W cs

/-- The initial state is sound. -/
theorem searchOk_init (tm : NTM k) (x : List Bool) (W : ℕ) :
    SearchOk tm x W [] (Cobham.cfgCode W (tm.initCfg x)) := by
  refine ⟨[tm.initCfg x], by simp [codesOf], by simp [codesOf], ?_, by simp [codesOf], ?_⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    rw [hc]
    exact NTM.reachesCfg_refl tm _
  · intro i hi
    simp at hi

/-! ## One step preserves the invariant -/

/-- The two encoded successors of a reachable configuration are codes of
reachable configurations. -/
theorem exists_succ_code (tm : NTM k) {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (x : List Bool) (W : ℕ)
    (hq : Fintype.card tm.Q ≤ blockWidth W) (hW : x.length + S x.length + 1 ≤ W)
    {c : Cfg k tm.Q} (hc : tm.ReachesCfg (tm.initCfg x) c) (β : Bool) :
    ∃ c', tm.ReachesCfg (tm.initCfg x) c' ∧
      nstepFn tm β (blockRuler W) (Cobham.cfgCode W c) = Cobham.cfgCode W c' := by
  have hinv := codeInv_of_reachesCfg tm hdec x hc W hW
  by_cases hh : c.state = tm.qhalt
  · exact ⟨c, hc, nstepFn_code_halted tm β W c hq hinv hh⟩
  · exact ⟨tm.stepCfg β c, hc.tail ⟨hh, β, rfl⟩, nstepFn_code tm β W c hq hinv hh⟩

/-- Adding one successor keeps every part of the invariant. -/
theorem searchOk_add (tm : NTM k) (x : List Bool) (W : ℕ) (cs : List (Cfg k tm.Q))
    (hnd : (codesOf W cs).Nodup) (hreach : ∀ d ∈ cs, tm.ReachesCfg (tm.initCfg x) d)
    {c : Cfg k tm.Q} (hc : tm.ReachesCfg (tm.initCfg x) c) :
    ∃ cs' : List (Cfg k tm.Q),
      addBlock (wideRuler (codeBlocks k) (blockRuler W)) (Cobham.cfgCode W c)
          (codesOf W cs).flatten = (codesOf W cs').flatten ∧
        (codesOf W cs').Nodup ∧ (∀ d ∈ cs', tm.ReachesCfg (tm.initCfg x) d) ∧
        (cs' = cs ∨ cs' = cs ++ [c]) ∧ Cobham.cfgCode W c ∈ codesOf W cs' := by
  rcases memFlag_flag (wideRuler (codeBlocks k) (blockRuler W)) (Cobham.cfgCode W c)
    (codesOf W cs).flatten with hm | hm
  · exact ⟨cs, by rw [addBlock_eq_self _ _ _ hm], hnd, hreach, Or.inl rfl,
      (memFlag_records k W _ (codesOf_recordWidth W cs) _).mp hm⟩
  · refine ⟨cs ++ [c], ?_, ?_, ?_, Or.inr rfl, by simp⟩
    · rw [addBlock_eq_append _ _ _ hm, codesOf_append, List.flatten_append]
      simp
    · rw [codesOf_append]
      exact addBlock_nodup k W _ (codesOf_recordWidth W cs) _ hnd hm
    · intro d hd
      rw [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl
      · exact hreach d hd
      · exact hc

/-- A list only grows at the end. -/
theorem append_cases_prefix {α : Type} {cs cs' : List α} {c : α}
    (h : cs' = cs ∨ cs' = cs ++ [c]) :
    (∀ y ∈ cs, y ∈ cs') ∧ cs.length ≤ cs'.length ∧
      ∀ i, ∀ hi : i < cs.length, ∀ hi' : i < cs'.length, cs'[i] = cs[i] := by
  rcases h with rfl | rfl
  · exact ⟨fun _ hy => hy, le_rfl, fun _ _ _ => rfl⟩
  · exact ⟨fun y hy => List.mem_append_left _ hy, by simp,
      fun i hi _ => List.getElem_append_left hi⟩

/-- **One step of the search preserves the invariant.** -/
theorem searchStepPair_ok (tm : NTM k) {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (x : List Bool) (W : ℕ)
    (hq : Fintype.card tm.Q ≤ blockWidth W) (hW : x.length + S x.length + 1 ≤ W)
    (r V : List Bool) (h : SearchOk tm x W r V) :
    SearchOk tm x W (searchStepPair tm (codeBlocks k) (blockRuler W) (r, V)).1
      (searchStepPair tm (codeBlocks k) (blockRuler W) (r, V)).2 := by
  obtain ⟨cs, rfl, hnd, hreach, hinit, hclos⟩ := h
  have hbs := codesOf_recordWidth W cs
  have hlen : (codesOf W cs).flatten.length = cs.length * recordWidth k W := by
    rw [length_flatten_records k W _ hbs, codesOf_length]
  have hpos := recordWidth_pos k W
  have hguard : (guardRuler (codeBlocks k) (blockRuler W) r).length
      = (r.length + 1) * recordWidth k W := by
    rw [guardRuler_length, recordWidth]
  rw [searchStepPair]
  by_cases hg : (guardRuler (codeBlocks k) (blockRuler W) r).length
      ≤ (codesOf W cs).flatten.length
  · rw [ite_eq_left hg]
    have hj : r.length < cs.length := by
      rw [hguard, hlen] at hg
      by_contra hcon
      have : cs.length * recordWidth k W ≤ r.length * recordWidth k W :=
        Nat.mul_le_mul_right _ (by omega)
      have hexp : (r.length + 1) * recordWidth k W
          = r.length * recordWidth k W + recordWidth k W := by ring
      omega
    have hj' : r.length < (codesOf W cs).length := by rwa [codesOf_length]
    have hcur : curBlock (codeBlocks k) (blockRuler W) r (codesOf W cs).flatten
        = Cobham.cfgCode W cs[r.length] := by
      rw [curBlock, blockAt_records k W _ hbs r.length hj', codesOf_getElem]
    have hc : tm.ReachesCfg (tm.initCfg x) cs[r.length] :=
      hreach _ (List.getElem_mem hj)
    obtain ⟨c₀, hc₀, hstep₀⟩ := exists_succ_code tm hdec x W hq hW hc false
    obtain ⟨c₁, hc₁, hstep₁⟩ := exists_succ_code tm hdec x W hq hW hc true
    have hfit : ∀ (β : Bool) (d : Cfg k tm.Q),
        nstepFn tm β (blockRuler W) (Cobham.cfgCode W cs[r.length]) = Cobham.cfgCode W d →
        fitCode (codeBlocks k) (blockRuler W)
          (nstepFn tm β (blockRuler W)
            (curBlock (codeBlocks k) (blockRuler W) r (codesOf W cs).flatten))
          = Cobham.cfgCode W d := by
      intro β d hd
      rw [hcur, hd, fitCode_cfgCode]
    obtain ⟨cs₁, hadd₁, hnd₁, hreach₁, hcases₁, hmem₁⟩ :=
      searchOk_add tm x W cs hnd hreach hc₀
    obtain ⟨cs₂, hadd₂, hnd₂, hreach₂, hcases₂, hmem₂⟩ :=
      searchOk_add tm x W cs₁ hnd₁ hreach₁ hc₁
    obtain ⟨hsub₁, hle₁, hget₁⟩ := append_cases_prefix hcases₁
    obtain ⟨hsub₂, hle₂, hget₂⟩ := append_cases_prefix hcases₂
    have hcsub : ∀ b ∈ codesOf W cs, b ∈ codesOf W cs₂ := by
      intro b hb
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
      exact List.mem_map_of_mem (hsub₂ _ (hsub₁ _ hd))
    have hcsub₁ : ∀ b ∈ codesOf W cs₁, b ∈ codesOf W cs₂ := by
      intro b hb
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
      exact List.mem_map_of_mem (hsub₂ _ hd)
    refine ⟨cs₂, ?_, hnd₂, hreach₂, hcsub _ hinit, ?_⟩
    · show searchBody tm (codeBlocks k) (blockRuler W) r (codesOf W cs).flatten
        = (codesOf W cs₂).flatten
      rw [searchBody, hfit false c₀ hstep₀, hadd₁, hfit true c₁ hstep₁, hadd₂]
    · intro i hi hi' β
      have hi2 : i < r.length + 1 := hi
      have hlt : i < cs.length := by omega
      have hlt₁ : i < cs₁.length := by omega
      have hbi : cs₂[i] = cs[i] := by
        rw [hget₂ i hlt₁ hi', hget₁ i hlt hlt₁]
      rw [hbi]
      rcases Nat.lt_or_ge i r.length with hir | hir
      · exact hcsub _ (hclos i hir hlt β)
      · have hieq : i = r.length := by omega
        subst hieq
        cases β
        · rw [hstep₀]
          exact hcsub₁ _ hmem₁
        · rw [hstep₁]
          exact hmem₂
  · rw [ite_eq_right hg]
    refine ⟨cs, rfl, hnd, hreach, hinit, ?_⟩
    intro i hi hi' β
    have hi2 : i < r.length + 1 := hi
    have hlt : i < r.length := by
      rw [hguard, hlen] at hg
      by_contra hcon
      have hle : (r.length + 1) * recordWidth k W ≤ cs.length * recordWidth k W :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    exact hclos i hlt hi' β

/-! ## A saturated search has found everything -/

/-- **Once the counter has passed every record, the search is complete.** -/
theorem searchOk_complete (tm : NTM k) {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (x : List Bool) (W : ℕ)
    (hq : Fintype.card tm.Q ≤ blockWidth W) (hW : x.length + S x.length + 1 ≤ W)
    (r V : List Bool) (h : SearchOk tm x W r V)
    (hsat : V.length ≤ r.length * recordWidth k W) {c : Cfg k tm.Q}
    (hc : tm.ReachesCfg (tm.initCfg x) c) :
    memFlag (wideRuler (codeBlocks k) (blockRuler W)) (Cobham.cfgCode W c) V = [true] := by
  obtain ⟨cs, rfl, hnd, hreach, hinit, hclos⟩ := h
  have hbs := codesOf_recordWidth W cs
  have hlen : (codesOf W cs).flatten.length = cs.length * recordWidth k W := by
    rw [length_flatten_records k W _ hbs, codesOf_length]
  have hpos := recordWidth_pos k W
  have hbr : cs.length ≤ r.length := by
    rw [hlen] at hsat
    by_contra hcon
    have : (r.length + 1) * recordWidth k W ≤ cs.length * recordWidth k W :=
      Nat.mul_le_mul_right _ (by omega)
    have hexp : (r.length + 1) * recordWidth k W
        = r.length * recordWidth k W + recordWidth k W := by ring
    omega
  refine (memFlag_records k W _ hbs _).mpr ?_
  induction hc with
  | refl => exact hinit
  | tail hbefore hstep ih =>
      rename_i c' c''
      obtain ⟨d, hd, hdeq⟩ := List.mem_map.mp ih
      obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem hd
      obtain ⟨hne, β, rfl⟩ := hstep
      have hkey := hclos i (by omega) hi β
      rw [hieq, hdeq, nstepFn_code tm β W _ hq
        (codeInv_of_reachesCfg tm hdec x hbefore W hW) hne] at hkey
      exact hkey

/-! ## How long the visited string can get -/

/-- **The visited string is bounded by the configuration count.** The records are
distinct and each is the code of a reachable configuration, and distinct
configurations of the graph have distinct codes in the finite type of
`Complexitylib.Classes.Containments.Internal.ConfigCount`. -/
theorem searchOk_length_le (tm : NTM k) {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (x : List Bool) (W : ℕ) (r V : List Bool)
    (h : SearchOk tm x W r V) :
    V.length ≤ Fintype.card (Code tm.Q k x.length (S x.length)) * recordWidth k W := by
  obtain ⟨cs, rfl, hnd, hreach, -, -⟩ := h
  rw [length_flatten_records k W _ (codesOf_recordWidth W cs), codesOf_length]
  refine Nat.mul_le_mul_right _ ?_
  have hspace : ∀ c', tm.ReachesCfg (tm.initCfg x) c' →
      c'.WithinDecisionSpace x.length (S x.length) :=
    fun c' hc' => NTM.withinDecisionSpace_of_reachesCfg hdec x hc'
  have hwin : ∀ c ∈ cs, Windowed x (S x.length) c := fun c hc =>
    windowed_of_reachesCfg hspace (windowed_init tm.qstart x (S x.length)) (hreach c hc)
  have hcsnd : cs.Nodup := List.Nodup.of_map _ hnd
  have hinj : ∀ c ∈ cs, ∀ d ∈ cs,
      cfgCode x.length (S x.length) c = cfgCode x.length (S x.length) d → c = d := by
    intro c hc d hd heq
    exact cfgCode_inj (hwin c hc) (hspace c (hreach c hc)) (hwin d hd)
      (hspace d (hreach d hd)) heq
  have hmapnd : (cs.map (cfgCode x.length (S x.length))).Nodup :=
    List.Nodup.map_on hinj hcsnd
  calc cs.length = (cs.map (cfgCode x.length (S x.length))).length := by
        rw [List.length_map]
    _ ≤ Fintype.card (Code tm.Q k x.length (S x.length)) := List.Nodup.length_le_card hmapnd

end Complexity
