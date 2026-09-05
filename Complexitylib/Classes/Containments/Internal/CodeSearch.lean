/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.BoundedReach

/-!
# The reachability search as a finite computation on codes

⚠️ Unreviewed by Bolton

`Complexitylib.Classes.Containments.Internal.BoundedReach` reduces membership to a bounded
breadth-first search in the configuration graph, but the rounds there are `Set (Cfg k tm.Q)` —
a specification, not a computation. This file replays the same search on the *codes* of
`Complexitylib.Classes.Containments.Internal.ConfigCount`: a round is a `Finset` operation on a
finite type, so the whole search is a finite, decidable iteration.

The bridge is a decoder. `cfgCode` forgets nothing about a configuration that respects the space
window, so it has a left inverse there, and the successor of a code is simply the code of the
successor of the configuration it denotes.

For a log-space machine the code type has polynomially many elements, so a round set is a
polynomially sized object and the search runs for polynomially many rounds — this is the data
structure a polynomial-time implementation manipulates.

## Main definitions

- `decodeCfg` — rebuild a configuration from its code
- `NTM.codeSucc`, `NTM.codeRound`, `NTM.reachCodes` — the search, on `Finset`s of codes

## Main results

- `decodeCfg_cfgCode` — decoding inverts coding inside the window
- `NTM.mem_reachCodes_iff` — the code search computes exactly the specified rounds
- `NTM.mem_iff_exists_mem_reachCodes` — membership as a finite search
- `logWindow_bigO` — the concrete window is still `O(log n)`
- `NL_finite_search` — for `NL`, a finite search whose window, round count, and accept test are
  all explicit arithmetic in the input length
-/

@[expose] public section

namespace Complexity

variable {k : ℕ} {Q : Type}

/-- Rebuild a configuration from its code. The input tape is restored from the input itself —
it is read-only — and each work and output cell beyond the window is restored to the blank that
the window invariant guarantees is there. -/
def decodeCfg (x : List Bool) (S : ℕ) (a : Code Q k x.length S) : Cfg k Q where
  state := a.1
  input := { head := a.2.1.val, cells := (Tape.init (x.map Γ.ofBool)).cells }
  work := fun i =>
    { head := (a.2.2.1 i).1.val
      cells := fun p => if h : p < S + 1 then (a.2.2.1 i).2 ⟨p, h⟩ else Γ.blank }
  output :=
    { head := a.2.2.2.1.val
      cells := fun p => if h : p < S + 2 then a.2.2.2.2 ⟨p, h⟩ else Γ.blank }

/-- **Decoding inverts coding on the configurations the search meets.** Inside the space window
the clamps in `cfgCode` are inert and the cells it drops are the ones `Windowed` pins down, so
nothing is lost. -/
theorem decodeCfg_cfgCode {x : List Bool} {S : ℕ} {c : Cfg k Q}
    (hw : Windowed x S c) (hs : c.WithinDecisionSpace x.length S) :
    decodeCfg x S (cfgCode x.length S c) = c := by
  refine Cfg.ext rfl ?_ ?_ ?_
  · refine Tape.ext ?_ hw.input.symm
    have : c.input.head ≤ x.length + S + 1 := hs.1.2
    simpa [decodeCfg, cfgCode] using by omega
  · funext i
    have hh : (c.work i).head ≤ S := hs.1.1 i
    refine Tape.ext ?_ ?_
    · simpa [decodeCfg, cfgCode] using by omega
    · funext p
      by_cases hp : p < S + 1
      · simp only [decodeCfg, cfgCode, dite_eq_left hp]
      · simp only [decodeCfg, cfgCode, dite_eq_right hp]
        exact (hw.work i p (by omega)).symm
  · have hh : c.output.head ≤ S + 1 := hs.2
    refine Tape.ext ?_ ?_
    · simpa [decodeCfg, cfgCode] using by omega
    · funext p
      by_cases hp : p < S + 2
      · simp only [decodeCfg, cfgCode, dite_eq_left hp]
      · simp only [decodeCfg, cfgCode, dite_eq_right hp]
        exact (hw.output p (by omega)).symm

namespace NTM

variable {tm : NTM k}

/-- The codes of the successors of the configuration a code denotes. -/
def codeSucc (tm : NTM k) (x : List Bool) (S : ℕ) (a : Code tm.Q k x.length S) :
    Finset (Code tm.Q k x.length S) :=
  if (decodeCfg x S a).state = tm.qhalt then ∅
  else {cfgCode x.length S (tm.stepCfg false (decodeCfg x S a)),
        cfgCode x.length S (tm.stepCfg true (decodeCfg x S a))}

/-- One round of the search: keep what is known and add every successor code. -/
def codeRound (tm : NTM k) (x : List Bool) (S : ℕ)
    (F : Finset (Code tm.Q k x.length S)) : Finset (Code tm.Q k x.length S) :=
  F ∪ F.biUnion (codeSucc tm x S)

/-- The search: `t` rounds of successor-closure starting from a single code. -/
def reachCodes (tm : NTM k) (x : List Bool) (S : ℕ) (a₀ : Code tm.Q k x.length S) :
    ℕ → Finset (Code tm.Q k x.length S)
  | 0 => {a₀}
  | t + 1 => codeRound tm x S (reachCodes tm x S a₀ t)

/-- **The code search computes exactly the specified rounds.** Every code in round `t` is the
code of a configuration in round `t`, and conversely. -/
theorem mem_reachCodes_iff {x : List Bool} {S : ℕ} {c₀ : Cfg k tm.Q}
    (hs : ∀ c, tm.ReachesCfg c₀ c → c.WithinDecisionSpace x.length S)
    (hw : ∀ c, tm.ReachesCfg c₀ c → Windowed x S c) :
    ∀ (t : ℕ) (a : Code tm.Q k x.length S),
      a ∈ reachCodes tm x S (cfgCode x.length S c₀) t ↔
        ∃ c ∈ reachSet tm c₀ t, cfgCode x.length S c = a := by
  intro t
  induction t with
  | zero =>
      intro a
      simp only [reachCodes, Finset.mem_singleton, reachSet, Set.mem_singleton_iff]
      exact ⟨fun h => ⟨c₀, rfl, h.symm⟩, fun ⟨c, hc, hca⟩ => by rw [hc] at hca; exact hca.symm⟩
  | succ t ih =>
      intro a
      simp only [reachCodes, codeRound, Finset.mem_union, Finset.mem_biUnion, reachSet_succ,
        Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · rintro (h | ⟨b, hb, hab⟩)
        · obtain ⟨c, hc, hca⟩ := (ih a).mp h
          exact ⟨c, Or.inl hc, hca⟩
        · obtain ⟨c, hc, rfl⟩ := (ih b).mp hb
          have hreach := reachesCfg_of_mem_reachSet tm c₀ t hc
          rw [codeSucc, decodeCfg_cfgCode (hw c hreach) (hs c hreach)] at hab
          by_cases hhalt : c.state = tm.qhalt
          · rw [ite_eq_left hhalt] at hab; exact absurd hab (Finset.notMem_empty a)
          · rw [ite_eq_right hhalt, Finset.mem_insert, Finset.mem_singleton] at hab
            rcases hab with rfl | rfl
            · exact ⟨tm.stepCfg false c, Or.inr ⟨c, hc, hhalt, false, rfl⟩, rfl⟩
            · exact ⟨tm.stepCfg true c, Or.inr ⟨c, hc, hhalt, true, rfl⟩, rfl⟩
      · rintro ⟨c, hc | ⟨c', hc', hhalt, b, rfl⟩, rfl⟩
        · exact Or.inl ((ih _).mpr ⟨c, hc, rfl⟩)
        · refine Or.inr ⟨cfgCode x.length S c', (ih _).mpr ⟨c', hc', rfl⟩, ?_⟩
          have hreach := reachesCfg_of_mem_reachSet tm c₀ t hc'
          rw [codeSucc, decodeCfg_cfgCode (hw c' hreach) (hs c' hreach), ite_eq_right hhalt]
          cases b
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- **Membership is a finite search over codes.** Every quantifier is over a finite type and
every operation is a `Finset` operation, so this is an algorithm — what remains for `NL ⊆ P` is
to bound its cost. -/
theorem mem_iff_exists_mem_reachCodes {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (x : List Bool) {N : ℕ}
    (hN : Fintype.card (Code tm.Q k x.length (S x.length)) ≤ N) :
    x ∈ L ↔ ∃ a ∈ reachCodes tm x (S x.length)
        (cfgCode x.length (S x.length) (tm.initCfg x)) N,
      (decodeCfg x (S x.length) a).state = tm.qhalt ∧
        (decodeCfg x (S x.length) a).output.cells 1 = Γ.one := by
  have hs : ∀ c, tm.ReachesCfg (tm.initCfg x) c → c.WithinDecisionSpace x.length (S x.length) :=
    fun _ h => withinDecisionSpace_of_reachesCfg hdec x h
  have hw : ∀ c, tm.ReachesCfg (tm.initCfg x) c → Windowed x (S x.length) c :=
    fun _ h => windowed_of_reachesCfg_init hdec x h
  rw [mem_iff_exists_mem_reachSet hdec x hN]
  constructor
  · rintro ⟨c, hmem, hhalt, hout⟩
    refine ⟨cfgCode x.length (S x.length) c, (mem_reachCodes_iff hs hw _ _).mpr ⟨c, hmem, rfl⟩, ?_⟩
    have hreach := reachesCfg_of_mem_reachSet tm _ _ hmem
    rw [decodeCfg_cfgCode (hw c hreach) (hs c hreach)]
    exact ⟨hhalt, hout⟩
  · rintro ⟨a, hmem, hhalt, hout⟩
    obtain ⟨c, hc, rfl⟩ := (mem_reachCodes_iff hs hw _ _).mp hmem
    have hreach := reachesCfg_of_mem_reachSet tm _ _ hc
    rw [decodeCfg_cfgCode (hw c hreach) (hs c hreach)] at hhalt hout
    exact ⟨c, hc, hhalt, hout⟩

end NTM

/-- The concrete window is still a logarithmic bound, so the code count over it stays
polynomial. -/
theorem logWindow_bigO (C D : ℕ) : logWindow C D =O (fun n => Nat.log 2 n) :=
  BigO.add (BigO.const_mul_left C (BigO.refl _)) (BigO.const_le_logTwo D)

/-- **A language in `NL` is a finite search of polynomially many rounds.** Every quantity in
this statement is an explicit arithmetic function of the input length and finitely many machine
constants: the window is `logWindow C D |x|`, the round count is `A · (|x| + 1) ^ B`, the rounds
are `Finset`s of codes over that window, and the accept test is a decidable property of a single
code. No trace, choice sequence, machine time bound, or asymptotic quantifier survives. This is
the specification a polynomial-time implementation has to run; what remains for `NL ⊆ P` is to
account for its cost. -/
theorem NL_finite_search {L : Language} (hL : L ∈ NL) :
    ∃ (k : ℕ) (tm : NTM k) (C D A B : ℕ),
      ∀ x : List Bool, x ∈ L ↔
        ∃ a ∈ NTM.reachCodes tm x (logWindow C D x.length)
            (cfgCode x.length (logWindow C D x.length) (tm.initCfg x))
            (A * (x.length + 1) ^ B),
          (decodeCfg x (logWindow C D x.length) a).state = tm.qhalt ∧
            (decodeCfg x (logWindow C D x.length) a).output.cells 1 = Γ.one := by
  obtain ⟨k, tm, S, _, hdec, hS⟩ := hL
  obtain ⟨C, D, hCD⟩ := exists_log_bound hS
  have hdec' : tm.DecidesInSpace L (logWindow C D) :=
    NTM.DecidesInSpace.mono (fun n => hCD n) hdec
  obtain ⟨A, B, hAB⟩ := exists_config_bound (k := k) tm.Q (logWindow_bigO C D)
  exact ⟨k, tm, C, D, A, B, fun x => NTM.mem_iff_exists_mem_reachCodes hdec' x (hAB x.length)⟩

end Complexity
