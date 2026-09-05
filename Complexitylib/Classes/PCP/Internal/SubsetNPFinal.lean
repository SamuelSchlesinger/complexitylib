/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.ConsistencyLang
public import Complexitylib.Classes.PCP.Internal.GuessVerifyGeneric

/-!
# `PCP[O(log n), O(1)] ⊆ NP`

A verifier with logarithmic randomness has polynomially many coin strings, so
its whole behaviour on an input is captured by a table of answers of polynomial
size. This module assembles the checks on such a table — that it has the right
width, that it is consistent, and that the verifier accepts on every coin
string — into a single polynomial-time verifier language, and hands it to the
guess-and-verify bridge.

The completeness and soundness conditions of `PCP` do the rest: a member has a
proof accepted always, and a non-member has none, since a proof accepted always
would give acceptance probability one rather than at most one half.

## Main results

- `Complexity.PCP_subset_NP` — the easy inclusion of the PCP theorem
-/

@[expose] public section

namespace Complexity

section

variable (r : ℕ → ℕ) (Q : ℕ)

/-- The witness has exactly one block per coin string. -/
noncomputable def lenLang : Language :=
  {z | (pairSnd z).length = 2 ^ r (pairFst z).length * Q}

open scoped Complexity in
theorem lenLang_mem_P
    (hr : (fun x : List Bool => List.replicate (r x.length) true) ∈ FP)
    (hrlog : r =O fun n => Nat.log 2 n) : lenLang r Q ∈ P := by
  have ha : (fun z : List Bool => List.replicate (pairSnd z).length false) ∈ FP :=
    zeroBlockFn_mem_FP Cobham.sndBlock_mem_FP
  have hexp : (fun z : List Bool =>
      List.replicate (2 ^ r (pairFst z).length) true) ∈ FP := by
    have := mem_FP_comp Cobham.fstBlock_mem_FP (unaryExp_mem_FP_of_bigO_log hr hrlog)
    exact this
  have hQ : (fun _ : List Bool => List.replicate Q false) ∈ FP :=
    Cobham.const_replicate_mem_FP Q
  have hb : (fun z : List Bool =>
      List.replicate (2 ^ r (pairFst z).length * Q) false) ∈ FP := by
    have := Cobham.mulLenFn_mem_FP hexp hQ
    refine mem_FP_of_eq this fun z => ?_
    rw [List.length_replicate, List.length_replicate]
  refine mem_P_of_decisionFn (eqFlagFn_mem_FP ha hb) fun z => ?_
  rw [exists_eqFlag_iff]
  constructor
  · intro h
    rw [lenLang, Set.mem_ofPred_eq] at h
    rw [h]
  · intro h
    have := congrArg List.length h
    rw [List.length_replicate, List.length_replicate] at this
    exact this

variable (V : PCPVerifier) (f : List Bool → List Bool)

/-- **The verifier language**: the witness has the right shape, is consistent,
and is accepted on every coin string. -/
noncomputable def witLang : Language :=
  lenLang r Q ∩ (consLang f r Q ∩ accLang V f r Q)

open scoped Complexity in
theorem witLang_mem_P (hf : f ∈ FP)
    (hr : (fun x : List Bool => List.replicate (r x.length) true) ∈ FP)
    (hrlog : r =O fun n => Nat.log 2 n) : witLang r Q V f ∈ P :=
  P_inter (lenLang_mem_P r Q hr hrlog)
    (P_inter (consLang_mem_P f r Q hf hr hrlog) (accLang_mem_P V f r Q hf hr hrlog))

theorem mem_witLang_iff
    (hfspec : ∀ x rr : List Bool,
      f (pair x rr) = DataEncode.bitstringEncode (V.positions x rr))
    (hQ : ∀ x rr : List Bool, (V.positions x rr).length ≤ Q) (x w : List Bool) :
    pair x w ∈ witLang r Q V f
      ↔ w.length = 2 ^ r x.length * Q ∧ V.Witness (r x.length) Q x w := by
  constructor
  · rintro ⟨hlen, hcons, hacc⟩
    have hlen' : w.length = 2 ^ r x.length * Q := by
      rw [lenLang, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair] at hlen
      exact hlen
    refine ⟨hlen', ?_, ?_⟩
    · exact (mem_consLang_iff V f r Q hfspec hlen' (hQ x)).mp hcons
    · exact (mem_accLang_iff V f r Q hfspec hlen' (hQ x)).mp hacc
  · rintro ⟨hlen, hcons, hacc⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [lenLang, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair]
      exact hlen
    · exact (mem_consLang_iff V f r Q hfspec hlen (hQ x)).mpr hcons
    · exact (mem_accLang_iff V f r Q hfspec hlen (hQ x)).mpr hacc

end

open scoped Complexity in
/-- **`PCP[O(log n), O(1)] ⊆ NP`.** A verifier's whole behaviour is a table of
answers of polynomial size; guessing that table and checking it is an `NP`
computation. -/
theorem PCP_subset_NP {r q : ℕ → ℕ}
    (hr : (fun x : List Bool => List.replicate (r x.length) true) ∈ FP)
    (hrlog : r =O fun n => Nat.log 2 n) (hq : q =O fun _ => 1) :
    PCP r q ⊆ NP := by
  rintro L ⟨V, hVq, hcomp, hsound⟩
  obtain ⟨K, hK⟩ := exists_const_query_bound hVq hq
  obtain ⟨f, hf, hfspec⟩ := V.positions_mem
  set Q := K + 1 with hQdef
  have hQ : ∀ x rr : List Bool, (V.positions x rr).length ≤ Q := fun x rr =>
    le_trans (hK x rr) (by omega)
  have hQ0 : 0 < Q := by omega
  obtain ⟨p₀, hp₀⟩ := exists_poly_two_pow_of_bigO_log hrlog
  refine mem_NP_of_poly_witness (p₀ * Polynomial.C Q)
    (witLang_mem_P r Q V f hf hr hrlog) ?_ ?_
  · intro x y hy
    rw [mem_witLang_iff r Q V f hfspec hQ] at hy
    rw [hy.1]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    exact Nat.mul_le_mul_right _ (hp₀ x.length)
  · intro x
    constructor
    · intro hx
      obtain ⟨π, hπ⟩ := hcomp x hx
      rw [V.eventProb_acceptEvent_eq_one_iff] at hπ
      refine ⟨V.witnessOf (r x.length) Q x π, ?_⟩
      rw [mem_witLang_iff r Q V f hfspec hQ]
      refine ⟨V.length_witnessOf _ _ _ _, ?_, ?_⟩
      · intro ρ ρ' i i' pp hpos hpos'
        rw [V.tableOf_witnessOf x π hQ0 (fun ρ => hQ x _),
          V.tableOf_witnessOf x π hQ0 (fun ρ => hQ x _)]
        exact V.consistent_of_proof _ x π ρ ρ' i i' pp hpos hpos'
      · intro ρ
        rw [V.tableOf_witnessOf x π hQ0 (fun ρ => hQ x _)]
        exact hπ ρ
    · rintro ⟨w, hw⟩
      rw [mem_witLang_iff r Q V f hfspec hQ] at hw
      obtain ⟨π, hπ⟩ := V.exists_proof_of_witness hw.2
      by_contra hx
      have h1 : eventProb (V.acceptEvent (r x.length) x π) = 1 :=
        (V.eventProb_acceptEvent_eq_one_iff _ x π).mpr hπ
      have h2 := hsound x hx π
      rw [h1] at h2
      norm_num at h2

end Complexity
