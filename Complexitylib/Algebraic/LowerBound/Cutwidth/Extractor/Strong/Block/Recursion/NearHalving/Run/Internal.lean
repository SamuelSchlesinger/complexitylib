/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Run.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Unary
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Block.Program
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Unary
import Complexitylib.Classes.P.Iterate
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Tactic.PolyTime

/-!
# Exact and bounded evaluation of the near-halving payload loop

The encoded step follows the structured state on every canonical encoding.
Its numeric fields follow the actual rounded width schedule, while its
payload has fixed block width after each positive number of steps. Bounds
include static parameters, block counts, the arbitrary initial payload, and
the unused seed suffix. Zero-step runs require no entropy or reserve premise.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem nearHalvingBlockRunStepEval_encode (h Q E : Nat) (state : NearHalvingBlockRunState) :
    nearHalvingBlockRunStepEval (encodeNearHalvingBlockRun h Q E state) =
      encodeNearHalvingBlockRun h Q E (nearHalvingBlockRunStep h Q E state) := by
  simp only [nearHalvingBlockRunStepEval, encodeNearHalvingBlockRun, nearHalvingBlockRunStep,
    pairFst_pair, pairSnd_pair, List.length_replicate]

theorem nearHalvingBlockRunStepEval_iterate (h Q E : Nat) (state : NearHalvingBlockRunState)
    (i : Nat) :
    nearHalvingBlockRunStepEval^[i] (encodeNearHalvingBlockRun h Q E state) =
      encodeNearHalvingBlockRun h Q E ((nearHalvingBlockRunStep h Q E)^[i] state) := by
  have semiconj : Function.Semiconj (encodeNearHalvingBlockRun h Q E)
      (nearHalvingBlockRunStep h Q E) nearHalvingBlockRunStepEval :=
    fun state => (nearHalvingBlockRunStepEval_encode h Q E state).symm
  exact (semiconj.iterate_right i state).symm

theorem encodeNearHalvingBlockRun_length (h Q E : Nat) (state : NearHalvingBlockRunState) :
    (encodeNearHalvingBlockRun h Q E state).length =
      8 * state.width + 4 * state.remaining + 4 * state.remainingPower + 2 * state.count +
        4 * h + 2 * Q + 2 * E + 2 * state.payload.length + state.seeds.length + 28 := by
  simp only [encodeNearHalvingBlockRun, pair_length, List.length_replicate]
  lia

theorem nearHalvingBlockRun_numeric (N h Q E : Nat) (source seeds : List Bool)
    {i : Nat} (level : i ≤ h) :
    (nearHalvingBlockRun N h Q E i source seeds).width = nearHalvingBlockWidth N h Q E i ∧
      (nearHalvingBlockRun N h Q E i source seeds).remaining = h - i ∧
      (nearHalvingBlockRun N h Q E i source seeds).remainingPower = 2 ^ (h - i) := by
  induction i with
  | zero => simp [nearHalvingBlockRun, nearHalvingBlockRunInitial, nearHalvingBlockWidth]
  | succ i ih =>
    obtain ⟨width, remaining, power⟩ := ih (by lia)
    simp only [nearHalvingBlockRun] at width remaining power ⊢
    rw [Function.iterate_succ_apply']
    simp only [nearHalvingBlockRunStep, width, remaining, power]
    refine ⟨rfl, by lia, ?_⟩
    rw [show h - i = h - (i + 1) + 1 by lia, pow_succ]
    simp

theorem nearHalvingBlockRun_succ (N h Q E i : Nat) (source seeds : List Bool) :
    nearHalvingBlockRun N h Q E (i + 1) source seeds =
      nearHalvingBlockRunStep h Q E (nearHalvingBlockRun N h Q E i source seeds) :=
  Function.iterate_succ_apply' _ _ _

theorem nearHalvingBlockRun_seeds (N h Q E : Nat) (source seeds : List Bool)
    {i : Nat} (level : i ≤ h) :
    (nearHalvingBlockRun N h Q E i source seeds).seeds =
      seeds.drop ((Finset.range i).sum (nearHalvingBlockSeedWidth N h Q E)) := by
  induction i with
  | zero => simp [nearHalvingBlockRun, nearHalvingBlockRunInitial]
  | succ i ih =>
    have numeric := nearHalvingBlockRun_numeric N h Q E source seeds (by lia : i ≤ h)
    rw [nearHalvingBlockRun_succ]
    simp only [nearHalvingBlockRunStep, numeric.1, numeric.2.1, numeric.2.2, ih (by lia)]
    change (seeds.drop _).drop (nearHalvingBlockSeedWidth N h Q E i) = _
    rw [List.drop_drop, Finset.sum_range_succ]

theorem nearHalvingBlockRunStep_iterate_count (h Q E : Nat) (state : NearHalvingBlockRunState)
    (i : Nat) : ((nearHalvingBlockRunStep h Q E)^[i] state).count = 2 ^ i * state.count := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    change 2 * ((nearHalvingBlockRunStep h Q E)^[i] state).count = _
    rw [ih, pow_succ]
    ring

theorem nearHalvingBlockRun_count (N h Q E i : Nat) (source seeds : List Bool) :
    (nearHalvingBlockRun N h Q E i source seeds).count = 2 ^ i := by
  simp only [nearHalvingBlockRun, nearHalvingBlockRunStep_iterate_count,
    nearHalvingBlockRunInitial, Nat.mul_one]

theorem nearHalvingBlockRunStep_iterate_seeds_length (h Q E : Nat)
    (state : NearHalvingBlockRunState) (i : Nat) :
    ((nearHalvingBlockRunStep h Q E)^[i] state).seeds.length ≤ state.seeds.length := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    simp only [nearHalvingBlockRunStep, List.length_drop]
    exact (Nat.sub_le _ _).trans ih

theorem nearHalvingBlockRun_seeds_length (N h Q E i : Nat) (source seeds : List Bool) :
    (nearHalvingBlockRun N h Q E i source seeds).seeds.length ≤ seeds.length :=
  nearHalvingBlockRunStep_iterate_seeds_length h Q E
    (nearHalvingBlockRunInitial N h source seeds) i

private theorem nearHalvingBlockRunStep_payload_length (h Q E : Nat)
    (state : NearHalvingBlockRunState) :
    (nearHalvingBlockRunStep h Q E state).payload.length =
      (nearHalvingBlockRunStep h Q E state).count *
        (nearHalvingBlockRunStep h Q E state).width := by
  simp only [nearHalvingBlockRunStep, explicitBlockCondenserBits_length, List.length_replicate]
  rw [← explicitCondenserHalfWidth_double]
  ring

theorem nearHalvingBlockRunStep_iterate_payload_length (h Q E : Nat)
    (state : NearHalvingBlockRunState) {i : Nat} (positive : 0 < i) :
    ((nearHalvingBlockRunStep h Q E)^[i] state).payload.length =
      ((nearHalvingBlockRunStep h Q E)^[i] state).count *
        ((nearHalvingBlockRunStep h Q E)^[i] state).width := by
  cases i with
  | zero => lia
  | succ i =>
    rw [Function.iterate_succ_apply']
    exact nearHalvingBlockRunStep_payload_length h Q E _

theorem nearHalvingBlockRun_payload_length (N h Q E : Nat) (source seeds : List Bool)
    {i : Nat} (level : i ≤ h) (positive : 0 < i) :
    (nearHalvingBlockRun N h Q E i source seeds).payload.length =
      2 ^ i * nearHalvingBlockWidth N h Q E i := by
  have shape := nearHalvingBlockRunStep_iterate_payload_length h Q E
    (nearHalvingBlockRunInitial N h source seeds) positive
  change (nearHalvingBlockRun N h Q E i source seeds).payload.length =
    (nearHalvingBlockRun N h Q E i source seeds).count *
      (nearHalvingBlockRun N h Q E i source seeds).width at shape
  rw [nearHalvingBlockRun_count, (nearHalvingBlockRun_numeric N h Q E source seeds level).1]
    at shape
  exact shape

theorem nearHalvingBlockRun_iterate_bound (N h Q E : Nat) (source seeds : List Bool)
    {i : Nat} (level : i ≤ h)
    (valid : i = 0 ∨ (nearHalvingBlockEntropy h Q 0 ≤ N ∧
      2 * (6 * (nearHalvingBlockRate h + 1) *
        explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E + 2 * E) ≤ Q)) :
    (encodeNearHalvingBlockRun h Q E (nearHalvingBlockRun N h Q E i source seeds)).length ≤
      14 * N + 8 * h + 4 * 2 ^ h + 2 * Q + 2 * E +
        2 * source.length + seeds.length + 30 := by
  by_cases zero : i = 0
  · subst i
    simp only [encodeNearHalvingBlockRun_length, nearHalvingBlockRun,
      Function.iterate_zero_apply, nearHalvingBlockRunInitial]
    lia
  obtain ⟨capacity, reserve⟩ := valid.resolve_left zero
  have field_positive : 0 < 6 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget N (nearHalvingBlockEntropy h Q 0) E :=
    Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos _)) (explicitCondenserBudget_pos _ _ _)
  have positive : 0 < Q := by lia
  have numeric := nearHalvingBlockRun_numeric N h Q E source seeds level
  have payload := nearHalvingBlockRun_payload_length N h Q E source seeds level
    (Nat.pos_of_ne_zero zero)
  have widths := nearHalvingBlockWidth_bounds N h Q E capacity reserve level
  have counts := (nearHalvingBlock_count_le h Q positive level).trans capacity
  have payloads := nearHalvingBlock_payload_le N h Q E capacity reserve level
  have suffix := nearHalvingBlockRun_seeds_length N h Q E i source seeds
  have power := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le h i)
  rw [encodeNearHalvingBlockRun_length, numeric.1, numeric.2.1, numeric.2.2,
    nearHalvingBlockRun_count, payload]
  lia

theorem nearHalvingBlockRunStepEval_mem_FP : nearHalvingBlockRunStepEval ∈ FP := by
  unfold nearHalvingBlockRunStepEval
  polytime [nearHalvingBlockRate]

theorem nearHalvingBlockRun_mem_FP {N h Q E count : List Bool → Nat}
    {source seeds : List Bool → List Bool}
    (hN : UnaryFn N) (hh : UnaryFn h) (hQ : UnaryFn Q) (hE : UnaryFn E)
    (hcount : UnaryFn count) (hpower : UnaryFn fun z => 2 ^ h z)
    (hsource : source ∈ FP) (hseeds : seeds ∈ FP)
    (levels : ∀ z, count z ≤ h z)
    (valid : ∀ z, count z = 0 ∨ (nearHalvingBlockEntropy (h z) (Q z) 0 ≤ N z ∧
      2 * (6 * (nearHalvingBlockRate (h z) + 1) *
        explicitCondenserBudget (N z) (nearHalvingBlockEntropy (h z) (Q z) 0) (E z) +
          2 * E z) ≤ Q z)) :
    (fun z => encodeNearHalvingBlockRun (h z) (Q z) (E z)
      (nearHalvingBlockRun (N z) (h z) (Q z) (E z) (count z) (source z) (seeds z))) ∈ FP := by
  have start : (fun z => encodeNearHalvingBlockRun (h z) (Q z) (E z)
      (nearHalvingBlockRunInitial (N z) (h z) (source z) (seeds z))) ∈ FP := by
    unfold encodeNearHalvingBlockRun nearHalvingBlockRunInitial
    polytime
  have width : UnaryFn fun z =>
      14 * N z + 8 * h z + 4 * 2 ^ h z + 2 * Q z + 2 * E z +
        2 * (source z).length + (seeds z).length + 30 := by polytime
  have loop := iterate_mem_FP nearHalvingBlockRunStepEval_mem_FP start
    hcount.mem_FP width.mem_FP (fun z i hi => by
      simp only [List.length_replicate] at hi
      rw [nearHalvingBlockRunStepEval_iterate, List.length_replicate]
      apply nearHalvingBlockRun_iterate_bound (N z) (h z) (Q z) (E z)
        (source z) (seeds z) (hi.trans (levels z))
      rcases valid z with zero | budget
      · exact Or.inl (by lia)
      · exact Or.inr budget)
  refine mem_FP_of_eq loop fun z => ?_
  simp only [List.length_replicate, nearHalvingBlockRun]
  exact nearHalvingBlockRunStepEval_iterate (h z) (Q z) (E z) _ (count z)

end Algebraic.Cutwidth.Extractor.Internal
