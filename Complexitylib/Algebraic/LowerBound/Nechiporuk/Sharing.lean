/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Nechiporuk.Sharing.Defs
public import Complexitylib.Algebraic.LowerBound.Nechiporuk.Sharing.Internal

/-!
# Programs with shared gates over the full binary basis

A `SharedProgram` over `Binary.Formula` on `n` inputs with `k` shared gates consists of `k`
intermediate formulas over the full binary basis together with one output formula, where each
formula may read the primary inputs and all previously computed shared values.

Fixing the coordinates outside a block `Y ⊆ Fin n` turns each of the `k + 1` formulas into a
subfunction of the coordinates in `Y` together with the active shared variables:
- If a shared formula `G` has no leaves in the current block (`G.leavesIn Y = 0`), then by
  `Formula.eval_eq_of_leavesIn_eq_zero` its value is constant once the outside coordinates are
  fixed, so its output wire is placed outside the block (`castBlock Y`) and contributes `0` to
  both the shared-gate count and the shared-leaf count on `Y`.
- If `G.leavesIn Y ≠ 0`, its output wire is included in the active block (`snocBlock Y`),
  contributing `1` active shared gate and `P.occ N` active shared-variable leaves.

Applying Nechiporuk's counting lemma (`Nechiporuk.card_subfunctions_le`) to the active formulas
yields
`|(subfunctions P.eval Y)| ≤ 2 ^ (P.activeShared Y + 1) · 16 ^ (P.inputLeavesIn Y +
  P.activeSharedLeaves Y)` (`SharedProgram.card_subfunctions_le_activeSharedLeaves`), which in turn
implies the global bound
`|(subfunctions P.eval Y)| ≤ 2 ^ (k + 1) · 16 ^ (P.inputLeavesIn Y + P.sharedLeaves n)`
(`SharedProgram.card_subfunctions_le_inputLeavesIn`).

Every single-output circuit `c` over `Binary.signature` decomposes from its last gate down into a
`SharedProgram` with `k ≤ KW.sharedGateCount c` shared gates, at most `c.size` binary gates, at
most `sharedFanOut c` total shared-variable leaves, and on every block `Y ⊆ Fin n`, at most
`activeSharedGateCount c Y` active shared gates and `activeSharedFanOut c Y` active shared-variable
leaves (`exists_sharedProgram_of_circuit`). Summed over a family of blocks, the active shared
fan-out weights each shared gate by the number of blocks its syntactic input cone meets
(`sum_activeSharedFanOut`, `sum_activeSharedFanOut_le_of_gateBlockSpan_le`).

The definitions live in `Complexitylib.Algebraic.LowerBound.Nechiporuk.Sharing.Defs` and the proof
internals in `Complexitylib.Algebraic.LowerBound.Nechiporuk.Sharing.Internal`.
-/

@[expose] public section

namespace Algebraic

namespace Nechiporuk

open scoped Classical
open Binary Cutwidth

namespace SharedProgram

variable {n N k : Nat}

/-- The input leaves of a program with `k` shared gates number at most `gates + k + 1`. -/
theorem inputLeaves_le_gates (m : Nat) : ∀ {N k : Nat} (P : SharedProgram N k),
    P.inputLeaves m ≤ P.gates + k + 1
  | _, _, output F => F.inputLeaves_le_gates_add_one m
  | _, _, share G P => by
    simp only [inputLeaves, gates]
    have := G.inputLeaves_le_gates_add_one m
    have := inputLeaves_le_gates m P
    omega

/-- Over pairwise disjoint blocks of `Fin n`, `inputLeavesIn` sums to at most `inputLeaves n`. -/
theorem sum_inputLeavesIn_le_inputLeaves {m n : Nat} (Y : Fin m → Finset (Fin n))
    (disjoint : Pairwise fun i j => Disjoint (Y i) (Y j)) :
    ∀ {N k : Nat} (P : SharedProgram N k), ∑ i, P.inputLeavesIn (Y i) ≤ P.inputLeaves n
  | _, _, output F => F.sum_inputLeavesIn_le_inputLeaves Y disjoint
  | _, _, share G P => by
    simp only [inputLeavesIn, inputLeaves, Finset.sum_add_distrib]
    exact Nat.add_le_add (G.sum_inputLeavesIn_le_inputLeaves Y disjoint)
      (sum_inputLeavesIn_le_inputLeaves Y disjoint P)

/-- At most `k` of the `k` shared gates of a program are active on any block. -/
theorem activeShared_le :
    ∀ {N k : Nat} (P : SharedProgram N k) (Y : Finset (Fin N)), P.activeShared Y ≤ k
  | _, 0, output _, _ => le_rfl
  | _, _ + 1, share G P, Y => by
    simp only [activeShared]
    have := activeShared_le P (stepBlock G Y)
    split_ifs <;> omega

/-- The shared-variable leaves reading active shared gates are among all shared-variable leaves. -/
theorem activeSharedLeaves_le_sharedLeaves :
    ∀ {N k : Nat} (P : SharedProgram N k) (Y : Finset (Fin N)),
      P.activeSharedLeaves Y ≤ P.sharedLeaves N
  | _, 0, output _, _ => Nat.zero_le _
  | N, _ + 1, share G P, Y => by
    simp only [activeSharedLeaves, sharedLeaves]
    have hP := activeSharedLeaves_le_sharedLeaves P (stepBlock G Y)
    have hsplit := P.sharedLeaves_eq_occ_add_sharedLeaves_succ N
    split_ifs <;> omega

/-- **Sharpened Nechiporuk counting lemma for programs with shared gates.** A program `P` has at
most `2 ^ (P.activeShared Y + 1) · 16 ^ (P.activeLeavesIn Y)` subfunctions on `Y`: shared gates
with no leaves in the current active block contribute neither to the exponent of `2` nor to the
active leaf count. -/
theorem card_subfunctions_le_active :
    ∀ {N k : Nat} (P : SharedProgram N k) (Y : Finset (Fin N)),
      (subfunctions P.eval Y).card ≤ 2 ^ (P.activeShared Y + 1) * 16 ^ P.activeLeavesIn Y
  | _, 0, output F, Y => by
    simpa [eval, activeShared, activeLeavesIn] using Nechiporuk.card_subfunctions_le Y F
  | N, _ + 1, share G P, Y => by
    by_cases hG : G.leavesIn Y = 0
    · calc (subfunctions (share G P).eval Y).card
          ≤ (subfunctions P.eval (castBlock Y)).card :=
            card_subfunctions_share_le_of_leavesIn_eq_zero G P Y hG
        _ ≤ 2 ^ (P.activeShared (castBlock Y) + 1) * 16 ^ P.activeLeavesIn (castBlock Y) :=
            card_subfunctions_le_active P (castBlock Y)
        _ = 2 ^ ((share G P).activeShared Y + 1) * 16 ^ (share G P).activeLeavesIn Y := by
            simp only [activeShared, activeLeavesIn, stepBlock, hG, ↓reduceIte, Nat.zero_add]
    · calc (subfunctions (share G P).eval Y).card
          ≤ (subfunctions G.eval Y).card * (subfunctions P.eval (snocBlock Y)).card :=
            card_subfunctions_share_le_mul G P Y
        _ ≤ (2 * 16 ^ G.leavesIn Y) *
              (2 ^ (P.activeShared (snocBlock Y) + 1) * 16 ^ P.activeLeavesIn (snocBlock Y)) :=
            Nat.mul_le_mul (Nechiporuk.card_subfunctions_le Y G)
              (card_subfunctions_le_active P (snocBlock Y))
        _ = 2 ^ ((share G P).activeShared Y + 1) * 16 ^ (share G P).activeLeavesIn Y := by
            simp only [activeShared, activeLeavesIn, stepBlock, hG, ↓reduceIte, pow_add, pow_one]
            ring

/-- A program `P` has at most
`2 ^ (P.activeShared Y + 1) · 16 ^ (P.inputLeavesIn Y + P.activeSharedLeaves Y)` subfunctions on a
primary block `Y ⊆ Fin n`. -/
theorem card_subfunctions_le_activeSharedLeaves (P : SharedProgram n k) (Y : Finset (Fin n)) :
    (subfunctions P.eval Y).card ≤
      2 ^ (P.activeShared Y + 1) * 16 ^ (P.inputLeavesIn Y + P.activeSharedLeaves Y) := by
  rw [← activeLeavesIn_eq_inputLeavesIn_add_activeSharedLeaves]
  exact P.card_subfunctions_le_active Y

/-- **Nechiporuk's counting lemma for programs with shared gates.** A program with `k` shared
gates has at most `2 ^ (k + 1) · 16 ^ (P.leavesIn Y)` subfunctions on `Y`. -/
theorem card_subfunctions_le :
    ∀ {N k : Nat} (P : SharedProgram N k) (Y : Finset (Fin N)),
      (subfunctions P.eval Y).card ≤ 2 ^ (k + 1) * 16 ^ P.leavesIn Y
  | _, 0, output F, Y => by
    simpa [eval, leavesIn] using Nechiporuk.card_subfunctions_le Y F
  | N, k + 1, share G P, Y => by
    calc (subfunctions (share G P).eval Y).card
        ≤ (subfunctions G.eval Y).card * (subfunctions P.eval (snocBlock Y)).card :=
          card_subfunctions_share_le_mul G P Y
      _ ≤ (2 * 16 ^ G.leavesIn Y) * (2 ^ (k + 1) * 16 ^ P.leavesIn (snocBlock Y)) :=
          Nat.mul_le_mul (Nechiporuk.card_subfunctions_le Y G)
            (card_subfunctions_le P (snocBlock Y))
      _ = 2 ^ (k + 1 + 1) * 16 ^ (share G P).leavesIn Y := by
          simp only [leavesIn, pow_add, pow_one]
          ring

/-- A program with `k` shared gates has at most
`2 ^ (k + 1) · 16 ^ (P.inputLeavesIn Y + P.sharedLeaves n)` subfunctions on `Y`. -/
theorem card_subfunctions_le_inputLeavesIn (P : SharedProgram n k) (Y : Finset (Fin n)) :
    (subfunctions P.eval Y).card ≤ 2 ^ (k + 1) * 16 ^ (P.inputLeavesIn Y + P.sharedLeaves n) := by
  rw [← leavesIn_eq_inputLeavesIn_add_sharedLeaves]
  exact P.card_subfunctions_le Y

end SharedProgram

/-! ### Shared fan-out and translation from binary circuits to `SharedProgram` -/

section BinaryCircuits

variable {σ : Signature} {n m t : Nat}

/-- Every shared gate has fan-out at least two, so there are at most `sharedFanOut c` of them. -/
theorem sharedGateCount_le_sharedFanOut (c : Circuit σ n m) :
    KW.sharedGateCount c ≤ sharedFanOut c := by
  rw [KW.sharedGateCount, sharedFanOut, Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun g hg => ?_
  have := (Finset.mem_filter.mp hg).2
  omega

/-- A circuit has at most `c.size` shared gates. -/
theorem sharedGateCount_le_size (c : Circuit σ n m) : KW.sharedGateCount c ≤ c.size :=
  (Finset.card_le_univ _).trans_eq (Fintype.card_fin c.size)

/-- The shared gates active on a block are among all shared gates. -/
theorem activeSharedGateCount_le_sharedGateCount (c : Circuit σ n m) (Y : Finset (Fin n)) :
    activeSharedGateCount c Y ≤ KW.sharedGateCount c := by
  apply Finset.card_le_card
  intro g hg
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
  exact hg.1

/-- The fan-out of the shared gates active on a block is at most the total shared fan-out. -/
theorem activeSharedFanOut_le_sharedFanOut (c : Circuit σ n m) (Y : Finset (Fin n)) :
    activeSharedFanOut c Y ≤ sharedFanOut c := by
  apply Finset.sum_le_sum_of_subset
  intro g hg
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
  exact hg.1

/-- Each active shared gate has fan-out at least two, so it contributes at least one to
`activeSharedFanOut c Y`. -/
theorem activeSharedGateCount_le_activeSharedFanOut (c : Circuit σ n m) (Y : Finset (Fin n)) :
    activeSharedGateCount c Y ≤ activeSharedFanOut c Y := by
  rw [activeSharedGateCount, activeSharedFanOut, Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun g hg => ?_
  have := (Finset.mem_filter.mp hg).2.1
  omega

/-- A gate is active on at most all `B` blocks. -/
theorem gateBlockSpan_le {B : Nat} (Y : Fin B → Finset (Fin n)) (p : Program σ n t) (g : Fin t) :
    gateBlockSpan Y p g ≤ B :=
  (Finset.card_le_univ _).trans_eq (Fintype.card_fin B)

/-- Summing `activeSharedGateCount` over a family of blocks equals summing the block-spans of all
shared gates. -/
theorem sum_activeSharedGateCount {B : Nat} (c : Circuit σ n m) (Y : Fin B → Finset (Fin n)) :
    ∑ i, activeSharedGateCount c (Y i) =
      ∑ g ∈ Finset.univ.filter (fun g => 2 ≤ KW.gateFanOut c g),
        gateBlockSpan Y c.program g := by
  simp only [activeSharedGateCount, gateBlockSpan, Finset.card_filter]
  rw [Finset.sum_comm]
  simp only [Finset.sum_filter]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases h : 2 ≤ KW.gateFanOut c g
  · simp [h]
  · simp [h]

/-- Summing `activeSharedFanOut` over a family of blocks equals summing
`KW.gateFanOut c g * gateBlockSpan Y c.program g` over all shared gates `g`. -/
theorem sum_activeSharedFanOut {B : Nat} (c : Circuit σ n m) (Y : Fin B → Finset (Fin n)) :
    ∑ i, activeSharedFanOut c (Y i) =
      ∑ g ∈ Finset.univ.filter (fun g => 2 ≤ KW.gateFanOut c g),
        KW.gateFanOut c g * gateBlockSpan Y c.program g := by
  simp only [activeSharedFanOut, gateBlockSpan, Finset.card_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases h : 2 ≤ KW.gateFanOut c g
  · simp only [h, true_and, ↓reduceIte, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  · simp [h]

/-- If every shared gate of `c` is active on at most `s` blocks of `Y`, then the sum of
`activeSharedFanOut c (Y i)` over all blocks is at most `s * sharedFanOut c`. -/
theorem sum_activeSharedFanOut_le_of_gateBlockSpan_le {B s : Nat} (c : Circuit σ n m)
    (Y : Fin B → Finset (Fin n))
    (hs : ∀ g : Fin c.size, 2 ≤ KW.gateFanOut c g → gateBlockSpan Y c.program g ≤ s) :
    ∑ i, activeSharedFanOut c (Y i) ≤ s * sharedFanOut c := by
  rw [sum_activeSharedFanOut, sharedFanOut, Finset.mul_sum]
  refine Finset.sum_le_sum fun g hg => ?_
  rw [mul_comm (KW.gateFanOut c g)]
  exact Nat.mul_le_mul_right _ (hs g (Finset.mem_filter.mp hg).2)

/-- Over `B` blocks, the active shared fan-out sums to at most `B * sharedFanOut c`. -/
theorem sum_activeSharedFanOut_le {B : Nat} (c : Circuit σ n m) (Y : Fin B → Finset (Fin n)) :
    ∑ i, activeSharedFanOut c (Y i) ≤ B * sharedFanOut c :=
  sum_activeSharedFanOut_le_of_gateBlockSpan_le c Y fun g _ => gateBlockSpan_le Y c.program g

/-- **Full-binary-basis circuits as programs with shared gates.** Every single-output circuit `c`
over `Binary.signature` computing `f` yields a `SharedProgram` computing `f` with at most
`KW.sharedGateCount c` shared gates, at most `c.size` binary gates, at most `sharedFanOut c`
shared-variable leaves, and on every block `Y ⊆ Fin n`, at most `activeSharedGateCount c Y`
active shared gates and `activeSharedFanOut c Y` active shared-variable leaves. -/
theorem exists_sharedProgram_of_circuit {n : Nat} (c : Circuit Binary.signature n 1)
    {f : Cslib.BooleanFunction n} (hc : c.ComputesWith Binary.interpretation fun x _ => f x) :
    ∃ k, ∃ P : SharedProgram n k,
      k ≤ KW.sharedGateCount c ∧ P.Computes f ∧
        P.gates ≤ c.size ∧ P.sharedLeaves n ≤ sharedFanOut c ∧
        ∀ Y : Finset (Fin n),
          P.activeShared Y ≤ activeSharedGateCount c Y ∧
            P.activeSharedLeaves Y ≤ activeSharedFanOut c Y := by
  obtain ⟨k, P, hk, hP, hgates, hshared, hact⟩ := exists_sharedProgram_of_program f c.program
    (fun g => (Finset.univ.filter fun o => c.outputs o = Wire.gate g).card) (j := 0)
    (SharedProgram.output (.var (c.outputs 0).index))
    (fun x => by
      have := congrFun (hc x) 0
      simp only [Circuit.eval, Function.comp_apply, Program.trace] at this
      simp [wireValues, KW.append_index, this])
    (fun g => by
      simp only [SharedProgram.occ, Formula.occ]
      split_ifs with h
      · exact Finset.card_pos.mpr ⟨0, by simpa using (KW.index_val_eq_iff _ g).mp h⟩
      · exact Nat.zero_le _)
  have hinit_shared :
      (SharedProgram.output (.var (c.outputs 0).index)).sharedLeaves (n + c.size) = 0 :=
    Formula.sharedLeaves_eq_zero_of_le le_rfl _
  refine ⟨k, P, by rw [KW.sharedGateCount_eq]; simpa using hk, hP, ?_, ?_, fun Y => ?_⟩
  · simpa [Formula.gates] using hgates
  · rw [sharedFanOut_eq]
    simpa [hinit_shared] using hshared
  · obtain ⟨hact1, hact2⟩ := hact Y
    rw [activeSharedGateCount_eq, activeSharedFanOut_eq]
    exact ⟨by simpa [SharedProgram.activeShared] using hact1,
      by simpa [SharedProgram.activeSharedLeaves] using hact2⟩

end BinaryCircuits

end Nechiporuk
end Algebraic
