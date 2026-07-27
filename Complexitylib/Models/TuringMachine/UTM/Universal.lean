/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.UTM.Internal.SimLoop
public import Complexitylib.Models.TuringMachine.UTM.Internal.Terminated
public import Complexitylib.Models.TuringMachine.Deterministic

/-!
# The universal machine: headline theorems

**Arora–Barak Theorem 1.9** (efficient universal simulation), in two forms:

* `utmTM_simulates_decider` — for any description `α` (with the standing
  region side condition, satisfied by every canonical encoding), if the
  interpreted machine decides `L` in time `T`, then the fixed machine
  `utmTM` decides membership of `x` from the input `pair α x` within
  `utmTime α (T |x|) |x|` steps — **linear in `T` with per-description
  constants**.
* `utmTM_universal` — one fixed six-work-tape machine universally simulates
  *every* multi-tape decider: for each `TM k` deciding `L` in time `T`
  there is a description `α` such that `utmTM` decides `L`'s membership
  from paired inputs within `utmTime α (singleTapeSimTime k T ·) ·` — the
  quadratic factor coming solely from the single-tape reduction.
-/

@[expose] public section

namespace Complexity

namespace TM.UTMBody

/-- Total running time of the universal machine on `pair α x` when the
    simulated machine halts within `T` steps (`n = |x|`). Linear in `T`;
    all other dependence is on the description alone. -/
def utmTime (α : List Bool) (T n : ℕ) : ℕ :=
  4 * (2 * α.length + 2 + n) + 4 * (groupPairs α).length + 25 +
    ((T + 1) * utmStepTime α + 1 + (2 * T + 9))

/-- **Universal simulation of deciders** (AB Theorem 1.9). If the machine
    described by `α` decides `L` within `T`, the universal machine reads
    `pair α x` and reports `x ∈ L` within `utmTime α (T |x|) |x|` steps. -/
theorem utmTM_simulates_decider {α : List Bool} (hterm : TerminatedRegion α)
    {L : Language} {T : ℕ → ℕ}
    (hdec : (decodeDesc α).toTM.DecidesInTime L T) (x : List Bool) :
    ∃ c' t, t ≤ utmTime α (T x.length) x.length ∧
      utmTM.reachesIn t (utmTM.initCfg (pair α x)) c' ∧
      utmTM.halted c' ∧
      (x ∈ L → c'.output.cells 1 = Γ.one) ∧
      (x ∉ L → c'.output.cells 1 = Γ.zero) := by
  obtain ⟨mcF, t₀, ht₀, hrun, hhalt, hmem, hnmem⟩ := hdec x
  have hht := utmTM_hoareTime α x hterm t₀ mcF hrun hhalt
  obtain ⟨c', t, ht, hreach, hhalt', hpost⟩ :=
    hht (Tape.init ((pair α x).map Γ.ofBool)) (fun _ => Tape.init [])
      (Tape.init []) ⟨rfl, fun _ => rfl, rfl⟩
  obtain ⟨m, hm, -, -, hagree⟩ := hpost
  have hcell1 : c'.output.cells 1 = mcF.output.cells 1 := hagree 0 (by omega)
  refine ⟨c', t, ?_, hreach, hhalt', fun hx => by rw [hcell1]; exact hmem hx,
    fun hx => by rw [hcell1]; exact hnmem hx⟩
  calc t ≤ 4 * (pair α x).length + 4 * (groupPairs α).length + 24 + 1 +
      ((t₀ + 1) * utmStepTime α + 1 + (2 * t₀ + 9)) := ht
    _ ≤ utmTime α (T x.length) x.length := by
      unfold utmTime
      rw [pair_length]
      have hmul : (t₀ + 1) * utmStepTime α
          ≤ (T x.length + 1) * utmStepTime α :=
        Nat.mul_le_mul_right _ (by omega)
      omega

/-- **One machine simulates them all**: for every multi-tape decider there
    is a description under which the fixed universal machine decides the
    same language from paired inputs, at single-tape-reduction (quadratic)
    cost. -/
theorem utmTM_universal {k : ℕ} (M : TM k) {L : Language} {T : ℕ → ℕ}
    (hdec : M.DecidesInTime L T) :
    ∃ α : List Bool, ∀ x : List Bool,
      ∃ c' t, t ≤ utmTime α (NTM.singleTapeSimTime k T x.length) x.length ∧
        utmTM.reachesIn t (utmTM.initCfg (pair α x)) c' ∧
        utmTM.halted c' ∧
        (x ∈ L → c'.output.cells 1 = Γ.one) ∧
        (x ∉ L → c'.output.cells 1 = Γ.zero) := by
  obtain ⟨M₁, hM₁⟩ := TM.exists_singleTape_decidesInTime M hdec
  have hwf := TM.descOfTM_wf M₁
  have hterm : TerminatedRegion (encodeDesc (TM.descOfTM M₁)) :=
    terminatedRegion_encodeDesc_plain hwf (descOfTM_entries_ne_nil M₁)
  have hdec' : (decodeDesc (encodeDesc (TM.descOfTM M₁))).toTM.DecidesInTime L
      (NTM.singleTapeSimTime k T) := by
    rw [decodeDesc_encodeDesc hwf]
    exact TM.descOfTM_decidesInTime M₁ hM₁
  exact ⟨encodeDesc (TM.descOfTM M₁),
    fun x => utmTM_simulates_decider hterm hdec' x⟩

/-- **Padded universality**: the description of a decider works under
    arbitrary padding — every machine has descriptions of every sufficiently
    large length, all correctly simulated. This is the form the
    hierarchy-theorem diagonalization consumes. -/
theorem utmTM_universal_padded {k : ℕ} (M : TM k) {L : Language} {T : ℕ → ℕ}
    (hdec : M.DecidesInTime L T) :
    ∃ α₀ : List Bool, ∀ junk x : List Bool,
      ∃ c' t, t ≤ utmTime (α₀ ++ junk)
          (NTM.singleTapeSimTime k T x.length) x.length ∧
        utmTM.reachesIn t (utmTM.initCfg (pair (α₀ ++ junk) x)) c' ∧
        utmTM.halted c' ∧
        (x ∈ L → c'.output.cells 1 = Γ.one) ∧
        (x ∉ L → c'.output.cells 1 = Γ.zero) := by
  obtain ⟨M₁, hM₁⟩ := TM.exists_singleTape_decidesInTime M hdec
  have hwf := TM.descOfTM_wf M₁
  refine ⟨encodeDesc (TM.descOfTM M₁), fun junk x => ?_⟩
  have hterm : TerminatedRegion (encodeDesc (TM.descOfTM M₁) ++ junk) :=
    terminatedRegion_encodeDesc hwf (descOfTM_entries_ne_nil M₁) junk
  have hdec' : (decodeDesc (encodeDesc (TM.descOfTM M₁) ++ junk)).toTM.DecidesInTime
      L (NTM.singleTapeSimTime k T) := by
    rw [decodeDesc_encodeDesc_append hwf]
    exact TM.descOfTM_decidesInTime M₁ hM₁
  exact utmTM_simulates_decider hterm hdec' x

end TM.UTMBody

end Complexity
