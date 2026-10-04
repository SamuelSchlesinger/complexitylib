/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexitylib.Cslib.Circuit.Boolean.Complexity
public import Complexitylib.Cslib.Circuit.Family
public import Cslib.Computability.Circuit.Boolean.Lupanov
public import Cslib.Computability.Circuit.Boolean.Shannon
public import Cslib.Computability.Circuit.Boolean.Synthesis
import Cslib.Foundations.Data.Nat.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Ring

/-!
# Size classes of De Morgan circuit families

`SIZE s` is the class of languages decided by De Morgan circuit families with at most `s n` gates
on `n` inputs, following [Arora and Barak, Definition 6.1][AroraBarak09], and `PPoly` is the
class P/poly of languages decided by such families of polynomial size, following their
Definition 6.5. The bound in P/poly is `n ^ k + k` rather than
`n ^ k` because of the slice at length `0`: a circuit with no inputs has no wire to designate as
its output until it has a gate, so that slice costs at least one constant gate, which `0 ^ k` does
not allow when `k > 0`.

Lupanov's and Shannon's bounds carry over to families: every language has a family with at most
`(1 + ε) 2ⁿ/n` gates at all large lengths, while some language defeats every family with at most
`2ⁿ/n` gates at all large lengths and so lies outside P/poly. Since the circuits of a family need
not be related, P/poly also contains every unary language, including languages that no Turing
machine decides.

Ported from `Cslib.Computability.Circuit.Boolean.Family` at commit `2a4389b` of the author's
CSLib fork (branch `complexitylib-integration`); upstream CSLib does not have this module. It
keeps its `Cslib.Circuits.Boolean` namespace as a candidate for upstreaming.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*,
  Section 6.1][AroraBarak09]
-/

@[expose] public section

open Filter

namespace Cslib.Circuits.Boolean

/-- `SIZE(s)`: the languages decided by De Morgan circuit families with at most `s n` gates on
`n` inputs. -/
def SIZE (s : ℕ → ℕ) : Set (Language Bool) := {L | DecidableInSize L interpretation id s}

theorem mem_SIZE_iff {L : Language Bool} {s : ℕ → ℕ} :
    L ∈ SIZE s ↔ DecidableInSize L interpretation id s :=
  Iff.rfl

theorem SIZE_mono : Monotone SIZE := fun _ _ h _ hL => hL.mono h

/-- A language is in `SIZE s` exactly when every slice has complexity at most the bound. -/
theorem mem_SIZE_iff_complexity_le {L : Language Bool} {s : ℕ → ℕ} :
    L ∈ SIZE s ↔ ∀ n, complexity interpretation (fun x (_ : Fin 1) => L.slice n x) ≤ s n :=
  decidableInSize_id_iff_complexity_le

/-- P/poly: the languages decided by De Morgan circuit families of polynomial size. -/
def PPoly : Set (Language Bool) := ⋃ k, SIZE fun n => n ^ k + k

theorem mem_PPoly_iff {L : Language Bool} :
    L ∈ PPoly ↔ ∃ k, L ∈ SIZE fun n => n ^ k + k :=
  Set.mem_iUnion

theorem SIZE_subset_PPoly (k : ℕ) : SIZE (fun n => n ^ k + k) ⊆ PPoly :=
  Set.subset_iUnion (fun k => SIZE fun n => n ^ k + k) k

/-- Every polynomial bound lies below some `n ^ k + k` at every length: a large enough `k`
absorbs the leading coefficient for `n ≥ c` and the whole polynomial for `n < c`. -/
private theorem le_pow_add (c k d : ℕ) : ∃ k', ∀ n, c * n ^ k + d ≤ n ^ k' + k' := by
  refine ⟨c ^ (k + 1) + d + k + 1, fun n => ?_⟩
  rcases lt_or_ge n c with hn | hn
  · calc c * n ^ k + d ≤ c * c ^ k + d := by gcongr
      _ = c ^ (k + 1) + d := by ring
      _ ≤ n ^ (c ^ (k + 1) + d + k + 1) + (c ^ (k + 1) + d + k + 1) := by omega
  · rcases Nat.eq_zero_or_pos n with rfl | hpos
    · obtain rfl : c = 0 := by omega
      omega
    · calc c * n ^ k + d ≤ n * n ^ k + d := by gcongr
        _ = n ^ (k + 1) + d := by ring
        _ ≤ n ^ (c ^ (k + 1) + d + k + 1) + (c ^ (k + 1) + d + k + 1) := by
          have := Nat.pow_le_pow_right hpos (show k + 1 ≤ c ^ (k + 1) + d + k + 1 by omega)
          omega

/-- The bounds `n ^ k + k` are cofinal among polynomials, so a language decided within any
polynomial bound is in P/poly. -/
theorem mem_PPoly_of_le {L : Language Bool} {s : ℕ → ℕ} (hL : L ∈ SIZE s)
    (c k d : ℕ) (h : ∀ n, s n ≤ c * n ^ k + d) : L ∈ PPoly := by
  obtain ⟨k', hk'⟩ := le_pow_add c k d
  exact SIZE_subset_PPoly k' (SIZE_mono (fun n => (h n).trans (hk' n)) hL)

/-- Lupanov's bound for families: for every `ε > 0` there is a length beyond which every
language is decided by a family with at most `(1 + ε) 2ⁿ/n` gates per circuit. -/
theorem exists_decides_size_le (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ L : Language Bool, ∃ F : CircuitFamily signature,
      F.Decides interpretation id L ∧ ∀ n ≥ N, ((F n).size : ℝ) ≤ (1 + ε) * 2 ^ n / n := by
  obtain ⟨N, hN⟩ := Lupanov.exists_circuit ε hε
  refine ⟨N, fun L => ?_⟩
  have h (n : ℕ) : ∃ c : Circuit signature n 1,
      c.Computes interpretation (fun x _ => L.slice n x) ∧
      (N ≤ n → (c.size : ℝ) ≤ (1 + ε) * 2 ^ n / n) := by
    by_cases hn : N ≤ n
    · obtain ⟨c, hc, hs⟩ := hN n hn (L.slice n)
      exact ⟨c, hc, fun _ => hs⟩
    · obtain ⟨c, hc⟩ := Interpretation.IsComplete.exists_computes (I := interpretation)
        (fun x (_ : Fin 1) => L.slice n x)
      exact ⟨c, hc, fun h => absurd h hn⟩
  choose F hF hs using h
  exact ⟨F, CircuitFamily.decides_id_iff.mpr hF, hs⟩

/-- Shannon's bound for families: some language defeats, at all large lengths, every family
with at most `2ⁿ/n` gates per circuit. -/
theorem exists_language_lt_size :
    ∃ L : Language Bool, ∃ N : ℕ, ∀ F : CircuitFamily signature,
      F.Decides interpretation id L → ∀ n ≥ N, 2 ^ n / (n : ℝ) < ((F n).size : ℝ) := by
  obtain ⟨N, hN⟩ := Shannon.exists_hard_function
  have h (n : ℕ) : ∃ f : BooleanFunction n, N ≤ n →
      ∀ c : Circuit signature n 1,
        c.Computes interpretation (fun x _ => f x) → 2 ^ n / (n : ℝ) < c.size := by
    by_cases hn : N ≤ n
    · obtain ⟨f, hf⟩ := hN n hn
      exact ⟨f, fun _ => hf⟩
    · exact ⟨fun _ => false, fun h => absurd h hn⟩
  choose f hf using h
  exact ⟨Language.ofSlices f, N, fun F hF n hn =>
    hf n hn (F n) (by simpa using CircuitFamily.decides_id_iff.mp hF n)⟩

/-- Some language is not in P/poly. -/
theorem exists_not_mem_PPoly : ∃ L : Language Bool, L ∉ PPoly := by
  obtain ⟨L, N, hL⟩ := exists_language_lt_size
  refine ⟨L, fun h => ?_⟩
  obtain ⟨k, F, hF, hs⟩ := mem_PPoly_iff.mp h
  obtain ⟨M, hM⟩ := eventually_atTop.mp (Nat.eventually_mul_pow_le_pow (k + 1) (k + 1)
    Nat.one_lt_two)
  let n := max M (max N 1)
  have hpow := hM n (le_max_left _ _)
  have hn : max N 1 ≤ n := le_max_right _ _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (le_max_right N 1).trans hn
  have hlt : 2 ^ n < (F n).size * n := by
    exact_mod_cast (div_lt_iff₀ hn0).mp (hL F hF n ((le_max_left N 1).trans hn))
  have hle : (F n).size * n ≤ (k + 1) * n ^ (k + 1) := calc
    (F n).size * n ≤ (n ^ k + k) * n := Nat.mul_le_mul_right n (hs n)
    _ = n ^ (k + 1) + k * n := by ring
    _ ≤ n ^ (k + 1) + k * n ^ (k + 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left k (Nat.le_self_pow (by omega) n)) _
    _ = (k + 1) * n ^ (k + 1) := by ring
  exact lt_irrefl _ (hlt.trans_le (hle.trans hpow))

/-- The word of length `n` is all `true` exactly when every one of its bits is. -/
private theorem ofFn_eq_replicate_true_iff {n : ℕ} {x : BitString n} :
    List.ofFn x = List.replicate n true ↔ ∀ i, x i = true := by
  simp [List.eq_replicate_iff, List.mem_ofFn]

/-- A unary language, whose words consist only of `true`s, is decided by a family with at most
`n + 1` gates on `n` inputs: a constant when the word of length `n` is not in the language, and
otherwise a conjunction of the inputs, whose extra gate supplies the empty conjunction. -/
theorem mem_SIZE_of_unary {L : Language Bool} (hL : ∀ w ∈ L, ∀ b ∈ w, b = true) :
    L ∈ SIZE fun n => n + 1 := by
  rw [mem_SIZE_iff_complexity_le]
  intro n
  have hmem (x : BitString n) :
      List.ofFn x ∈ L ↔ List.replicate n true ∈ L ∧ ∀ i, x i = true := by
    refine ⟨fun hx => ?_, fun ⟨hn, hx⟩ => by rwa [ofFn_eq_replicate_true_iff.mpr hx]⟩
    have hx' : ∀ i, x i = true := fun i => hL _ hx _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact ⟨ofFn_eq_replicate_true_iff.mpr hx' ▸ hx, hx'⟩
  by_cases hn : List.replicate n true ∈ L
  · have hslice : L.slice n = fun x => decide (∀ i ∈ Finset.univ, x i = true) := by
      funext x
      rw [Bool.eq_iff_iff]
      simp [hmem, hn]
    have h := Synthesis.forall_mem (s := inputs n) Finset.univ
      (fun i (x : BitString n) => x i) (fun _ => 0) fun i _ => Synthesis.of_mem ⟨i, rfl⟩
    have hc := h.complexity_le
    unfold single at hc
    simpa [hslice] using hc
  · have hslice : L.slice n = fun _ => false := by
      funext x
      rw [Bool.eq_iff_iff]
      simp [hmem, hn]
    rw [hslice]
    exact (Synthesis.const false).complexity_le.trans (by omega)

/-- Every unary language is in P/poly. -/
theorem mem_PPoly_of_unary {L : Language Bool} (hL : ∀ w ∈ L, ∀ b ∈ w, b = true) :
    L ∈ PPoly :=
  SIZE_subset_PPoly 1 (by simpa using mem_SIZE_of_unary hL)

end Cslib.Circuits.Boolean
