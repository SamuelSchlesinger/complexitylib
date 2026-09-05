/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.PermArith
public import Complexitylib.Classes.PCP.Internal.PermCount

/-!
# A tuple of permutations that expands

The counting argument. Of the `(n!)^30` tuples of thirty permutations of
`Fin n`, not all can fail to expand: a tuple fails at a vertex set `S` of at
most half the vertices exactly when every one of its thirty permutations keeps
all but a tenth of `S` inside `S`. `PermCount` bounds how many permutations do
that for a fixed `S`; `PermArith.key_estimate` turns the thirtieth power of that
bound into `(n!)^30 / 2^{|S|}`, with room to spare for the `C(n,s)` sets of each
size; and summing `2^{-s}` over `s ≥ 1` stays below one.

Everything is done with natural numbers — the geometric series appears as an
induction that carries the slack `+ K` explicitly, so no division is needed.

## Main definitions

- `Complexity.escLE` — the permutations keeping all but `t` points of `S` in `S`
- `Complexity.tOf` — the escape a set of a given size is allowed

## Main results

- `Complexity.exists_good_perms` — a tuple of thirty permutations for which
  every set of at most half the vertices is moved out of itself, by at least a
  tenth of it, by one of them
-/

@[expose] public section

namespace Complexity

open Finset

variable {n : ℕ}

/-- The permutations moving at most `t` points of `S` out of `S`. -/
noncomputable def escLE (S : Finset (Fin n)) (t : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun σ => escape σ S ≤ t

/-- The escape a set of size `s` is allowed before it counts as expanding. -/
def tOf (S : Finset (Fin n)) : ℕ := (S.card - 1) / 10

theorem ten_mul_tOf_le (S : Finset (Fin n)) : 10 * tOf S ≤ S.card := by
  rw [tOf]
  omega

theorem mem_escLE_iff {S : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} (hS : 1 ≤ S.card) :
    σ ∈ escLE S (tOf S) ↔ ¬ S.card ≤ 10 * escape σ S := by
  simp only [escLE, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold tOf
  omega

/-- The bound on how many permutations fail to expand a set of size `s`. -/
def escB (n s : ℕ) : ℕ :=
  s.choose ((s - 1) / 10) * s.descFactorial (s - (s - 1) / 10)
    * Nat.factorial (n - (s - (s - 1) / 10))

theorem card_escLE_le (S : Finset (Fin n)) : (escLE S (tOf S)).card ≤ escB n S.card := by
  have hts : tOf S ≤ S.card := by have := ten_mul_tOf_le S; omega
  have h := card_perm_escape_le S (tOf S)
  rw [Nat.choose_symm hts] at h
  rw [escLE, escB, ← tOf]
  calc (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => escape σ S ≤ tOf S).card
      ≤ S.card.choose (tOf S)
        * (S.card.descFactorial (S.card - tOf S) * Nat.factorial (n - (S.card - tOf S))) := h
    _ = S.card.choose (tOf S) * S.card.descFactorial (S.card - tOf S)
        * Nat.factorial (n - (S.card - tOf S)) := by ring

/-- **The per-size estimate.** -/
theorem two_pow_mul_escB_le {s : ℕ} (hs : 1 ≤ s) (hsn : 2 * s ≤ n) :
    2 ^ s * (n.choose s * escB n s ^ 30) ≤ Nat.factorial n ^ 30 := by
  set t := (s - 1) / 10 with ht
  set k := s - t with hk
  have hts : t ≤ s := by omega
  have h9 : 9 * s ≤ 10 * k := by omega
  have hkn : k ≤ n := by omega
  exact key_estimate hs hsn h9 (count_bound (by omega) hts hkn)

/-! ### The geometric slack -/

private theorem sum_geom_bound {K : ℕ} :
    ∀ (n : ℕ) (h : ℕ → ℕ), h 0 = 0 → (∀ s, 1 ≤ s → s ≤ n → 2 ^ s * h s ≤ K) →
      2 ^ n * ∑ s ∈ Finset.range (n + 1), h s + K ≤ 2 ^ n * K := by
  intro n
  induction n with
  | zero =>
      intro h h0 _
      simp [h0]
  | succ p ih =>
      intro h h0 hb
      have hIH := ih h h0 fun s hs1 hsp => hb s hs1 (by omega)
      have hlast : 2 ^ (p + 1) * h (p + 1) ≤ K := hb (p + 1) (by omega) le_rfl
      rw [Finset.sum_range_succ]
      set A := 2 ^ p with hA
      set T0 := ∑ s ∈ Finset.range (p + 1), h s with hT0
      have hpow : (2 : ℕ) ^ (p + 1) = 2 * A := by rw [hA, pow_succ]; ring
      rw [hpow] at hlast ⊢
      set x := A * T0 with hx
      set y := A * h (p + 1) with hy
      set z := A * K with hz
      have e1 : 2 * A * (T0 + h (p + 1)) = 2 * x + 2 * y := by rw [hx, hy]; ring
      have e2 : 2 * A * K = 2 * z := by rw [hz]; ring
      have e3 : 2 * A * h (p + 1) = 2 * y := by rw [hy]; ring
      rw [e1, e2]
      rw [e3] at hlast
      omega

/-! ### The union bound -/

/-- **A tuple that expands.** -/
theorem exists_good_perms (n : ℕ) :
    ∃ σ : Fin 30 → Equiv.Perm (Fin n), ∀ S : Finset (Fin n), 2 * S.card ≤ n →
      S.Nonempty → ∃ i, S.card ≤ 10 * escape (σ i) S := by
  classical
  set badSets : Finset (Finset (Fin n)) :=
    Finset.univ.filter fun S => 2 * S.card ≤ n ∧ S.Nonempty with hbadSets
  set term : Finset (Fin n) → ℕ := fun S => (escLE S (tOf S)).card ^ 30 with hterm
  set h : ℕ → ℕ := fun s => ∑ S ∈ badSets.filter fun S => S.card = s, term S with hh
  -- the count of failing tuples
  set BAD : Finset (Fin 30 → Equiv.Perm (Fin n)) :=
    Finset.univ.filter fun σ => ∃ S ∈ badSets, ∀ i, σ i ∈ escLE S (tOf S) with hBAD
  have htotal : (Finset.univ : Finset (Fin 30 → Equiv.Perm (Fin n))).card
      = Nat.factorial n ^ 30 := by
    rw [Finset.card_univ, Fintype.card_pi]
    simp [Fintype.card_perm]
  have hbound : BAD.card ≤ ∑ S ∈ badSets, term S := by
    have hsub : BAD ⊆ badSets.biUnion fun S => Fintype.piFinset fun _ => escLE S (tOf S) := by
      intro σ hσ
      rw [hBAD, Finset.mem_filter] at hσ
      obtain ⟨S, hS, hall⟩ := hσ.2
      exact Finset.mem_biUnion.2 ⟨S, hS, Fintype.mem_piFinset.2 hall⟩
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    refine le_of_eq (Finset.sum_congr rfl fun S _ => ?_)
    rw [Fintype.card_piFinset, hterm]
    simp
  -- regroup by size
  have hmaps : ∀ S ∈ badSets, S.card ∈ Finset.range (n + 1) := by
    intro S hS
    rw [hbadSets, Finset.mem_filter] at hS
    exact Finset.mem_range.2 (by omega)
  have hregroup : ∑ S ∈ badSets, term S = ∑ s ∈ Finset.range (n + 1), h s :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  -- the per-size bound
  have hh0 : h 0 = 0 := by
    rw [hh]
    refine Finset.sum_eq_zero fun S hS => ?_
    exfalso
    rw [Finset.mem_filter, hbadSets, Finset.mem_filter] at hS
    have hempty : S = ∅ := Finset.card_eq_zero.1 hS.2
    exact absurd hS.1.2.2 (by rw [hempty]; exact Finset.not_nonempty_empty)
  have hhb : ∀ s, 1 ≤ s → s ≤ n → 2 ^ s * h s ≤ Nat.factorial n ^ 30 := by
    intro s hs1 _
    rcases Finset.eq_empty_or_nonempty (badSets.filter fun S => S.card = s) with he | ⟨S₀, hS₀⟩
    · rw [hh]
      simp only
      rw [he, Finset.sum_empty, Nat.mul_zero]
      positivity
    · have hS₀' := hS₀
      rw [Finset.mem_filter, hbadSets, Finset.mem_filter] at hS₀'
      have hsn : 2 * s ≤ n := by rw [← hS₀'.2]; exact hS₀'.1.2.1
      have hcards : ∀ S ∈ badSets.filter fun S => S.card = s, term S ≤ escB n s ^ 30 := by
        intro S hS
        rw [Finset.mem_filter] at hS
        have := card_escLE_le S
        rw [hS.2] at this
        rw [hterm]
        exact Nat.pow_le_pow_left this 30
      have hcnt : (badSets.filter fun S => S.card = s).card ≤ n.choose s := by
        have hsub : (badSets.filter fun S => S.card = s)
            ⊆ Finset.powersetCard s Finset.univ := by
          intro S hS
          rw [Finset.mem_filter] at hS
          exact Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS.2⟩
        have := Finset.card_le_card hsub
        rwa [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at this
      have hsum : h s ≤ n.choose s * escB n s ^ 30 := by
        rw [hh]
        calc ∑ S ∈ badSets.filter fun S => S.card = s, term S
            ≤ (badSets.filter fun S => S.card = s).card • escB n s ^ 30 := by
              refine Finset.sum_le_card_nsmul _ _ _ fun S hS => ?_
              exact hcards S hS
          _ = (badSets.filter fun S => S.card = s).card * escB n s ^ 30 := by
              rw [smul_eq_mul]
          _ ≤ n.choose s * escB n s ^ 30 := Nat.mul_le_mul_right _ hcnt
      calc 2 ^ s * h s ≤ 2 ^ s * (n.choose s * escB n s ^ 30) := Nat.mul_le_mul_left _ hsum
        _ ≤ Nat.factorial n ^ 30 := two_pow_mul_escB_le hs1 hsn
  -- conclude
  have hgeom := sum_geom_bound (K := Nat.factorial n ^ 30) n h hh0 hhb
  have hfacpos : 0 < Nat.factorial n ^ 30 := pow_pos (Nat.factorial_pos n) 30
  have hlt : ∑ S ∈ badSets, term S < Nat.factorial n ^ 30 := by
    rw [hregroup]
    have h2 : (0 : ℕ) < 2 ^ n := pow_pos (by norm_num) n
    nlinarith [hgeom, hfacpos, h2]
  have hBADlt : BAD.card < (Finset.univ : Finset (Fin 30 → Equiv.Perm (Fin n))).card := by
    rw [htotal]
    exact lt_of_le_of_lt hbound hlt
  obtain ⟨σ, -, hσ⟩ := Finset.exists_mem_notMem_of_card_lt_card hBADlt
  refine ⟨σ, fun S hS hSne => ?_⟩
  by_contra hcon
  push Not at hcon
  refine hσ ?_
  rw [hBAD, Finset.mem_filter]
  have hS1 : 1 ≤ S.card := Finset.card_pos.2 hSne
  refine ⟨Finset.mem_univ _, S, ?_,
    fun i => (mem_escLE_iff hS1).2 (by simpa using hcon i)⟩
  rw [hbadSets, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hS, hSne⟩

end Complexity
