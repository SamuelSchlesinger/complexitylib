/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.EdgeExpansion
public import Complexitylib.Classes.PCP.Internal.ExpanderPad

/-!
# Cheeger's inequality: edge expansion gives a spectral gap

`EdgeExpansion` proved that a spectral gap forces every set to have many
boundary darts. This module proves the converse — the harder direction of
Cheeger's inequality — in the form the rest of the development consumes: a
`SpectralBound` below one, for the graph with a self-loop added per dart.

The argument is the classical one, made discrete.

* The **Dirichlet form** `∑ (f u - f w)²` over darts equals
  `2 d (‖f‖² - ⟨f, step f⟩)`.
* **Co-area.** For `ψ ≥ 0` supported on at most half the vertices,
  `∑ |ψ u - ψ w| ≥ 2 h d ∑ ψ`: peel off the lowest positive level, apply the
  expansion to the support, and induct on the support.
* **Cauchy–Schwarz** turns the co-area bound for `ψ = φ²` into
  `h² d ∑ φ² ≤ Dirichlet φ` for nonnegative `φ` of small support.
* **A median split** extends this to every mean-zero `f`, losing nothing.
* **The lazy walk.** Adding `d` loops halves the step operator plus the
  identity, which is positive semidefinite, and a Cauchy–Schwarz for
  semidefinite forms turns the Rayleigh bound into an operator bound — no
  spectral theorem needed.

## Main definitions

- `Complexity.RegGraph.EdgeExpansion` — every set of at most half the vertices
  has at least `h d |S|` boundary darts
- `Complexity.RegGraph.dirichlet` — the Dirichlet form over darts

## Main results

- `Complexity.RegGraph.dirichlet_ge_of_edgeExpansion` — `h² d ‖f‖² ≤ Dirichlet f`
  for mean-zero `f`
- `Complexity.RegGraph.spectralBound_padLoops_of_edgeExpansion` — the lazy
  graph has bound `1 - h² / 4`
-/

@[expose] public section

namespace Complexity

namespace RegGraph

variable (G : RegGraph)

/-! ### Darts and their reversal -/

/-- The reversal of darts, as a permutation. -/
def rotPerm : Equiv.Perm (G.V × G.D) := G.rot_involutive.toPerm

theorem nbr_rot (p : G.V × G.D) : G.nbr (G.rot p).1 (G.rot p).2 = p.1 := by
  show (G.rot (G.rot p)).1 = p.1
  rw [G.rot_involutive p]

/-- **Reversing every dart** swaps the two ends in a sum. -/
theorem sum_darts_swap (g : G.V → G.V → ℝ) :
    ∑ p : G.V × G.D, g p.1 (G.nbr p.1 p.2) = ∑ p : G.V × G.D, g (G.nbr p.1 p.2) p.1 := by
  refine Fintype.sum_equiv G.rotPerm _ _ fun p => ?_
  show g p.1 (G.nbr p.1 p.2) = g (G.nbr (G.rot p).1 (G.rot p).2) (G.rot p).1
  rw [nbr_rot]
  rfl

theorem sum_darts_fst (g : G.V → ℝ) :
    ∑ p : G.V × G.D, g p.1 = (G.deg : ℝ) * ∑ v : G.V, g v := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, card_eq_deg, nsmul_eq_mul]
  rw [← Finset.mul_sum]

theorem sum_darts_snd (g : G.V → ℝ) :
    ∑ p : G.V × G.D, g (G.nbr p.1 p.2) = (G.deg : ℝ) * ∑ v : G.V, g v := by
  rw [G.sum_darts_swap (fun _ w => g w)]
  exact G.sum_darts_fst g

theorem sum_mul_step (f g : G.V → ℝ) :
    ∑ v : G.V, f v * G.step g v = (∑ p : G.V × G.D, f p.1 * g (G.nbr p.1 p.2)) / (G.deg : ℝ) := by
  simp only [step, Fintype.sum_prod_type]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← mul_div_assoc, Finset.mul_sum]

/-! ### Edge expansion and the Dirichlet form -/

/-- **Edge expansion**: every set of at most half the vertices has at least
`h · d · |S|` darts leaving it. -/
def EdgeExpansion (h : ℝ) : Prop :=
  ∀ S : Finset G.V, 2 * S.card ≤ G.order →
    h * (G.deg : ℝ) * (S.card : ℝ) ≤ ((G.dartsBetween S Sᶜ).card : ℝ)

/-- The Dirichlet form: the sum over darts of the squared difference. -/
noncomputable def dirichlet (f : G.V → ℝ) : ℝ :=
  ∑ p : G.V × G.D, (f p.1 - f (G.nbr p.1 p.2)) ^ 2

theorem dirichlet_nonneg (f : G.V → ℝ) : 0 ≤ G.dirichlet f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The Dirichlet form and the step operator.** -/
theorem dirichlet_eq (f : G.V → ℝ) :
    G.dirichlet f = 2 * (G.deg : ℝ) * ((∑ v : G.V, (f v) ^ 2) - ∑ v : G.V, f v * G.step f v) := by
  have hd : (G.deg : ℝ) ≠ 0 := G.deg_ne_zero
  rw [sum_mul_step]
  simp only [dirichlet]
  have hexp : ∀ p : G.V × G.D, (f p.1 - f (G.nbr p.1 p.2)) ^ 2
      = (f p.1) ^ 2 + (f (G.nbr p.1 p.2)) ^ 2 - 2 * (f p.1 * f (G.nbr p.1 p.2)) := fun p => by ring
  rw [Finset.sum_congr rfl fun p _ => hexp p, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, G.sum_darts_fst (fun v => (f v) ^ 2), G.sum_darts_snd (fun v => (f v) ^ 2)]
  field_simp
  ring

/-- The Dirichlet form is invariant under adding a constant. -/
theorem dirichlet_sub_const (f : G.V → ℝ) (c : ℝ) :
    G.dirichlet (fun v => f v - c) = G.dirichlet f := by
  simp only [dirichlet]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-! ### Co-area -/

/-- The darts crossing out of or into `S`, counted with the boundary in both
directions. -/
theorem sum_darts_boundary (S : Finset G.V) :
    ∑ p : G.V × G.D, (if p.1 ∈ S ∧ G.nbr p.1 p.2 ∉ S then (1 : ℝ) else 0)
      + ∑ p : G.V × G.D, (if p.1 ∉ S ∧ G.nbr p.1 p.2 ∈ S then (1 : ℝ) else 0)
      = 2 * ((G.dartsBetween S Sᶜ).card : ℝ) := by
  classical
  have h1 : ∑ p : G.V × G.D, (if p.1 ∈ S ∧ G.nbr p.1 p.2 ∉ S then (1 : ℝ) else 0)
      = ((G.dartsBetween S Sᶜ).card : ℝ) := by
    rw [dartsBetween, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    simp
  have h2 : ∑ p : G.V × G.D, (if p.1 ∉ S ∧ G.nbr p.1 p.2 ∈ S then (1 : ℝ) else 0)
      = ((G.dartsBetween S Sᶜ).card : ℝ) := by
    rw [← h1, G.sum_darts_swap (fun u w => if u ∉ S ∧ w ∈ S then (1 : ℝ) else 0)]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [and_comm]
  rw [h1, h2]
  ring

/-- The support of a function. -/
noncomputable def support (ψ : G.V → ℝ) : Finset G.V := Finset.univ.filter fun v => ψ v ≠ 0

theorem mem_support_iff (ψ : G.V → ℝ) (v : G.V) : v ∈ G.support ψ ↔ ψ v ≠ 0 := by
  simp [support]

theorem eq_zero_of_notMem_support (ψ : G.V → ℝ) {v : G.V} (hv : v ∉ G.support ψ) : ψ v = 0 := by
  by_contra h
  exact hv ((G.mem_support_iff ψ v).2 h)

/-- **Co-area.** For `ψ ≥ 0` supported on at most half the vertices,
`∑ |ψ u - ψ w| ≥ 2 h d ∑ ψ`. -/
theorem coarea {h : ℝ} (hexp : G.EdgeExpansion h) :
    ∀ (n : ℕ) (ψ : G.V → ℝ), (G.support ψ).card = n → (∀ v, 0 ≤ ψ v)
      → 2 * (G.support ψ).card ≤ G.order
      → 2 * h * (G.deg : ℝ) * ∑ v : G.V, ψ v
        ≤ ∑ p : G.V × G.D, |ψ p.1 - ψ (G.nbr p.1 p.2)| := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ψ hn hpos hhalf
    by_cases hemp : G.support ψ = ∅
    · -- everything vanishes
      have hzero : ∀ v, ψ v = 0 := fun v => by
        by_contra hv
        have : v ∈ G.support ψ := by simp [support, hv]
        rw [hemp] at this
        exact absurd this (Finset.notMem_empty v)
      simp [hzero]
    · -- peel the lowest positive level
      have hne : (G.support ψ).Nonempty := Finset.nonempty_iff_ne_empty.2 hemp
      set S := G.support ψ with hS
      have hmem : ∀ v, v ∈ S ↔ ψ v ≠ 0 := fun v => by rw [hS]; exact G.mem_support_iff ψ v
      have hz : ∀ v, v ∉ S → ψ v = 0 := fun v hv => by
        by_contra h
        exact hv ((hmem v).2 h)
      set μ := (S.image ψ).min' (hne.image ψ) with hμ
      have hμmem : μ ∈ S.image ψ := Finset.min'_mem _ _
      obtain ⟨v₀, hv₀S, hv₀⟩ := Finset.mem_image.1 hμmem
      have hμpos : 0 < μ := by
        rw [← hv₀]
        exact lt_of_le_of_ne (hpos v₀) (Ne.symm ((hmem v₀).1 hv₀S))
      have hμle : ∀ v ∈ S, μ ≤ ψ v := fun v hv =>
        Finset.min'_le _ _ (Finset.mem_image_of_mem ψ hv)
      -- the peeled function
      set ψ' : G.V → ℝ := fun v => if v ∈ S then ψ v - μ else 0 with hψ'
      have hψ'in : ∀ v, v ∈ S → ψ' v = ψ v - μ := fun v hv => by simp [hψ', hv]
      have hψ'out : ∀ v, v ∉ S → ψ' v = 0 := fun v hv => by simp [hψ', hv]
      have hψ'pos : ∀ v, 0 ≤ ψ' v := fun v => by
        by_cases hv : v ∈ S
        · rw [hψ'in v hv]; linarith [hμle v hv]
        · rw [hψ'out v hv]
      have hψ'supp : G.support ψ' ⊆ S.erase v₀ := by
        intro v hv
        rw [G.mem_support_iff] at hv
        rw [Finset.mem_erase]
        by_cases hvS : v ∈ S
        · refine ⟨fun hvv => ?_, hvS⟩
          rw [hψ'in v hvS, hvv, hv₀, sub_self] at hv
          exact hv rfl
        · rw [hψ'out v hvS] at hv
          exact absurd rfl hv
      have hcard' : (G.support ψ').card < n := by
        rw [← hn]
        calc (G.support ψ').card ≤ (S.erase v₀).card := Finset.card_le_card hψ'supp
          _ < S.card := Finset.card_erase_lt_of_mem hv₀S
      have hhalf' : 2 * (G.support ψ').card ≤ G.order := by
        have := Finset.card_le_card hψ'supp
        omega
      have ihψ' := ih _ hcard' ψ' rfl hψ'pos hhalf'
      -- relate the two functions
      have hsum : ∑ v : G.V, ψ v = ∑ v : G.V, ψ' v + μ * S.card := by
        have : ∀ v, ψ v = ψ' v + (if v ∈ S then μ else 0) := fun v => by
          by_cases hv : v ∈ S
          · rw [hψ'in v hv, ite_eq_left hv]; ring
          · rw [hψ'out v hv, ite_eq_right hv, hz v hv]; ring
        rw [Finset.sum_congr rfl fun v _ => this v, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      have hdart : ∀ p : G.V × G.D, |ψ p.1 - ψ (G.nbr p.1 p.2)|
          = |ψ' p.1 - ψ' (G.nbr p.1 p.2)|
            + μ * ((if p.1 ∈ S ∧ G.nbr p.1 p.2 ∉ S then (1 : ℝ) else 0)
              + (if p.1 ∉ S ∧ G.nbr p.1 p.2 ∈ S then (1 : ℝ) else 0)) := by
        intro p
        by_cases hu : p.1 ∈ S <;> by_cases hw : G.nbr p.1 p.2 ∈ S
        · rw [hψ'in _ hu, hψ'in _ hw, ite_eq_right (by tauto), ite_eq_right (by tauto)]
          have : ψ p.1 - μ - (ψ (G.nbr p.1 p.2) - μ) = ψ p.1 - ψ (G.nbr p.1 p.2) := by ring
          rw [this]
          ring
        · rw [hψ'in _ hu, hψ'out _ hw, hz _ hw, ite_eq_left ⟨hu, hw⟩, ite_eq_right (by tauto),
          sub_zero,
            sub_zero, abs_of_nonneg (hpos _), abs_of_nonneg (by linarith [hμle _ hu])]
          ring
        · rw [hψ'out _ hu, hψ'in _ hw, hz _ hu, ite_eq_right (by tauto), ite_eq_left ⟨hu, hw⟩,
          zero_sub,
            zero_sub, abs_neg, abs_neg, abs_of_nonneg (hpos _),
            abs_of_nonneg (by linarith [hμle _ hw])]
          ring
        · rw [hψ'out _ hu, hψ'out _ hw, hz _ hu, hz _ hw, ite_eq_right (by tauto),
          ite_eq_right (by tauto)]
          simp
      rw [Finset.sum_congr rfl fun p _ => hdart p, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_add_distrib, G.sum_darts_boundary S, hsum]
      have hexpS := hexp S hhalf
      have hd : (0 : ℝ) ≤ G.deg := by positivity
      nlinarith [ihψ', hexpS, hμpos, hd]

/-! ### The core bound for small support -/

theorem support_sq (φ : G.V → ℝ) : G.support (fun v => (φ v) ^ 2) = G.support φ := by
  ext v
  simp [support, pow_eq_zero_iff]

/-- **Small support.** For `φ ≥ 0` supported on at most half the vertices,
`h² d ‖φ‖² ≤ Dirichlet φ`. -/
theorem dirichlet_ge_of_support {h : ℝ} (hexp : G.EdgeExpansion h) (hh : 0 ≤ h)
    (φ : G.V → ℝ) (hpos : ∀ v, 0 ≤ φ v) (hhalf : 2 * (G.support φ).card ≤ G.order) :
    h ^ 2 * (G.deg : ℝ) * ∑ v : G.V, (φ v) ^ 2 ≤ G.dirichlet φ := by
  classical
  have hd : (0 : ℝ) < G.deg := by exact_mod_cast G.deg_pos
  have hco := G.coarea hexp _ (fun v => (φ v) ^ 2) rfl (fun v => sq_nonneg _)
    (by rw [support_sq]; exact hhalf)
  -- `|a² - b²| = |a - b| (a + b)` for nonnegative `a, b`
  have habs : ∀ p : G.V × G.D, |(φ p.1) ^ 2 - (φ (G.nbr p.1 p.2)) ^ 2|
      = |φ p.1 - φ (G.nbr p.1 p.2)| * (φ p.1 + φ (G.nbr p.1 p.2)) := by
    intro p
    rw [sq_sub_sq, abs_mul, abs_of_nonneg (by linarith [hpos p.1, hpos (G.nbr p.1 p.2)])]
    ring
  rw [Finset.sum_congr rfl fun p _ => habs p] at hco
  -- Cauchy–Schwarz
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (G.V × G.D))
    (fun p => |φ p.1 - φ (G.nbr p.1 p.2)|) (fun p => φ p.1 + φ (G.nbr p.1 p.2))
  simp only [sq_abs] at hcs
  have hsumsq : ∑ p : G.V × G.D, (φ p.1 + φ (G.nbr p.1 p.2)) ^ 2
      ≤ 4 * (G.deg : ℝ) * ∑ v : G.V, (φ v) ^ 2 := by
    have : ∀ p : G.V × G.D, (φ p.1 + φ (G.nbr p.1 p.2)) ^ 2
        ≤ 2 * ((φ p.1) ^ 2 + (φ (G.nbr p.1 p.2)) ^ 2) := fun p => by
      nlinarith [sq_nonneg (φ p.1 - φ (G.nbr p.1 p.2))]
    calc ∑ p : G.V × G.D, (φ p.1 + φ (G.nbr p.1 p.2)) ^ 2
        ≤ ∑ p : G.V × G.D, 2 * ((φ p.1) ^ 2 + (φ (G.nbr p.1 p.2)) ^ 2) :=
          Finset.sum_le_sum fun p _ => this p
      _ = 4 * (G.deg : ℝ) * ∑ v : G.V, (φ v) ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, G.sum_darts_fst (fun v => (φ v) ^ 2),
            G.sum_darts_snd (fun v => (φ v) ^ 2)]
          ring
  have hS : 0 ≤ ∑ v : G.V, (φ v) ^ 2 := Finset.sum_nonneg fun v _ => sq_nonneg _
  have hD : 0 ≤ G.dirichlet φ := G.dirichlet_nonneg φ
  -- `dirichlet φ` is the first factor of Cauchy–Schwarz
  have hDeq : ∑ p : G.V × G.D, (φ p.1 - φ (G.nbr p.1 p.2)) ^ 2 = G.dirichlet φ := rfl
  rw [hDeq] at hcs
  set A := 2 * h * (G.deg : ℝ) * ∑ v : G.V, (φ v) ^ 2 with hA
  set B := ∑ p : G.V × G.D, |φ p.1 - φ (G.nbr p.1 p.2)| * (φ p.1 + φ (G.nbr p.1 p.2)) with hB
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hAB : A ^ 2 ≤ B ^ 2 := by
    have hB0 : 0 ≤ B := le_trans hA0 hco
    nlinarith [hco, hA0, hB0]
  have hkey : A ^ 2 ≤ G.dirichlet φ * (4 * (G.deg : ℝ) * ∑ v : G.V, (φ v) ^ 2) :=
    le_trans hAB (le_trans hcs (mul_le_mul_of_nonneg_left hsumsq hD))
  rw [hA] at hkey
  rcases hS.eq_or_lt with hS0 | hS0
  · rw [← hS0, mul_zero]; exact hD
  · have h4 : 0 < 4 * (G.deg : ℝ) * ∑ v : G.V, (φ v) ^ 2 := by positivity
    have : (2 * h * (G.deg : ℝ) * ∑ v : G.V, (φ v) ^ 2) ^ 2
        = (h ^ 2 * (G.deg : ℝ) * ∑ v : G.V, (φ v) ^ 2)
          * (4 * (G.deg : ℝ) * ∑ v : G.V, (φ v) ^ 2) := by
      ring
    rw [this] at hkey
    exact le_of_mul_le_mul_right hkey h4

/-! ### The median split -/

/-- **A median.** Some value has at most half the vertices strictly above it and at
most half strictly below. -/
theorem exists_median (f : G.V → ℝ) :
    ∃ c : ℝ, 2 * (Finset.univ.filter fun v => c < f v).card ≤ G.order
      ∧ 2 * (Finset.univ.filter fun v => f v < c).card ≤ G.order := by
  classical
  rcases isEmpty_or_nonempty G.V with hV | hV
  · exact ⟨0, by simp, by simp⟩
  have : Nonempty G.V := hV
  set T : Finset ℝ := (Finset.univ.image f).filter
    fun t => 2 * (Finset.univ.filter fun v => t < f v).card ≤ G.order with hT
  have hTne : T.Nonempty := by
    refine ⟨(Finset.univ.image f).max' (Finset.univ_nonempty.image f), ?_⟩
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.max'_mem _ _, ?_⟩
    have : (Finset.univ.filter fun v =>
        (Finset.univ.image f).max' (Finset.univ_nonempty.image f) < f v) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v _ hlt
      exact absurd (Finset.le_max' _ _ (Finset.mem_image_of_mem f (Finset.mem_univ v)))
        (not_le.2 hlt)
    rw [this]
    simp
  set c := T.min' hTne with hc
  have hcT : c ∈ T := Finset.min'_mem _ _
  rw [hT, Finset.mem_filter] at hcT
  refine ⟨c, hcT.2, ?_⟩
  by_contra hcon
  push Not at hcon
  -- the largest value below `c` would be a smaller member of `T`
  set L := Finset.univ.filter fun v => f v < c with hL
  have hLne : L.Nonempty := by
    rw [← Finset.card_pos]
    omega
  set t' := (L.image f).max' (hLne.image f) with ht'
  have ht'mem : t' ∈ L.image f := Finset.max'_mem _ _
  obtain ⟨v', hv'L, hv'⟩ := Finset.mem_image.1 ht'mem
  have hv'c : f v' < c := by
    have := hv'L
    rw [hL, Finset.mem_filter] at this
    exact this.2
  have ht'c : t' < c := by rw [← hv']; exact hv'c
  -- `{f > t'} = {f ≥ c}`
  have hset : (Finset.univ.filter fun v => t' < f v) = Finset.univ.filter fun v => ¬ f v < c := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    constructor
    · intro hlt
      by_contra hvc
      push Not at hvc
      have hvL : v ∈ L := by rw [hL, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hvc⟩
      have := Finset.le_max' (L.image f) (f v) (Finset.mem_image_of_mem f hvL)
      rw [← ht'] at this
      linarith
    · intro hge
      linarith
  have hcard : (Finset.univ.filter fun v => ¬ f v < c).card + L.card = G.order := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset G.V))
      (fun v => f v < c)
    rw [Finset.card_univ] at this
    rw [hL, add_comm]
    exact this
  have ht'T : t' ∈ T := by
    rw [hT, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [← hv']
      exact Finset.mem_image_of_mem f (Finset.mem_univ v')
    · rw [hset]
      omega
  have := Finset.min'_le T t' ht'T
  rw [← hc] at this
  linarith

theorem support_max_subset (g : G.V → ℝ) :
    G.support (fun v => max (g v) 0) ⊆ Finset.univ.filter fun v => 0 < g v := by
  intro v hv
  rw [mem_support_iff] at hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra hle
  push Not at hle
  exact hv (max_eq_right hle)

/-- **Cheeger's inequality, Dirichlet form.** For mean-zero `f`,
`h² d ‖f‖² ≤ Dirichlet f`. -/
theorem dirichlet_ge_of_edgeExpansion {h : ℝ} (hexp : G.EdgeExpansion h) (hh : 0 ≤ h)
    (f : G.V → ℝ) (hf : ∑ v : G.V, f v = 0) :
    h ^ 2 * (G.deg : ℝ) * ∑ v : G.V, (f v) ^ 2 ≤ G.dirichlet f := by
  classical
  obtain ⟨c, hc₁, hc₂⟩ := G.exists_median f
  set g : G.V → ℝ := fun v => f v - c with hg
  set gp : G.V → ℝ := fun v => max (g v) 0 with hgp
  set gm : G.V → ℝ := fun v => max (-g v) 0 with hgm
  -- supports
  have hsp : 2 * (G.support gp).card ≤ G.order := by
    have : (G.support gp).card ≤ (Finset.univ.filter fun v => 0 < g v).card :=
      Finset.card_le_card (G.support_max_subset g)
    have heq : (Finset.univ.filter fun v => 0 < g v) = Finset.univ.filter fun v => c < f v := by
      ext v; simp [hg]
    rw [heq] at this
    omega
  have hsm : 2 * (G.support gm).card ≤ G.order := by
    have : (G.support gm).card ≤ (Finset.univ.filter fun v => 0 < -g v).card :=
      Finset.card_le_card (G.support_max_subset (fun v => -g v))
    have heq : (Finset.univ.filter fun v => 0 < -g v) = Finset.univ.filter fun v => f v < c := by
      ext v; simp [hg]
    rw [heq] at this
    omega
  have hp := G.dirichlet_ge_of_support hexp hh gp (fun v => le_max_right _ _) hsp
  have hm := G.dirichlet_ge_of_support hexp hh gm (fun v => le_max_right _ _) hsm
  -- squares split
  have hsq : ∀ v, (g v) ^ 2 = (gp v) ^ 2 + (gm v) ^ 2 := by
    intro v
    simp only [hgp, hgm]
    rcases le_total (g v) 0 with hle | hle
    · rw [max_eq_right hle, max_eq_left (by linarith)]; ring
    · rw [max_eq_left hle, max_eq_right (by linarith)]; ring
  -- Dirichlet forms split, with slack
  have hdir : G.dirichlet gp + G.dirichlet gm ≤ G.dirichlet g := by
    simp only [dirichlet]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    simp only [hgp, hgm]
    rcases le_total (g p.1) 0 with h1 | h1 <;> rcases le_total (g (G.nbr p.1 p.2)) 0 with h2 | h2
    · rw [max_eq_right h1, max_eq_right h2, max_eq_left (by linarith), max_eq_left (by linarith)]
      nlinarith
    · rw [max_eq_right h1, max_eq_left h2, max_eq_left (by linarith), max_eq_right (by linarith)]
      nlinarith [mul_nonpos_iff.2 (Or.inr ⟨h1, h2⟩)]
    · rw [max_eq_left h1, max_eq_right h2, max_eq_right (by linarith), max_eq_left (by linarith)]
      nlinarith [mul_nonpos_iff.2 (Or.inl ⟨h1, h2⟩)]
    · rw [max_eq_left h1, max_eq_left h2, max_eq_right (by linarith), max_eq_right (by linarith)]
      nlinarith
  -- `‖g‖² ≥ ‖f‖²`
  have hnorm : ∑ v : G.V, (f v) ^ 2 ≤ ∑ v : G.V, (g v) ^ 2 := by
    have : ∀ v, (g v) ^ 2 = (f v) ^ 2 - 2 * c * f v + c ^ 2 := fun v => by
      simp only [hg]; ring
    rw [Finset.sum_congr rfl fun v _ => this v, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hf]
    have : 0 ≤ ∑ _v : G.V, c ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hdirg : G.dirichlet g = G.dirichlet f := G.dirichlet_sub_const f c
  have hsplit : ∑ v : G.V, (g v) ^ 2 = ∑ v : G.V, (gp v) ^ 2 + ∑ v : G.V, (gm v) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => hsq v
  have hd : (0 : ℝ) ≤ h ^ 2 * G.deg := by positivity
  calc h ^ 2 * (G.deg : ℝ) * ∑ v : G.V, (f v) ^ 2
      ≤ h ^ 2 * (G.deg : ℝ) * ∑ v : G.V, (g v) ^ 2 := mul_le_mul_of_nonneg_left hnorm hd
    _ = h ^ 2 * (G.deg : ℝ) * ∑ v : G.V, (gp v) ^ 2
          + h ^ 2 * (G.deg : ℝ) * ∑ v : G.V, (gm v) ^ 2 := by rw [hsplit]; ring
    _ ≤ G.dirichlet gp + G.dirichlet gm := add_le_add hp hm
    _ ≤ G.dirichlet g := hdir
    _ = G.dirichlet f := hdirg

/-! ### The lazy walk -/

/-- The lazy quadratic form, as an inner product of dart sums. -/
noncomputable def lazyQ (f g : G.V → ℝ) : ℝ :=
  ∑ p : G.V × G.D, (f p.1 + f (G.nbr p.1 p.2)) * (g p.1 + g (G.nbr p.1 p.2))

theorem step_lazy (f : G.V → ℝ) (v : G.V) :
    (G.padLoops G.deg).step f v = (G.step f v + f v) / 2 := by
  rw [step_padLoops]
  have hd : (G.deg : ℝ) ≠ 0 := G.deg_ne_zero
  field_simp
  ring

/-- **The lazy step against a function is the lazy form.** -/
theorem sum_lazy_mul (f g : G.V → ℝ) :
    ∑ v : G.V, (G.padLoops G.deg).step f v * g v = G.lazyQ f g / (4 * (G.deg : ℝ)) := by
  have hd : (G.deg : ℝ) ≠ 0 := G.deg_ne_zero
  simp only [step_lazy, lazyQ]
  have hexp : ∀ p : G.V × G.D, (f p.1 + f (G.nbr p.1 p.2)) * (g p.1 + g (G.nbr p.1 p.2))
      = f p.1 * g p.1 + f (G.nbr p.1 p.2) * g (G.nbr p.1 p.2)
        + (f p.1 * g (G.nbr p.1 p.2) + f (G.nbr p.1 p.2) * g p.1) := fun p => by ring
  rw [Finset.sum_congr rfl fun p _ => hexp p, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, G.sum_darts_fst (fun v => f v * g v),
    G.sum_darts_snd (fun v => f v * g v), G.sum_darts_swap (fun u w => f w * g u)]
  have h1 : ∑ v : G.V, (G.step f v + f v) / 2 * g v
      = (∑ v : G.V, g v * G.step f v + ∑ v : G.V, f v * g v) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun v _ => by ring
  have hswap : ∑ p : G.V × G.D, g p.1 * f (G.nbr p.1 p.2)
      = ∑ p : G.V × G.D, f p.1 * g (G.nbr p.1 p.2) := by
    rw [G.sum_darts_swap (fun u w => g u * f w)]
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  rw [h1, sum_mul_step, hswap]
  field_simp
  ring

theorem lazyQ_self (f : G.V → ℝ) :
    G.lazyQ f f = 4 * (G.deg : ℝ) * ∑ v : G.V, (f v) ^ 2 - G.dirichlet f := by
  simp only [lazyQ, dirichlet]
  have : ∀ p : G.V × G.D, (f p.1 + f (G.nbr p.1 p.2)) * (f p.1 + f (G.nbr p.1 p.2))
      = 2 * ((f p.1) ^ 2 + (f (G.nbr p.1 p.2)) ^ 2) - (f p.1 - f (G.nbr p.1 p.2)) ^ 2 :=
    fun p => by ring
  rw [Finset.sum_congr rfl fun p _ => this p, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_add_distrib, G.sum_darts_fst (fun v => (f v) ^ 2),
    G.sum_darts_snd (fun v => (f v) ^ 2)]
  ring

theorem lazyQ_nonneg (f : G.V → ℝ) : 0 ≤ G.lazyQ f f :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem lazyQ_sq_le (f g : G.V → ℝ) : (G.lazyQ f g) ^ 2 ≤ G.lazyQ f f * G.lazyQ g g := by
  have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (G.V × G.D))
    (fun p => f p.1 + f (G.nbr p.1 p.2)) (fun p => g p.1 + g (G.nbr p.1 p.2))
  simp only [lazyQ, sq] at this ⊢
  exact this

theorem sum_lazy_step (f : G.V → ℝ) :
    ∑ v : G.V, (G.padLoops G.deg).step f v = ∑ v : G.V, f v := by
  simp only [step_lazy]
  rw [← Finset.sum_div, Finset.sum_add_distrib, sum_step]
  ring

/-- **Cheeger's inequality, spectral form.** Edge expansion `h` gives the lazy
graph — `d` self-loops added — the spectral bound `1 - h² / 4`. -/
theorem spectralBound_padLoops_of_edgeExpansion {h : ℝ} (hexp : G.EdgeExpansion h) (hh : 0 ≤ h) :
    (G.padLoops G.deg).SpectralBound (1 - h ^ 2 / 4) := by
  intro f hf
  have hd : (0 : ℝ) < G.deg := by exact_mod_cast G.deg_pos
  set B : G.V → ℝ := (G.padLoops G.deg).step f with hB
  have hBmean : ∑ v : G.V, B v = 0 := by rw [hB]; erw [sum_lazy_step]; exact hf
  -- the Rayleigh bound, on `f` and on `B f`
  have hray : ∀ g : G.V → ℝ, ∑ v : G.V, g v = 0 →
      G.lazyQ g g ≤ (4 * (G.deg : ℝ) * (1 - h ^ 2 / 4)) * ∑ v : G.V, (g v) ^ 2 := by
    intro g hg
    rw [lazyQ_self]
    have := G.dirichlet_ge_of_edgeExpansion hexp hh g hg
    linarith
  have hf' := hray f hf
  have hB' := hray B hBmean
  -- `‖B f‖²` through the lazy form
  have hBB : ∑ v : G.V, (B v) ^ 2 = G.lazyQ f B / (4 * (G.deg : ℝ)) := by
    erw [← sum_lazy_mul, hB]
    exact Finset.sum_congr rfl fun v _ => by ring
  have hcs := G.lazyQ_sq_le f B
  have hQf := G.lazyQ_nonneg f
  have hQB := G.lazyQ_nonneg B
  have hSB : 0 ≤ ∑ v : G.V, (B v) ^ 2 := Finset.sum_nonneg fun v _ => sq_nonneg _
  show ∑ v : G.V, (B v) ^ 2 ≤ (1 - h ^ 2 / 4) ^ 2 * ∑ v : G.V, (f v) ^ 2
  set lam := 1 - h ^ 2 / 4 with hlam
  have hprod : G.lazyQ f f * G.lazyQ B B
      ≤ (4 * (G.deg : ℝ) * lam * ∑ v : G.V, (f v) ^ 2)
        * (4 * (G.deg : ℝ) * lam * ∑ v : G.V, (B v) ^ 2) :=
    mul_le_mul hf' hB' hQB (le_trans hQf hf')
  have hQfB : G.lazyQ f B = 4 * (G.deg : ℝ) * ∑ v : G.V, (B v) ^ 2 := by
    rw [hBB]; field_simp
  rw [hQfB] at hcs
  have hkey : (4 * (G.deg : ℝ)) ^ 2 * (∑ v : G.V, (B v) ^ 2) ^ 2
      ≤ (4 * (G.deg : ℝ)) ^ 2 * (lam ^ 2 * ∑ v : G.V, (f v) ^ 2) * ∑ v : G.V, (B v) ^ 2 := by
    nlinarith [hcs, hprod]
  rcases hSB.eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · have h16 : 0 < (4 * (G.deg : ℝ)) ^ 2 * ∑ v : G.V, (B v) ^ 2 := by positivity
    have : (4 * (G.deg : ℝ)) ^ 2 * (∑ v : G.V, (B v) ^ 2) ^ 2
        = ((4 * (G.deg : ℝ)) ^ 2 * ∑ v : G.V, (B v) ^ 2) * ∑ v : G.V, (B v) ^ 2 := by ring
    rw [this] at hkey
    have : (4 * (G.deg : ℝ)) ^ 2 * (lam ^ 2 * ∑ v : G.V, (f v) ^ 2) * ∑ v : G.V, (B v) ^ 2
        = ((4 * (G.deg : ℝ)) ^ 2 * ∑ v : G.V, (B v) ^ 2) * (lam ^ 2 * ∑ v : G.V, (f v) ^ 2) := by
      ring
    rw [this] at hkey
    exact le_of_mul_le_mul_left hkey h16

end RegGraph

end Complexity
