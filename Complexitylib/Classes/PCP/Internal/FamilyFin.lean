/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.TowerFin
public import Complexitylib.Classes.PCP.Internal.MergeGen

/-!
# An expander of every size, numbered

`TowerFin` gives an expander at the tower's own sizes; a constraint graph asks
for one on exactly its own vertex count, and Dinur's degree reduction asks for
one on every vertex degree. This module closes the gap — fold the first large
enough member onto `n` vertices, then pad the degree with self-loops — keeping
every naming explicit, so that the rotation map stays a formula in numbers.

Nothing is numbered by an arbitrary bijection: a slot and a dart are packed with
`finProdFinEquiv`, and the padding with `finSumFinEquiv`. That is what lets
`famRotVal` compute the family's rotation map on raw numerals, which is what an
algorithm has to be handed.

## Main definitions

- `Complexity.FinBase.famGraph` — the member on `n` vertices
- `Complexity.FinBase.toFamily` — the family

## Main results

- `Complexity.FinBase.spectral_famGraph` — its spectral bound, below one
-/

@[expose] public section

namespace Complexity

namespace FinBase

variable (F : FinBase) (hd : 1 < F.deg)

/-! ### The member folded onto `n` vertices -/

/-- The tower level used for `n` vertices: the first one at least twice as big. -/
noncomputable def fitLevel (n : ℕ) : ℕ := F.level hd (2 * n)

/-- **A fit's level is at most twice the size asked for**, so the polynomial an
algorithm needs to bound the search is linear. -/
theorem fitLevel_le (n : ℕ) : F.fitLevel hd n ≤ 2 * n := F.level_le hd (2 * n)

/-- Its size. -/
noncomputable def fitN (n : ℕ) : ℕ := F.size (F.fitLevel hd n)

/-- The degree of every tower member. -/
def fitD : ℕ := F.deg ^ 2

theorem fitD_pos : 0 < F.fitD := F.sq_pos

theorem two_mul_le_fitN (n : ℕ) : 2 * n ≤ F.fitN hd n := F.le_size_level hd (2 * n)

/-- The width bound: the overshoot of the tower is at most `2 deg ^ 4`. -/
def widthBnd : ℕ := 2 * F.deg ^ 4 + 1

/-- The family's degree. -/
def famDeg : ℕ := F.widthBnd * F.fitD

theorem famDeg_pos : 0 < F.famDeg := by
  have h1 : 0 < F.widthBnd := by rw [widthBnd]; omega
  exact Nat.mul_pos h1 F.fitD_pos

theorem fitN_le {n : ℕ} (hn : 0 < n) : F.fitN hd n ≤ 2 * F.deg ^ 4 * n := by
  have h := F.size_level_le hd (2 * n) (by omega)
  rw [fitN, fitLevel]
  calc F.size (F.level hd (2 * n)) ≤ F.deg ^ 4 * (2 * n) := h
    _ = 2 * F.deg ^ 4 * n := by ring

/-- The width of the fold. -/
noncomputable def wid (n : ℕ) : ℕ := RegGraph.mergeWidth (F.fitN hd n) n

theorem three_le_wid {n : ℕ} (hn : 0 < n) : 3 ≤ F.wid hd n :=
  RegGraph.three_le_mergeWidth hn (F.two_mul_le_fitN hd n)

theorem wid_pos {n : ℕ} (hn : 0 < n) : 0 < F.wid hd n := by
  have := F.three_le_wid hd hn
  omega

theorem wid_le {n : ℕ} (hn : 0 < n) : F.wid hd n ≤ F.widthBnd :=
  RegGraph.mergeWidth_le hn (F.fitN_le hd hn)

theorem fitN_le_wid_mul {n : ℕ} (hn : 0 < n) : F.fitN hd n ≤ F.wid hd n * n :=
  RegGraph.le_mergeWidth_mul _ hn

theorem wid_sub_one_mul_le (n : ℕ) : (F.wid hd n - 1) * n ≤ F.fitN hd n :=
  RegGraph.mergeWidth_sub_one_mul_le _ _

theorem wid_mul_fitD_le {n : ℕ} (hn : 0 < n) : F.wid hd n * F.fitD ≤ F.famDeg :=
  Nat.mul_le_mul_right _ (F.wid_le hd hn)

/-- The tower member used for `n`, on its own numbers. -/
noncomputable def fitGraph (n : ℕ) : RegGraph := F.graphAt (F.fitLevel hd n)

@[simp] theorem order_fitGraph (n : ℕ) : (F.fitGraph hd n).order = F.fitN hd n :=
  F.order_graphAt _

@[simp] theorem deg_fitGraph (n : ℕ) : (F.fitGraph hd n).deg = F.fitD :=
  F.deg_graphAt _

theorem spectral_fitGraph (n : ℕ) : (F.fitGraph hd n).SpectralBound (2 / 5) :=
  spectral_graphAt F _

/-- Its rotation map, at the numeric type it lives on. -/
noncomputable def fitRot (n : ℕ) :
    Fin (F.fitN hd n) × Fin F.fitD → Fin (F.fitN hd n) × Fin F.fitD :=
  (F.data (F.fitLevel hd n)).1

theorem fitRot_involutive (n : ℕ) : Function.Involutive (F.fitRot hd n) :=
  (F.data (F.fitLevel hd n)).2

theorem base_fitRot (n : ℕ) :
    RegGraph.base F.fitD_pos (F.fitRot hd n) (F.fitRot_involutive hd n) = F.fitGraph hd n := rfl

/-! ### The fold, and the padding -/

/-- The tower member folded onto exactly `n` vertices. -/
noncomputable def mergedG {n : ℕ} (hn : 0 < n) : RegGraph :=
  RegGraph.mergedN hn F.fitD_pos (F.wid_pos hd hn) (F.fitN_le_wid_mul hd hn)
    (F.fitRot hd n) (F.fitRot_involutive hd n)

@[simp] theorem order_mergedG {n : ℕ} (hn : 0 < n) : (F.mergedG hd hn).order = n :=
  RegGraph.order_mergedN _ _ _ _ _ _

@[simp] theorem deg_mergedG {n : ℕ} (hn : 0 < n) :
    (F.mergedG hd hn).deg = F.wid hd n * F.fitD :=
  RegGraph.deg_mergedN _ _ _ _ _ _

theorem spectral_mergedG {n : ℕ} (hn : 0 < n) : (F.mergedG hd hn).SpectralBound (4 / 5) := by
  have hspec : (RegGraph.base F.fitD_pos (F.fitRot hd n)
      (F.fitRot_involutive hd n)).SpectralBound (2 / 5) := by
    rw [F.base_fitRot hd n]
    exact F.spectral_fitGraph hd n
  have hmerged := RegGraph.spectralBound_mergedN hn F.fitD_pos (F.wid_pos hd hn)
    (F.fitN_le_wid_mul hd hn) (F.wid_sub_one_mul_le hd n) (F.two_mul_le_fitN hd n)
    (F.fitRot hd n) (F.fitRot_involutive hd n) (by norm_num) hspec
  refine hmerged.mono (Real.sqrt_nonneg _) ?_
  rw [show (4 : ℝ) / 5 = Real.sqrt ((4 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  refine Real.sqrt_le_sqrt ?_
  have hm3 : (3 : ℝ) ≤ (F.wid hd n : ℝ) := by exact_mod_cast F.three_le_wid hd hn
  set m : ℝ := (F.wid hd n : ℝ)
  have h1 : (1 - (2 / 5 : ℝ) ^ 2) / (2 * m) ≤ (1 - (2 / 5 : ℝ) ^ 2) / (2 * 3) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have h2 : (1 : ℝ) / m ≤ 1 / 3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm3
  nlinarith [h1, h2]

/-- The fold padded up to the family's uniform degree. -/
noncomputable def paddedG {n : ℕ} (hn : 0 < n) : RegGraph :=
  (F.mergedG hd hn).padLoops (F.famDeg - F.wid hd n * F.fitD)

@[simp] theorem order_paddedG {n : ℕ} (hn : 0 < n) : (F.paddedG hd hn).order = n :=
  F.order_mergedG hd hn

@[simp] theorem deg_paddedG {n : ℕ} (hn : 0 < n) : (F.paddedG hd hn).deg = F.famDeg := by
  rw [paddedG, RegGraph.deg_padLoops, deg_mergedG]
  have := F.wid_mul_fitD_le hd hn
  omega

/-- The uniform contraction factor of the family. -/
noncomputable def famLam : ℝ := Real.sqrt (1 - 27 / (25 * F.widthBnd))

theorem three_le_widthBnd : 3 ≤ F.widthBnd := by
  have h1 : 1 ≤ F.deg ^ 4 := Nat.one_le_pow _ _ F.deg_pos
  rw [widthBnd]
  omega

theorem famLam_nonneg : 0 ≤ F.famLam := Real.sqrt_nonneg _

theorem famLam_lt_one : F.famLam < 1 := by
  have hW : (3 : ℝ) ≤ (F.widthBnd : ℝ) := by exact_mod_cast F.three_le_widthBnd
  have h0 : (0 : ℝ) ≤ 1 - 27 / (25 * F.widthBnd) := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have hlt : (1 : ℝ) - 27 / (25 * F.widthBnd) < 1 := by
    have : (0 : ℝ) < 27 / (25 * F.widthBnd) := by positivity
    linarith
  calc F.famLam = Real.sqrt (1 - 27 / (25 * F.widthBnd)) := rfl
    _ < Real.sqrt 1 := Real.sqrt_lt_sqrt h0 hlt
    _ = 1 := Real.sqrt_one

theorem spectral_paddedG {n : ℕ} (hn : 0 < n) : (F.paddedG hd hn).SpectralBound F.famLam := by
  have hpad := RegGraph.spectralBound_padLoops (G := F.mergedG hd hn)
    (F.famDeg - F.wid hd n * F.fitD) (F.spectral_mergedG hd hn)
  refine hpad.mono (Real.sqrt_nonneg _) ?_
  rw [famLam]
  refine Real.sqrt_le_sqrt ?_
  have hle : F.wid hd n * F.fitD ≤ F.famDeg := F.wid_mul_fitD_le hd hn
  have hF : (0 : ℝ) < (F.fitD : ℝ) := by exact_mod_cast F.fitD_pos
  have hW : (3 : ℝ) ≤ (F.widthBnd : ℝ) := by exact_mod_cast F.three_le_widthBnd
  have hm : (3 : ℝ) ≤ (F.wid hd n : ℝ) := by exact_mod_cast F.three_le_wid hd hn
  have hDeg : ((F.famDeg : ℝ)) = (F.widthBnd : ℝ) * (F.fitD : ℝ) := by
    rw [famDeg]; push_cast; ring
  have hk : (((F.famDeg - F.wid hd n * F.fitD : ℕ) : ℝ))
      = (F.famDeg : ℝ) - (F.wid hd n : ℝ) * (F.fitD : ℝ) := by
    rw [Nat.cast_sub hle]; push_cast; ring
  have hDpos : (0 : ℝ) < (F.widthBnd : ℝ) * (F.fitD : ℝ) := by positivity
  rw [F.deg_mergedG hd hn, hk]
  push_cast
  rw [hDeg, show ((F.wid hd n : ℝ) * (F.fitD : ℝ)
      + ((F.widthBnd : ℝ) * (F.fitD : ℝ) - (F.wid hd n : ℝ) * (F.fitD : ℝ)))
      = (F.widthBnd : ℝ) * (F.fitD : ℝ) from by ring, div_le_iff₀ hDpos, sub_mul, one_mul,
    show 27 / (25 * (F.widthBnd : ℝ)) * ((F.widthBnd : ℝ) * (F.fitD : ℝ))
      = 27 * (F.fitD : ℝ) / 25 from by field_simp]
  nlinarith [mul_le_mul_of_nonneg_right hm (le_of_lt hF)]

/-! ### Numbering the darts -/

theorem wid_mul_fitD_add {n : ℕ} (hn : 0 < n) :
    F.wid hd n * F.fitD + (F.famDeg - F.wid hd n * F.fitD) = F.famDeg := by
  have := F.wid_mul_fitD_le hd hn
  omega

/-- The darts of the padded fold, numbered: a slot and a dart of the member are
packed together, and the padding loops follow them. -/
noncomputable def famDartName {n : ℕ} (hn : 0 < n) :
    (F.paddedG hd hn).D ≃ Fin F.famDeg :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans
    (finSumFinEquiv.trans (finCongr (F.wid_mul_fitD_add hd hn)))

/-- The member of the family on `n` vertices, for `n` positive. -/
noncomputable def famGraph {n : ℕ} (hn : 0 < n) : RegGraph :=
  (F.paddedG hd hn).relabel (F.famDartName hd hn)

theorem famGraph_V {n : ℕ} (hn : 0 < n) : (F.famGraph hd hn).V = Fin n := rfl

theorem famGraph_D {n : ℕ} (hn : 0 < n) : (F.famGraph hd hn).D = Fin F.famDeg := rfl

theorem spectral_famGraph {n : ℕ} (hn : 0 < n) :
    (F.famGraph hd hn).SpectralBound F.famLam :=
  RegGraph.spectralBound_relabel _ _ (F.spectral_paddedG hd hn)

/-- The family's rotation map. -/
noncomputable def famRot (n : ℕ) : Fin n × Fin F.famDeg → Fin n × Fin F.famDeg :=
  if hn : 0 < n then (F.famGraph hd hn).rot else id

theorem famRot_involutive (n : ℕ) : Function.Involutive (F.famRot hd n) := by
  unfold famRot
  by_cases hn : 0 < n
  · erw [dite_eq_left hn]
    exact (F.famGraph hd hn).rot_involutive
  · erw [dite_eq_right hn]
    exact fun x => rfl

theorem famRot_eq {n : ℕ} (hn : 0 < n) : F.famRot hd n = (F.famGraph hd hn).rot := by
  erw [famRot, dite_eq_left hn]

theorem spectral_famRot (n : ℕ) :
    (RegGraph.ofRot F.famDeg F.famDeg_pos n (F.famRot hd n)
      (F.famRot_involutive hd n)).SpectralBound F.famLam := by
  rcases Nat.eq_zero_or_pos n with h | hn
  · subst h
    exact RegGraph.spectralBound_of_isEmpty (by exact Fin.isEmpty') _
  · have key : ∀ (r : Fin n × Fin F.famDeg → Fin n × Fin F.famDeg)
        (hr : Function.Involutive r), r = (F.famGraph hd hn).rot →
        (RegGraph.ofRot F.famDeg F.famDeg_pos n r hr).SpectralBound F.famLam := by
      rintro r hr rfl
      exact F.spectral_famGraph hd hn
    exact key _ _ (F.famRot_eq hd hn)

/-! ### The rotation map, in numbers -/

theorem val_famDartName_inl {n : ℕ} (hn : 0 < n) (s : Fin (F.wid hd n)) (c : Fin F.fitD) :
    ((F.famDartName hd hn) (Sum.inl (s, c) : (F.paddedG hd hn).D)).val
      = c.val + F.fitD * s.val := rfl

theorem val_famDartName_inr {n : ℕ} (hn : 0 < n)
    (j : Fin (F.famDeg - F.wid hd n * F.fitD)) :
    ((F.famDartName hd hn) (Sum.inr j : (F.paddedG hd hn).D)).val
      = F.wid hd n * F.fitD + j.val := rfl

theorem famDartName_symm_of_lt {n : ℕ} (hn : 0 < n) (i : Fin F.famDeg)
    (h : i.val < F.wid hd n * F.fitD) :
    (F.famDartName hd hn).symm i
      = Sum.inl (⟨i.val / F.fitD, by
          exact (Nat.div_lt_iff_lt_mul F.fitD_pos).mpr h⟩,
        ⟨i.val % F.fitD, Nat.mod_lt _ F.fitD_pos⟩) := by
  erw [Equiv.symm_apply_eq]
  refine Fin.ext ?_
  show i.val = i.val % F.fitD + F.fitD * (i.val / F.fitD)
  exact (Nat.mod_add_div i.val F.fitD).symm

theorem famDartName_symm_of_ge {n : ℕ} (hn : 0 < n) (i : Fin F.famDeg)
    (h : F.wid hd n * F.fitD ≤ i.val) :
    (F.famDartName hd hn).symm i
      = (Sum.inr ⟨i.val - F.wid hd n * F.fitD, by
          have := i.isLt
          omega⟩ : (F.paddedG hd hn).D) := by
  erw [Equiv.symm_apply_eq]
  refine Fin.ext ?_
  show i.val = F.wid hd n * F.fitD + (i.val - F.wid hd n * F.fitD)
  omega

/-- **The family's rotation map, on raw numbers.** A dart below `wid * fitD`
splits into a slot and a dart of the tower member; the vertex it lifts to is
`v + slot * n`, and the vertex it lands on is read modulo `n`, with the slot it
landed in becoming part of the new dart. Every other dart is a self-loop. -/
noncomputable def famRotVal (n : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.2 < F.wid hd n * F.fitD then
    if p.1 + p.2 / F.fitD * n < F.fitN hd n then
      let y := F.rotVal (F.fitLevel hd n) (p.1 + p.2 / F.fitD * n, p.2 % F.fitD)
      (y.1 % n, y.2 + F.fitD * (y.1 / n))
    else p
  else p

/-- **The numbers compute the family's rotation map.** -/
theorem famRotVal_eq {n : ℕ} (hn : 0 < n) (v : Fin n) (i : Fin F.famDeg) :
    F.famRotVal hd n (v.val, i.val)
      = ((F.famRot hd n (v, i)).1.val, (F.famRot hd n (v, i)).2.val) := by
  rw [F.famRot_eq hd hn]
  by_cases hi : i.val < F.wid hd n * F.fitD
  · obtain ⟨s, c, rfl⟩ : ∃ (s : Fin (F.wid hd n)) (c : Fin F.fitD),
        i = F.famDartName hd hn (Sum.inl (s, c)) := by
      refine ⟨⟨i.val / F.fitD, (Nat.div_lt_iff_lt_mul F.fitD_pos).mpr hi⟩,
        ⟨i.val % F.fitD, Nat.mod_lt _ F.fitD_pos⟩, ?_⟩
      erw [← Equiv.symm_apply_eq]
      exact F.famDartName_symm_of_lt hd hn i hi
    simp only [famGraph, RegGraph.relabel, val_famDartName_inl]
    erw [Equiv.symm_apply_apply]
    show F.famRotVal hd n (v.val, c.val + F.fitD * s.val)
        = (((F.mergedG hd hn).rot (v, (s, c))).1.val,
           ((F.famDartName hd hn)
              (Sum.inl ((F.mergedG hd hn).rot (v, (s, c))).2 : (F.paddedG hd hn).D)).val)
    by_cases hu : v.val + s.val * n < F.fitN hd n
    · have hlift : RegGraph.liftN (F.fitN hd n) n v s.val
          = some (⟨v.val + s.val * n, hu⟩ : Fin (F.fitN hd n)) := by
        rw [RegGraph.liftN, dite_eq_left hu]
      simp only [mergedG, RegGraph.mergedN, RegGraph.mergeRotN, hlift]
      have hlt : c.val + F.fitD * s.val < F.wid hd n * F.fitD := by
        have h1 : c.val < F.fitD := c.isLt
        have h2 : s.val + 1 ≤ F.wid hd n := s.isLt
        nlinarith
      have hs : (c.val + F.fitD * s.val) / F.fitD = s.val := by
        rw [Nat.add_mul_div_left _ _ F.fitD_pos, Nat.div_eq_of_lt c.isLt, Nat.zero_add]
      have hc : (c.val + F.fitD * s.val) % F.fitD = c.val := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt c.isLt]
      have hrot := F.rotVal_eq (F.fitLevel hd n)
        (⟨v.val + s.val * n, hu⟩ : Fin (F.size (F.fitLevel hd n))) c
      rw [famRotVal, ite_eq_left hlt]
      dsimp only
      rw [hs, hc, ite_eq_left hu, hrot]
      rfl
    · have hlift : RegGraph.liftN (F.fitN hd n) n v s.val = none := by
        rw [RegGraph.liftN, dite_eq_right hu]
      simp only [mergedG, RegGraph.mergedN, RegGraph.mergeRotN, hlift]
      have hlt : c.val + F.fitD * s.val < F.wid hd n * F.fitD := by
        have h1 : c.val < F.fitD := c.isLt
        have h2 : s.val + 1 ≤ F.wid hd n := s.isLt
        nlinarith
      have hs : (c.val + F.fitD * s.val) / F.fitD = s.val := by
        rw [Nat.add_mul_div_left _ _ F.fitD_pos, Nat.div_eq_of_lt c.isLt, Nat.zero_add]
      rw [famRotVal, ite_eq_left hlt]
      dsimp only
      rw [hs, ite_eq_right hu]
      rfl
  · obtain ⟨j, rfl⟩ : ∃ j : Fin (F.famDeg - F.wid hd n * F.fitD),
        i = F.famDartName hd hn (Sum.inr j : (F.paddedG hd hn).D) := by
      refine ⟨⟨i.val - F.wid hd n * F.fitD, by have := i.isLt; omega⟩, ?_⟩
      erw [← Equiv.symm_apply_eq]
      exact F.famDartName_symm_of_ge hd hn i (by omega)
    simp only [famGraph, RegGraph.relabel]
    erw [Equiv.symm_apply_apply]
    have hge : ¬ (F.wid hd n * F.fitD + j.val < F.wid hd n * F.fitD) := by omega
    show F.famRotVal hd n (v.val, F.wid hd n * F.fitD + j.val) = _
    rw [famRotVal, ite_eq_right hge]
    rfl

/-- **The expander family the numbered tower generates**: one member at every
size, of a constant degree, all contracting by the same factor, and with every
naming explicit. -/
noncomputable def toFamily : ExpanderFamily where
  degree := F.famDeg
  degree_pos := F.famDeg_pos
  rot := F.famRot hd
  rot_involutive := F.famRot_involutive hd
  lam := F.famLam
  lam_nonneg := F.famLam_nonneg
  lam_lt_one := F.famLam_lt_one
  spectral := F.spectral_famRot hd

end FinBase

/-! ### The family the algorithm uses -/

/-- A numbered base of degree above one, chosen once. -/
noncomputable def algBase : FinBase := Classical.choose exists_finBase

theorem one_lt_algBase_deg : 1 < algBase.deg := Classical.choose_spec exists_finBase

/-- **The explicit expander family**: the tower over that base. Unlike
`randExpander` it comes with rotation tables an algorithm can read. -/
noncomputable def algFamily : ExpanderFamily := algBase.toFamily one_lt_algBase_deg

end Complexity
