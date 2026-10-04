/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.FieldMul.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Restrict
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Restrict.Internal
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Ordering
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.TotallyRegular.Internal
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Asymptotics
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Proofs for multiplication in coordinates

Write `X(u) = ∑ j, u j • b j` for the element with coordinates `u`, and split the `2 n` inputs
into the coordinates `x` of the first factor (`xCoords`) and `y` of the second (`yCoords`).

* **Fixing one factor.** With the second factor fixed to `Y = X(y₀)`, the product changes by
  `shiftLeft b y₀ d = b.repr (X(d_x) * Y)` when the input changes by `d`
  (`fieldMul_sub_left`), and symmetrically with the first factor fixed (`fieldMul_sub_right`).
  So the kernel form of the restricted rank-cut bound (`card_pow_le_supportedKernel_of_trace`)
  applies on these slices.
* **Averaging the fixed factor.** For `P` within the first factor and rows `Q`, summing the
  kernel `supportedKernel (shiftLeft b y₀) P Q` over all `y₀` counts the pairs `(d, y₀)`. The
  vector `d = 0` lies in every kernel; for `d ≠ 0` the element `X(d_x)` is nonzero, so
  `Y ↦ X(d_x) * Y` is a bijection and exactly `|F| ^ (n - |Q|)` values `y₀` put `d` in the
  kernel (`card_filter_shiftLeft_eq`). The sum is at most `|F| ^ n + |F| ^ (|P| + n - |Q|)`
  (`sum_card_supportedKernel_le`), at most `2 |F| ^ n` when `|P| ≤ |Q|`; with two blocks, some
  `y₀` makes both kernels number at most `4` together (`exists_card_add_card_le_four`).
* **The cut bound** (`le_add_two_of_trace`). A split holding `a` inputs of the first factor and
  `n - a` outputs has two blocks with `|P| = |Q|`, so `|F| ^ n ≤ |F| ^ (|A| + |B|) · 4` and
  `n ≤ |A| + |B| + 2`.
* **One component** (`mem_component_of_trace`). The component of an output is closed, so both
  kernels are full on it (`apply_eq_zero_of_closed_of_trace`). Since `b j * ((b j)⁻¹ * b i) =
  b i`, a suitable fixed factor makes any block with a column and a row nonzero; so the
  component holds every input of either factor and every output.
* **Distinct terminals** (`terminal_injective`). The outputs are distinct wires (fix `y = 1`),
  and none is an input of the first factor (fix `y = 0`). So the number of first-factor inputs
  and outputs in a prefix grows by at most one per wire, and a prefix ending at one of them holds
  exactly `n`. Charging it to the component holding all `2 n` inputs gives
  `n - 2 ≤ (A + η) (s - 2 n)⁺ + 3 log₂ (2 n + 3 s) + C` (`sub_two_le_of_trace`), and the
  asymptotic `(2 + 1/A - ε) n` bound follows as for totally regular maps.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Internal

open SingleCut Filter

variable {σ : Signature} {n s : Nat}

/-! ## The two factors -/

section Coordinates

/-- The inputs holding the coordinates of the first factor. -/
def xCoords (n : Nat) : Finset (Fin (n + n)) :=
  Finset.univ.map (Fin.castAddEmb n)

/-- The inputs holding the coordinates of the second factor. -/
def yCoords (n : Nat) : Finset (Fin (n + n)) :=
  Finset.univ.map (Fin.natAddEmb n)

theorem castAdd_mem_xCoords (j : Fin n) : Fin.castAdd n j ∈ xCoords n := by
  simp [xCoords]

theorem natAdd_notMem_xCoords (j : Fin n) : Fin.natAdd n j ∉ xCoords n := by
  simp only [xCoords, Finset.mem_map, Finset.mem_univ, true_and, Fin.coe_castAddEmb, not_exists]
  intro j' h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

theorem natAdd_mem_yCoords (j : Fin n) : Fin.natAdd n j ∈ yCoords n := by
  simp [yCoords]

theorem castAdd_notMem_yCoords (j : Fin n) : Fin.castAdd n j ∉ yCoords n := by
  simp only [yCoords, Finset.mem_map, Finset.mem_univ, true_and, Fin.natAddEmb_apply,
    not_exists]
  intro j' h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

theorem card_xCoords : (xCoords n).card = n := by
  simp [xCoords]

theorem mem_xCoords {k : Fin (n + n)} : k ∈ xCoords n ↔ ∃ j, Fin.castAdd n j = k := by
  simp [xCoords]

/-- The first-factor inputs placed in `S`, as coordinates of all inputs. -/
theorem inputsIn_inter_xCoords (S : Finset (Wire (n + n) s)) :
    inputsIn S ∩ xCoords n =
      (Finset.univ.filter fun j : Fin n => Wire.input (Fin.castAdd n j) ∈ S).map
        (Fin.castAddEmb n) := by
  ext k
  simp only [Finset.mem_inter, mem_inputsIn, mem_xCoords, Finset.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and, Fin.coe_castAddEmb]
  constructor
  · rintro ⟨hk, j, rfl⟩
    exact ⟨j, hk, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨hj, j, rfl⟩

end Coordinates

/-! ## Fixing one factor -/

section Shift

variable {F K : Type*} [Field F] [Field K] [Algebra F K] (b : Module.Basis (Fin n) F K)

theorem fieldMul_eq (z : Fin (n + n) → F) :
    fieldMul b z = b.equivFun (b.equivFun.symm (fun j => z (Fin.castAdd n j)) *
      b.equivFun.symm (fun j => z (Fin.natAdd n j))) := by
  funext i
  simp [fieldMul, Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply]

theorem fieldMul_append (x y : Fin n → F) :
    fieldMul b (Fin.append x y) = b.equivFun (b.equivFun.symm x * b.equivFun.symm y) := by
  rw [fieldMul_eq]
  simp only [Fin.append_left, Fin.append_right]

/-- **Multiplication in coordinates multiplies.** -/
theorem fieldMul_append_equivFun (u v : K) :
    fieldMul b (Fin.append (b.equivFun u) (b.equivFun v)) = b.equivFun (u * v) := by
  rw [fieldMul_append]
  simp

/-- The change of the product when the input changes by `d` and the second factor has the
coordinates `y₀`. -/
noncomputable def shiftLeft (y₀ : Fin n → F) (d : Fin (n + n) → F) : Fin n → F :=
  b.equivFun (b.equivFun.symm (fun j => d (Fin.castAdd n j)) * b.equivFun.symm y₀)

/-- The change of the product when the input changes by `d` and the first factor has the
coordinates `x₀`. -/
noncomputable def shiftRight (x₀ : Fin n → F) (d : Fin (n + n) → F) : Fin n → F :=
  b.equivFun (b.equivFun.symm x₀ * b.equivFun.symm (fun j => d (Fin.natAdd n j)))

/-- With the second factor fixed, the product changes by `shiftLeft`. -/
theorem fieldMul_sub_left (y₀ : Fin n → F) (z z' : Fin (n + n) → F)
    (hz : ∀ k, k ∉ xCoords n → z k = Fin.append 0 y₀ k)
    (hz' : ∀ k, k ∉ xCoords n → z' k = Fin.append 0 y₀ k) :
    fieldMul b z' - fieldMul b z = shiftLeft b y₀ (z' - z) := by
  have hy : (fun j => z (Fin.natAdd n j)) = y₀ := funext fun j =>
    (hz _ (natAdd_notMem_xCoords j)).trans (Fin.append_right _ _ j)
  have hy' : (fun j => z' (Fin.natAdd n j)) = y₀ := funext fun j =>
    (hz' _ (natAdd_notMem_xCoords j)).trans (Fin.append_right _ _ j)
  rw [fieldMul_eq, fieldMul_eq, hy, hy', shiftLeft, ← map_sub, ← sub_mul, ← map_sub]
  rfl

/-- With the first factor fixed, the product changes by `shiftRight`. -/
theorem fieldMul_sub_right (x₀ : Fin n → F) (z z' : Fin (n + n) → F)
    (hz : ∀ k, k ∉ yCoords n → z k = Fin.append x₀ 0 k)
    (hz' : ∀ k, k ∉ yCoords n → z' k = Fin.append x₀ 0 k) :
    fieldMul b z' - fieldMul b z = shiftRight b x₀ (z' - z) := by
  have hx : (fun j => z (Fin.castAdd n j)) = x₀ := funext fun j =>
    (hz _ (castAdd_notMem_yCoords j)).trans (Fin.append_left _ _ j)
  have hx' : (fun j => z' (Fin.castAdd n j)) = x₀ := funext fun j =>
    (hz' _ (castAdd_notMem_yCoords j)).trans (Fin.append_left _ _ j)
  rw [fieldMul_eq, fieldMul_eq, hx, hx', shiftRight, ← map_sub, ← mul_sub, ← map_sub]
  rfl

theorem equivFun_symm_single (j : Fin n) : b.equivFun.symm (Pi.single j 1) = b j := by
  rw [Module.Basis.equivFun_symm_apply]
  simp [Pi.single_apply]

/-- A unit vector on a first-factor input shifts the product by `b j` times the second
factor. -/
theorem shiftLeft_single (y₀ : Fin n → F) (j : Fin n) :
    shiftLeft b y₀ (Pi.single (Fin.castAdd n j) 1) = b.equivFun (b j * b.equivFun.symm y₀) := by
  have : (fun j' => (Pi.single (Fin.castAdd n j) (1 : F) : Fin (n + n) → F) (Fin.castAdd n j')) =
      Pi.single j 1 := by
    funext j'
    simp [Pi.single_apply, Fin.castAdd_inj]
  rw [shiftLeft, this, equivFun_symm_single]

/-- A unit vector on a second-factor input shifts the product by the first factor times
`b j`. -/
theorem shiftRight_single (x₀ : Fin n → F) (j : Fin n) :
    shiftRight b x₀ (Pi.single (Fin.natAdd n j) 1) = b.equivFun (b.equivFun.symm x₀ * b j) := by
  have : (fun j' => (Pi.single (Fin.natAdd n j) (1 : F) : Fin (n + n) → F) (Fin.natAdd n j')) =
      Pi.single j 1 := by
    funext j'
    simp [Pi.single_apply]
  rw [shiftRight, this, equivFun_symm_single]

/-- **Every block entry can be made nonzero**: with the second factor `(b j)⁻¹ * b i`, the unit
vector on the first-factor input `j` shifts output `i` by one. -/
theorem shiftLeft_single_apply (j i : Fin n) :
    shiftLeft b (b.equivFun ((b j)⁻¹ * b i)) (Pi.single (Fin.castAdd n j) 1) i = 1 := by
  rw [shiftLeft_single, LinearEquiv.symm_apply_apply, mul_inv_cancel_left₀ (b.ne_zero j)]
  simp [Module.Basis.equivFun_self]

/-- With the first factor `b i * (b j)⁻¹`, the unit vector on the second-factor input `j`
shifts output `i` by one. -/
theorem shiftRight_single_apply (j i : Fin n) :
    shiftRight b (b.equivFun (b i * (b j)⁻¹)) (Pi.single (Fin.natAdd n j) 1) i = 1 := by
  rw [shiftRight_single, LinearEquiv.symm_apply_apply, inv_mul_cancel_right₀ (b.ne_zero j)]
  simp [Module.Basis.equivFun_self]

end Shift

/-! ## Averaging the fixed factor -/

section Average

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Field K] [Algebra F K]
  (b : Module.Basis (Fin n) F K)

/-- The vectors vanishing on `Q` number `|F| ^ |Qᶜ|`. -/
theorem card_filter_forall_eq_zero (Q : Finset (Fin n)) :
    (Finset.univ.filter fun u : Fin n → F => ∀ i ∈ Q, u i = 0).card =
      Fintype.card F ^ Qᶜ.card := by
  rw [← card_slice Qᶜ 0]
  congr 1
  ext u
  simp [mem_slice]

/-- For a vector `d` whose first-factor part is a nonzero element, exactly `|F| ^ |Qᶜ|` second
factors put it in the kernel on the rows `Q`. -/
theorem card_filter_shiftLeft_eq {d : Fin (n + n) → F}
    (hd : b.equivFun.symm (fun j => d (Fin.castAdd n j)) ≠ 0) (Q : Finset (Fin n)) :
    (Finset.univ.filter fun y₀ : Fin n → F => ∀ i ∈ Q, shiftLeft b y₀ d i = 0).card =
      Fintype.card F ^ Qᶜ.card := by
  rw [← card_filter_forall_eq_zero Q]
  let e : (Fin n → F) ≃ (Fin n → F) :=
    (b.equivFun.symm.toEquiv.trans (Equiv.mulLeft₀ _ hd)).trans b.equivFun.toEquiv
  refine Finset.card_equiv e fun y₀ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/-- **Averaging over the fixed factor.** For `P` within the first factor, the kernels on `P`
and `Q` number at most `|F| ^ n + |F| ^ |P| · |F| ^ |Qᶜ|` in total over all second factors. -/
theorem sum_card_supportedKernel_le (P : Finset (Fin (n + n))) (hP : P ⊆ xCoords n)
    (Q : Finset (Fin n)) :
    ∑ y₀ : Fin n → F, (supportedKernel (shiftLeft b y₀) P Q).card ≤
      Fintype.card F ^ n + Fintype.card F ^ P.card * Fintype.card F ^ Qᶜ.card := by
  set r : (Fin n → F) → (Fin (n + n) → F) → Prop := fun y₀ d => ∀ i ∈ Q, shiftLeft b y₀ d i = 0
  have hker : ∀ y₀, supportedKernel (shiftLeft b y₀) P Q =
      Finset.bipartiteAbove r (slice P 0) y₀ := by
    intro y₀
    ext d
    simp [supportedKernel, Finset.bipartiteAbove, mem_slice, r]
  simp_rw [hker]
  rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  have hterm : ∀ d ∈ slice P 0, (Finset.bipartiteBelow r Finset.univ d).card ≤
      (if d = 0 then Fintype.card F ^ n else 0) + Fintype.card F ^ Qᶜ.card := by
    intro d hd
    by_cases hd0 : d = 0
    · rw [ite_eq_left hd0]
      refine le_trans ?_ (Nat.le_add_right _ _)
      refine (Finset.card_filter_le _ _).trans ?_
      simp
    · rw [ite_eq_right hd0, zero_add]
      have hne : b.equivFun.symm (fun j => d (Fin.castAdd n j)) ≠ 0 := by
        intro h
        apply hd0
        funext k
        by_cases hk : k ∈ P
        · obtain ⟨j, rfl⟩ := mem_xCoords.mp (hP hk)
          have := congrFun (b.equivFun.symm.injective (h.trans (map_zero _).symm)) j
          simpa using this
        · exact mem_slice.mp hd k hk
      exact (card_filter_shiftLeft_eq b hne Q).le
  calc ∑ d ∈ slice P 0, (Finset.bipartiteBelow r Finset.univ d).card
      ≤ ∑ d ∈ slice P 0, ((if d = 0 then Fintype.card F ^ n else 0) +
          Fintype.card F ^ Qᶜ.card) := Finset.sum_le_sum hterm
    _ = (if (0 : Fin (n + n) → F) ∈ slice P 0 then Fintype.card F ^ n else 0) +
          (slice P 0).card * Fintype.card F ^ Qᶜ.card := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_const, smul_eq_mul]
    _ ≤ Fintype.card F ^ n + Fintype.card F ^ P.card * Fintype.card F ^ Qᶜ.card := by
        rw [card_slice]
        split_ifs <;> omega

/-- When `|P| ≤ |Q|`, the kernels number at most `2 |F| ^ n` in total. -/
theorem sum_card_supportedKernel_le_two_mul (P : Finset (Fin (n + n))) (hP : P ⊆ xCoords n)
    (Q : Finset (Fin n)) (hPQ : P.card ≤ Q.card) :
    ∑ y₀ : Fin n → F, (supportedKernel (shiftLeft b y₀) P Q).card ≤ 2 * Fintype.card F ^ n := by
  refine (sum_card_supportedKernel_le b P hP Q).trans ?_
  have hQ : Q.card ≤ n := by simpa using Finset.card_le_univ Q
  have hQc : Qᶜ.card = n - Q.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hpow : Fintype.card F ^ P.card * Fintype.card F ^ Qᶜ.card ≤ Fintype.card F ^ n := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right Fintype.card_pos (by omega)
  omega

/-- **Some fixed factor makes two kernels small.** If `|P₁| ≤ |Q₁|` and `|P₂| ≤ |Q₂|`, some
second factor makes the two kernels number at most `4` together. -/
theorem exists_card_add_card_le_four (P₁ P₂ : Finset (Fin (n + n))) (hP₁ : P₁ ⊆ xCoords n)
    (hP₂ : P₂ ⊆ xCoords n) (Q₁ Q₂ : Finset (Fin n)) (h₁ : P₁.card ≤ Q₁.card)
    (h₂ : P₂.card ≤ Q₂.card) :
    ∃ y₀ : Fin n → F, (supportedKernel (shiftLeft b y₀) P₁ Q₁).card +
      (supportedKernel (shiftLeft b y₀) P₂ Q₂).card ≤ 4 := by
  have hsum : ∑ y₀ : Fin n → F, ((supportedKernel (shiftLeft b y₀) P₁ Q₁).card +
      (supportedKernel (shiftLeft b y₀) P₂ Q₂).card) ≤ ∑ _y₀ : Fin n → F, 4 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, smul_eq_mul]
    have := sum_card_supportedKernel_le_two_mul b P₁ hP₁ Q₁ h₁
    have := sum_card_supportedKernel_le_two_mul b P₂ hP₂ Q₂ h₂
    omega
  obtain ⟨y₀, -, hy₀⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨y₀, hy₀⟩

end Average

/-! ## The cut bound -/

section Cut

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Field K] [Algebra F K]
  (b : Module.Basis (Fin n) F K)

/-- **The cut bound for multiplication.** If the wires `out` of a program carry `fieldMul b`,
every split holding `a` inputs of the first factor and `n - a` outputs is crossed by at least
`n - 2` signals. -/
theorem le_add_two_of_trace (p : Program σ (n + n) s) (I : Interpretation σ F)
    (out : Fin n → Wire (n + n) s) (hf : ∀ z i, p.trace I z (out i) = fieldMul b z i)
    (S : Finset (Wire (n + n) s))
    (hS : (Finset.univ.filter fun j : Fin n => Wire.input (Fin.castAdd n j) ∈ S).card +
      (outputsIn out S).card = n) :
    n ≤ (forward p S).card + (backward p S).card + 2 := by
  set P₁ := inputsIn S ∩ xCoords n with hP₁
  set P₂ := (inputsIn S)ᶜ ∩ xCoords n with hP₂
  have hcard₁ : P₁.card =
      (Finset.univ.filter fun j : Fin n => Wire.input (Fin.castAdd n j) ∈ S).card := by
    rw [hP₁, inputsIn_inter_xCoords, Finset.card_map]
  have hcard : P₁.card + P₂.card = n := by
    rw [hP₁, hP₂, card_inter_add_card_compl_inter, card_xCoords]
  have hY : (outputsIn out S)ᶜ.card = n - (outputsIn out S).card := by
    rw [Finset.card_compl, Fintype.card_fin]
  obtain ⟨y₀, hy₀⟩ := exists_card_add_card_le_four b P₁ P₂ Finset.inter_subset_right
    Finset.inter_subset_right (outputsIn out S)ᶜ (outputsIn out S) (by omega) (by omega)
  have hker := card_pow_le_supportedKernel_of_trace p I out hf S (xCoords n) (Fin.append 0 y₀)
    (shiftLeft b y₀) fun z z' hz hz' => fieldMul_sub_left b y₀ z z' hz hz'
  rw [card_xCoords] at hker
  set κ₁ := (supportedKernel (shiftLeft b y₀) P₁ (outputsIn out S)ᶜ).card
  set κ₂ := (supportedKernel (shiftLeft b y₀) P₂ (outputsIn out S)).card
  have hprod : κ₁ * κ₂ ≤ 4 := by
    have : κ₁ ≤ 4 := by omega
    have : κ₂ ≤ 4 := by omega
    interval_cases κ₁ <;> interval_cases κ₂ <;> omega
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hfour : 4 ≤ Fintype.card F ^ 2 := by nlinarith
  have hpow : Fintype.card F ^ n ≤
      Fintype.card F ^ ((forward p S).card + (backward p S).card + 2) := by
    rw [pow_add]
    exact hker.trans (Nat.mul_le_mul_left _ (hprod.trans hfour))
  exact (Nat.pow_le_pow_iff_right (by omega)).mp hpow

end Cut

/-! ## One component and distinct terminals -/

section Component

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Field K] [Algebra F K]
  (b : Module.Basis (Fin n) F K)

/-- **All inputs and outputs lie in one component.** If the wires `out` of a program carry
`fieldMul b` and `n ≥ 1`, the component of the first output contains every input and every
output. -/
theorem mem_component_of_trace (hn : 0 < n) (p : Program σ (n + n) s) (I : Interpretation σ F)
    (out : Fin n → Wire (n + n) s) (hf : ∀ z i, p.trace I z (out i) = fieldMul b z i) :
    (∀ k, Wire.input k ∈ component p (out ⟨0, hn⟩)) ∧ ∀ i, out i ∈ component p (out ⟨0, hn⟩) := by
  set i₀ : Fin n := ⟨0, hn⟩
  set W := component p (out i₀) with hW
  have hclosed := component_closed p (out i₀)
  have hfwd := forward_eq_empty_of_closed hclosed
  have hbwd := backward_eq_empty_of_closed hclosed
  have hi₀ : i₀ ∈ outputsIn out W := by
    simp [outputsIn, hW, mem_component_self]
  have hleft := fun y₀ => apply_eq_zero_of_closed_of_trace p I out hf W (xCoords n)
    (Fin.append 0 y₀) (shiftLeft b y₀) (fun z z' hz hz' => fieldMul_sub_left b y₀ z z' hz hz')
    hfwd hbwd
  have hright := fun x₀ => apply_eq_zero_of_closed_of_trace p I out hf W (yCoords n)
    (Fin.append x₀ 0) (shiftRight b x₀) (fun z z' hz hz' => fieldMul_sub_right b x₀ z z' hz hz')
    hfwd hbwd
  -- Every input of the first factor.
  have hx : ∀ j, Wire.input (Fin.castAdd n j) ∈ W := by
    intro j
    by_contra hj
    have h := (hleft (b.equivFun ((b j)⁻¹ * b i₀))).2 (Pi.single (Fin.castAdd n j) 1)
      (fun k hk => Pi.single_eq_of_ne (by
        rintro rfl
        exact hk (Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr fun h => hj (mem_inputsIn.mp h),
          castAdd_mem_xCoords j⟩)) _)
      i₀ hi₀
    rw [shiftLeft_single_apply] at h
    exact one_ne_zero h
  -- Every output.
  have hout : ∀ i, out i ∈ W := by
    intro i
    by_contra hi
    have h := (hleft (b.equivFun ((b i₀)⁻¹ * b i))).1 (Pi.single (Fin.castAdd n i₀) 1)
      (fun k hk => Pi.single_eq_of_ne (by
        rintro rfl
        exact hk (Finset.mem_inter.mpr ⟨mem_inputsIn.mpr (hx i₀), castAdd_mem_xCoords i₀⟩)) _)
      i (by simpa [outputsIn] using hi)
    rw [shiftLeft_single_apply] at h
    exact one_ne_zero h
  -- Every input of the second factor.
  have hy : ∀ j, Wire.input (Fin.natAdd n j) ∈ W := by
    intro j
    by_contra hj
    have h := (hright (b.equivFun (b i₀ * (b j)⁻¹))).2 (Pi.single (Fin.natAdd n j) 1)
      (fun k hk => Pi.single_eq_of_ne (by
        rintro rfl
        exact hk (Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr fun h => hj (mem_inputsIn.mp h),
          natAdd_mem_yCoords j⟩)) _)
      i₀ hi₀
    rw [shiftRight_single_apply] at h
    exact one_ne_zero h
  refine ⟨fun k => ?_, hout⟩
  induction k using Fin.addCases with
  | left j => exact hx j
  | right j => exact hy j

omit [Fintype F] [DecidableEq F] in
/-- A program carrying `fieldMul b` carries distinct outputs on distinct wires: with the second
factor `1`, the outputs are the coordinates of the first factor. -/
theorem out_injective (p : Program σ (n + n) s) (I : Interpretation σ F)
    (out : Fin n → Wire (n + n) s) (hf : ∀ z i, p.trace I z (out i) = fieldMul b z i) :
    Function.Injective out := by
  intro i i' h
  have := (hf (Fin.append (b.equivFun (b i)) (b.equivFun 1)) i).symm.trans
    ((congrArg _ h).trans (hf _ i'))
  rw [fieldMul_append_equivFun, mul_one, Module.Basis.equivFun_self,
    Module.Basis.equivFun_self] at this
  by_contra hne
  simp [hne] at this

omit [Fintype F] [DecidableEq F] in
/-- No output of a program carrying `fieldMul b` is an input of the first factor: with the
second factor `0`, every output is zero. -/
theorem out_ne_input (p : Program σ (n + n) s) (I : Interpretation σ F)
    (out : Fin n → Wire (n + n) s) (hf : ∀ z i, p.trace I z (out i) = fieldMul b z i)
    (i j : Fin n) : out i ≠ Wire.input (Fin.castAdd n j) := by
  intro h
  have := (hf (Fin.append (b.equivFun (b j)) (b.equivFun 0)) i).symm
  rw [h, fieldMul_append_equivFun, mul_zero, map_zero] at this
  simp at this

/-- The *terminals*: the inputs of the first factor, then the outputs. -/
def terminal (out : Fin n → Wire (n + n) s) : Fin n ⊕ Fin n → Wire (n + n) s :=
  Sum.elim (fun j => Wire.input (Fin.castAdd n j)) out

omit [Fintype F] [DecidableEq F] in
/-- Distinct terminals lie on distinct wires. -/
theorem terminal_injective (p : Program σ (n + n) s) (I : Interpretation σ F)
    (out : Fin n → Wire (n + n) s) (hf : ∀ z i, p.trace I z (out i) = fieldMul b z i) :
    Function.Injective (terminal out) := by
  rintro (j | i) (j' | i') h <;> simp only [terminal, Sum.elim_inl, Sum.elim_inr] at h
  · injection h with h
    rw [Fin.castAdd_inj.mp h]
  · exact absurd h.symm (out_ne_input b p I out hf i' j)
  · exact absurd h (out_ne_input b p I out hf i j')
  · rw [out_injective b p I out hf h]

/-- Counting terminals splits into first-factor inputs and outputs. -/
theorem card_filter_terminal (out : Fin n → Wire (n + n) s) (q : Wire (n + n) s → Prop)
    [DecidablePred q] :
    (Finset.univ.filter fun a => q (terminal out a)).card =
      (Finset.univ.filter fun j : Fin n => q (Wire.input (Fin.castAdd n j))).card +
        (Finset.univ.filter fun i => q (out i)).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
  rfl

end Component

/-! ## The finite bound -/

section Finite

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Field K] [Algebra F K]
  (b : Module.Basis (Fin n) F K)

theorem card_terminal_prefixBelow_succ_le (rank : Wire (n + n) s → Nat)
    (hrank : Function.Injective rank) (out : Fin n → Wire (n + n) s)
    (hterm : Function.Injective (terminal out)) (t : Nat) :
    (Finset.univ.filter fun a => rank (terminal out a) < t + 1).card ≤
      (Finset.univ.filter fun a => rank (terminal out a) < t).card + 1 := by
  have hsub : (Finset.univ.filter fun a => rank (terminal out a) < t + 1) ⊆
      (Finset.univ.filter fun a => rank (terminal out a) < t) ∪
        Finset.univ.filter fun a => rank (terminal out a) = t := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at ha ⊢
    omega
  have hone : (Finset.univ.filter fun a => rank (terminal out a) = t).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha a' ha' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
    exact hterm (hrank (ha.trans ha'.symm))
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left hone _))

/-- **The finite bound for multiplication.** A fan-in-two program over any signature whose
wires `out` carry `fieldMul b` has `n - 2 ≤ (A + η) (s - 2 n)⁺ + 3 log₂ (2 n + 3 s) + C`. -/
theorem sub_two_le_of_trace {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) (p : Program σ (n + n) s) (hp : p.FanInAtMost 2)
    (I : Interpretation σ F) (out : Fin n → Wire (n + n) s)
    (hf : ∀ z i, p.trace I z (out i) = fieldMul b z i) :
    (n : ℝ) - 2 ≤ (A + η) * max ((s : ℝ) - 2 * n) 0 + 3 * Real.logb 2 (2 * n + 3 * s) + C := by
  have hC := orderingBound_nonneg order
  have hlog : 0 ≤ Real.logb 2 (2 * (n : ℝ) + 3 * s) := by
    rcases Nat.eq_zero_or_pos (2 * n + 3 * s) with h | h
    · have : (2 * (n : ℝ) + 3 * s) = 0 := by exact_mod_cast h
      rw [this, Real.logb_zero]
    · exact Real.logb_nonneg one_lt_two (by exact_mod_cast h)
  have hmax0 : 0 ≤ (A + η) * max ((s : ℝ) - 2 * n) 0 := mul_nonneg hAη (le_max_right _ _)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero] at hmax0 hlog ⊢
    linarith
  -- All inputs and outputs lie in the component of the first output.
  obtain ⟨hin, houtW⟩ := mem_component_of_trace b hn p I out hf
  set W₀ := component p (out ⟨0, hn⟩) with hW₀
  have hterm := terminal_injective b p I out hf
  have htermW : ∀ a, terminal out a ∈ W₀ := by
    rintro (j | i)
    · exact hin _
    · exact houtW i
  -- The ranking and the prefix holding exactly `n` terminals.
  obtain ⟨rank, hrank, hlt, hbound⟩ := exists_rank hAη order p hp
  let τ : Nat → Nat := fun t => (Finset.univ.filter fun a => rank (terminal out a) < t).card
  have hτ0 : τ 0 = 0 := by simp [τ]
  have hτT : n ≤ τ (n + n + s) := by
    have hall : (Finset.univ.filter fun a => rank (terminal out a) < n + n + s) = Finset.univ :=
      Finset.filter_true_of_mem fun a _ => hlt _
    simp only [τ, hall, Finset.card_univ, Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨t, hτt, hτt1⟩ := exists_cross τ hτ0 (h := n) hn (n + n + s) hτT
  have hτeq : τ (t + 1) = n := by
    have := card_terminal_prefixBelow_succ_le rank hrank out hterm t
    simp only [τ] at this hτt hτt1 ⊢
    omega
  -- A terminal is ranked `t`.
  obtain ⟨a, hat⟩ : ∃ a, rank (terminal out a) = t := by
    by_contra hnone
    push Not at hnone
    have heq : (Finset.univ.filter fun a => rank (terminal out a) < t + 1) =
        Finset.univ.filter fun a => rank (terminal out a) < t := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := hnone a
      omega
    have : τ (t + 1) = τ t := by simp only [τ, heq]
    omega
  set w := terminal out a with hw
  set S := prefixBelow rank (t + 1) with hS
  have hprefix : S = prefixUpTo rank w := by
    ext v
    simp only [hS, prefixBelow, prefixUpTo, Finset.mem_filter, Finset.mem_univ, true_and, hat]
    omega
  have hcount : (Finset.univ.filter fun j : Fin n => Wire.input (Fin.castAdd n j) ∈ S).card +
      (outputsIn out S).card = n := by
    refine Eq.trans ?_ hτeq
    have := card_filter_terminal out (· ∈ S)
    simp only [hS, prefixBelow, Finset.mem_filter, Finset.mem_univ, true_and] at this
    simp only [τ, outputsIn, hS, prefixBelow, Finset.mem_filter, Finset.mem_univ, true_and]
    exact this.symm
  -- The cut bound and the ordering bound at the prefix.
  have hlower := le_add_two_of_trace b p I out hf S hcount
  have hcomp : component p w = W₀ := component_eq_of_mem (htermW a)
  have hinputs : (inputsIn W₀).card = n + n := by
    have : inputsIn W₀ = Finset.univ := by
      ext k
      simp [mem_inputsIn, hin k]
    rw [this, Finset.card_univ, Fintype.card_fin]
  have hupper := hbound w
  rw [← hprefix, hcomp, hinputs] at hupper
  have hgates : ((gatesIn W₀).card : ℝ) ≤ s := by
    exact_mod_cast (by simpa using Finset.card_le_univ (gatesIn W₀))
  have hmax : (A + η) * max (((gatesIn W₀).card : ℝ) - ((n + n : Nat) : ℝ)) 0 ≤
      (A + η) * max ((s : ℝ) - 2 * n) 0 := by
    refine mul_le_mul_of_nonneg_left (max_le_max ?_ le_rfl) hAη
    push_cast
    linarith
  have hlogeq : Real.logb 2 (((n + n : Nat) : ℝ) + 3 * s) = Real.logb 2 (2 * n + 3 * s) := by
    congr 1
    push_cast
    ring
  have hlowerR : (n : ℝ) - 2 ≤ (((forward p S).card + (backward p S).card : Nat) : ℝ) := by
    have : (n : ℝ) ≤ (((forward p S).card + (backward p S).card : Nat) : ℝ) + 2 := by
      exact_mod_cast hlower
    linarith
  rw [hlogeq] at hupper
  linarith

end Finite

/-! ## Asymptotics -/

universe u v w

/-- **The asymptotic bound for multiplication** with a general ordering coefficient. -/
theorem eventually_lt_size_of_orderingBound_fieldMul {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (F : Type u) [Field F] [Fintype F] (K : Type w) [Field K]
      [Algebra F K] (b : Module.Basis (Fin n) F K) (σ : Signature.{v})
      (I : Interpretation σ F) (c : Circuit σ (n + n) n),
        c.FanInAtMost 2 → c.Computes I (fieldMul b) → (2 + 1 / A - ε) * n < c.size := by
  set ε' := min ε (1 / A) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'A : ε' ≤ 1 / A := min_le_right _ _
  set η := A ^ 2 * ε' / 2 with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨C, hC⟩ := order η hηpos
  have hAη : 0 ≤ A + η := by linarith
  set B : ℝ := 8 + 3 / A with hB
  have hBpos : 0 < B := by positivity
  filter_upwards [eventually_mul_logb_add_lt 3 (3 * Real.logb 2 B + C + 2)
    (show 0 < A * ε' / 2 by positivity), eventually_ge_atTop 1] with n hlog hn1
  intro F _ _ K _ _ b σ I c hfan hc
  classical
  by_contra hs
  rw [not_lt] at hs
  have hs' : (c.size : ℝ) ≤ (2 + 1 / A - ε') * n :=
    hs.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have core := sub_two_le_of_trace b hAη hC c.program hfan I c.outputs
    (fun z i => congrFun (hc z) i)
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  -- The cycle-rank term.
  have hrest : 0 ≤ (1 / A - ε') * n := mul_nonneg (by linarith) (by positivity)
  have hmax : max ((c.size : ℝ) - 2 * n) 0 ≤ (1 / A - ε') * n :=
    max_le (by linarith) hrest
  have hcoef : (A + η) * (1 / A - ε') ≤ 1 - A * ε' / 2 := by
    have h₁ : (A + η) * (1 / A - ε') = 1 - A * ε' + η / A - η * ε' := by
      field_simp
      ring
    have h₂ : η / A = A * ε' / 2 := by
      rw [hη]
      field_simp
    have h₃ : 0 ≤ η * ε' := by positivity
    linarith
  have hprod : (A + η) * max ((c.size : ℝ) - 2 * n) 0 ≤ (1 - A * ε' / 2) * n := by
    calc (A + η) * max ((c.size : ℝ) - 2 * n) 0 ≤ (A + η) * ((1 / A - ε') * n) :=
          mul_le_mul_of_nonneg_left hmax hAη
      _ = (A + η) * (1 / A - ε') * n := by ring
      _ ≤ (1 - A * ε' / 2) * n := mul_le_mul_of_nonneg_right hcoef (by positivity)
  -- The logarithmic term.
  have hVle : 2 * (n : ℝ) + 3 * c.size ≤ B * n := by
    have h₁ : (2 + 1 / A - ε') * (n : ℝ) ≤ (2 + 1 / A) * n :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h₂ : B * (n : ℝ) = 2 * n + 3 * ((2 + 1 / A) * n) := by
      rw [hB]
      ring
    linarith
  have hVpos : (0 : ℝ) < 2 * n + 3 * c.size := by positivity
  have hlogV : Real.logb 2 (2 * (n : ℝ) + 3 * c.size) ≤ Real.logb 2 B + Real.logb 2 n := by
    calc Real.logb 2 (2 * (n : ℝ) + 3 * c.size) ≤ Real.logb 2 (B * n) :=
          (Real.logb_le_logb one_lt_two hVpos (by positivity)).mpr hVle
      _ = Real.logb 2 B + Real.logb 2 n := Real.logb_mul hBpos.ne' (by positivity)
  have hsplit : (1 - A * ε' / 2) * (n : ℝ) = n - A * ε' / 2 * n := by ring
  linarith

end Algebraic.Cutwidth.MultiOutput.Internal
