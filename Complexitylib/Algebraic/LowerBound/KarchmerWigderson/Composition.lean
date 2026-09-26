/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Basic
public import Complexitylib.Algebraic.BooleanCube
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Composition of Boolean functions and the KRW conjecture

The composition `f ⋄ g` of `f` on `m` bits with `g` on `n` bits applies `f`
to the values of `g` on `m` disjoint blocks of `n` bits. Here depth and size
are the minimum depth and leaf count of a De Morgan formula (`formulaDepth`,
`formulaSize`). Substituting a formula for `g` into a formula for `f` gives,
for all `f` and `g`, `depth (f ⋄ g) ≤ depth f + depth g`
(`formulaDepth_compose_le`) and `size (f ⋄ g) ≤ size f · size g`
(`formulaSize_compose_le`). Projections give `depth g ≤ depth (f ⋄ g)` when
`f` is not constant and `depth f ≤ depth (f ⋄ g)` when `g` is not constant.

The Karchmer–Raz–Wigderson conjecture asserts that for non-constant `f` and
`g` the upper bounds are tight up to lower-order terms. It is stated here in
its strong form, with a constant slack. `KRWDepthWith c` says that
`depth f + depth g ≤ depth (f ⋄ g) + c` for all `m`, `n` and all non-constant
`f` and `g` (`NonConstant`), and `KRWSizeWith c` says that
`size f · size g ≤ c · size (f ⋄ g)` for all such `f` and `g`. The
conjectures `KRWDepth` and `KRWSize` say that some constant `c` works. They
are open, and nothing here proves them; forms whose slack grows with `m` or
`n` are not formalized.

Both non-constancy hypotheses are needed. If `f` or `g` is constant then
`f ⋄ g` is constant, and dropping either hypothesis from `KRWDepthWith c` or
`KRWSizeWith c` gives a false statement for every `c`
(`not_forall_depth_of_constant_inner`, `not_forall_depth_of_constant_outer`,
`not_forall_size_of_constant_inner`, `not_forall_size_of_constant_outer`).
-/

@[expose] public section

namespace Algebraic
namespace KW

open scoped Classical

variable {m n N : Nat}

/-! ### Relabeling and substitution -/

namespace Formula

/-- Relabel the variables of a formula. -/
def mapIndex (φ : Fin n → Fin N) : Formula n → Formula N
  | lit i b => lit (φ i) b
  | const b => const b
  | and l r => and (l.mapIndex φ) (r.mapIndex φ)
  | or l r => or (l.mapIndex φ) (r.mapIndex φ)

@[simp] theorem eval_mapIndex (φ : Fin n → Fin N) :
    ∀ (F : Formula n) (x : Fin N → Bool), (F.mapIndex φ).eval x = F.eval (x ∘ φ)
  | lit _ _, _ => rfl
  | const _, _ => rfl
  | and l r, x => by simp [mapIndex, eval_mapIndex φ l, eval_mapIndex φ r]
  | or l r, x => by simp [mapIndex, eval_mapIndex φ l, eval_mapIndex φ r]

@[simp] theorem depth_mapIndex (φ : Fin n → Fin N) :
    ∀ F : Formula n, (F.mapIndex φ).depth = F.depth
  | lit _ _ => rfl
  | const _ => rfl
  | and l r => by simp [mapIndex, depth, depth_mapIndex φ l, depth_mapIndex φ r]
  | or l r => by simp [mapIndex, depth, depth_mapIndex φ l, depth_mapIndex φ r]

@[simp] theorem leaves_mapIndex (φ : Fin n → Fin N) :
    ∀ F : Formula n, (F.mapIndex φ).leaves = F.leaves
  | lit _ _ => rfl
  | const _ => rfl
  | and l r => by simp [mapIndex, leaves, leaves_mapIndex φ l, leaves_mapIndex φ r]
  | or l r => by simp [mapIndex, leaves, leaves_mapIndex φ l, leaves_mapIndex φ r]

/-- Substitute a formula, or its negation, for every literal. -/
def subst (σ : Fin N → Formula n) : Formula N → Formula n
  | lit i b => if b then σ i else (σ i).neg
  | const b => const b
  | and l r => and (l.subst σ) (r.subst σ)
  | or l r => or (l.subst σ) (r.subst σ)

@[simp] theorem eval_subst (σ : Fin N → Formula n) :
    ∀ (F : Formula N) (x : Fin n → Bool), (F.subst σ).eval x = F.eval fun i => (σ i).eval x
  | lit i b, x => by
    cases b
    · simp only [subst, Bool.false_eq_true, ↓reduceIte, eval_neg, eval_lit]
      cases (σ i).eval x <;> rfl
    · simp only [subst, ↓reduceIte, eval_lit]
      cases (σ i).eval x <;> rfl
  | const _, _ => rfl
  | and l r, x => by simp [subst, eval_subst σ l, eval_subst σ r]
  | or l r, x => by simp [subst, eval_subst σ l, eval_subst σ r]

theorem depth_subst_le (σ : Fin N → Formula n) {d : Nat} (hσ : ∀ i, (σ i).depth ≤ d) :
    ∀ F : Formula N, (F.subst σ).depth ≤ F.depth + d
  | lit i b => by
    cases b <;> simp [subst, depth, hσ i]
  | const _ => by simp [subst, depth]
  | and l r => by
    simp only [subst, depth]
    have := depth_subst_le σ hσ l
    have := depth_subst_le σ hσ r
    omega
  | or l r => by
    simp only [subst, depth]
    have := depth_subst_le σ hσ l
    have := depth_subst_le σ hσ r
    omega

theorem leaves_subst_le (σ : Fin N → Formula n) {L : Nat} (hL : 1 ≤ L)
    (hσ : ∀ i, (σ i).leaves ≤ L) :
    ∀ F : Formula N, (F.subst σ).leaves ≤ F.leaves * L
  | lit i b => by
    cases b <;> simp [subst, leaves, hσ i]
  | const _ => by simpa [subst, leaves] using hL
  | and l r => by
    simp only [subst, leaves, Nat.add_mul]
    have := leaves_subst_le σ hL hσ l
    have := leaves_subst_le σ hL hσ r
    omega
  | or l r => by
    simp only [subst, leaves, Nat.add_mul]
    have := leaves_subst_le σ hL hσ l
    have := leaves_subst_le σ hL hσ r
    omega

/-- Every Boolean function has a De Morgan formula, by Shannon expansion. -/
theorem exists_computes :
    ∀ (n : Nat) (f : Cslib.BooleanFunction n), ∃ F : Formula n, F.Computes f
  | 0, f => ⟨const (f Fin.elim0), fun x => by
      rw [Subsingleton.elim x Fin.elim0]
      rfl⟩
  | n + 1, f => by
    obtain ⟨F₁, h₁⟩ := exists_computes n fun x => f (Fin.snoc x true)
    obtain ⟨F₀, h₀⟩ := exists_computes n fun x => f (Fin.snoc x false)
    refine ⟨or (and (lit (Fin.last n) true) (F₁.mapIndex Fin.castSucc))
      (and (lit (Fin.last n) false) (F₀.mapIndex Fin.castSucc)), fun x => ?_⟩
    have hx : x = Fin.snoc (x ∘ Fin.castSucc) (x (Fin.last n)) := (Fin.snoc_init_self x).symm
    rw [eval_or, eval_and, eval_and, eval_lit, eval_lit, eval_mapIndex, eval_mapIndex,
      h₁ (x ∘ Fin.castSucc), h₀ (x ∘ Fin.castSucc)]
    conv_rhs => rw [hx]
    cases x (Fin.last n) <;> simp

end Formula

/-- An infimum of natural numbers in `ℕ∞` over a nonempty index type is attained. -/
theorem exists_iInf_natCast_eq {ι : Type*} [Nonempty ι] (u : ι → Nat) :
    ∃ i, (⨅ j, (u j : ℕ∞)) = u i := by
  obtain ⟨i, hi⟩ := Nat.sInf_mem (Set.range_nonempty u)
  refine ⟨i, le_antisymm (iInf_le _ i) (le_iInf fun j => ?_)⟩
  have : u i ≤ u j := hi ▸ Nat.sInf_le (Set.mem_range_self j)
  exact_mod_cast this

/-! ### Composition -/

/-- The position of coordinate `i` of block `j`. -/
def blockIndex (j : Fin m) (i : Fin n) : Fin (m * n) :=
  finProdFinEquiv (j, i)

theorem finProdFinEquiv_symm_blockIndex (j : Fin m) (i : Fin n) :
    finProdFinEquiv.symm (blockIndex j i) = (j, i) :=
  Equiv.symm_apply_apply _ _

/-- The composition `f ⋄ g`: `f` applied to `g` on `m` disjoint blocks of `n` bits. -/
def compose (f : Cslib.BooleanFunction m) (g : Cslib.BooleanFunction n) :
    Cslib.BooleanFunction (m * n) :=
  fun z => f fun j => g fun i => z (blockIndex j i)

namespace Formula

/-- Substitute a formula for `g` into a formula for `f`, block by block. -/
def compose (F : Formula m) (G : Formula n) : Formula (m * n) :=
  F.subst fun j => G.mapIndex (blockIndex j)

theorem eval_compose (F : Formula m) (G : Formula n) (z : Fin (m * n) → Bool) :
    (F.compose G).eval z = F.eval fun j => G.eval fun i => z (blockIndex j i) := by
  simp [Formula.compose, Function.comp_def]

theorem compose_computes {F : Formula m} {G : Formula n} {f : Cslib.BooleanFunction m}
    {g : Cslib.BooleanFunction n} (hF : F.Computes f) (hG : G.Computes g) :
    (F.compose G).Computes (KW.compose f g) := by
  intro z
  rw [eval_compose, KW.compose, hF]
  congr 1
  funext j
  exact hG _

theorem depth_compose_le (F : Formula m) (G : Formula n) :
    (F.compose G).depth ≤ F.depth + G.depth :=
  depth_subst_le _ (fun j => by rw [depth_mapIndex]) F

theorem leaves_compose_le (F : Formula m) (G : Formula n) :
    (F.compose G).leaves ≤ F.leaves * G.leaves :=
  leaves_subst_le _ (one_le_leaves G) (fun j => by rw [leaves_mapIndex]) F

end Formula

instance (f : Cslib.BooleanFunction n) : Nonempty {F : Formula n // F.Computes f} :=
  let ⟨F, hF⟩ := Formula.exists_computes n f
  ⟨⟨F, hF⟩⟩

/-- Every function has finite formula depth. -/
theorem formulaDepth_ne_top (f : Cslib.BooleanFunction n) : formulaDepth f ≠ ⊤ := by
  obtain ⟨F, hF⟩ := exists_iInf_natCast_eq fun F : {F : Formula n // F.Computes f} => F.1.depth
  rw [formulaDepth, hF]
  exact ENat.natCast_ne_top _

/-- Composition adds at most the depths. -/
theorem formulaDepth_compose_le (f : Cslib.BooleanFunction m) (g : Cslib.BooleanFunction n) :
    formulaDepth (compose f g) ≤ formulaDepth f + formulaDepth g := by
  unfold formulaDepth
  rw [ENat.iInf_add]
  refine le_iInf fun F => ?_
  rw [ENat.add_iInf]
  refine le_iInf fun G => ?_
  refine (iInf_le
    (fun H : {H : Formula (m * n) // H.Computes (compose f g)} => (H.1.depth : ℕ∞))
    ⟨F.1.compose G.1, Formula.compose_computes F.2 G.2⟩).trans ?_
  exact_mod_cast Formula.depth_compose_le F.1 G.1

/-- Composition multiplies at most the sizes. -/
theorem formulaSize_compose_le (f : Cslib.BooleanFunction m) (g : Cslib.BooleanFunction n) :
    formulaSize (compose f g) ≤ formulaSize f * formulaSize g := by
  obtain ⟨F, hF⟩ := exists_iInf_natCast_eq fun F : {F : Formula m // F.Computes f} => F.1.leaves
  obtain ⟨G, hG⟩ := exists_iInf_natCast_eq fun G : {G : Formula n // G.Computes g} => G.1.leaves
  have hF' : formulaSize f = F.1.leaves := hF
  have hG' : formulaSize g = G.1.leaves := hG
  rw [hF', hG']
  refine (formulaSize_le (Formula.compose_computes F.2 G.2)).trans ?_
  exact_mod_cast Formula.leaves_compose_le F.1 G.1

/-! ### Lower bounds by projection -/

/-- A non-constant function is sensitive at some point in some coordinate. -/
theorem exists_sensitive_of_ne {f : Cslib.BooleanFunction m} {a₀ a₁ : Fin m → Bool}
    (h : f a₀ ≠ f a₁) :
    ∃ j a, f (Function.update a j true) ≠ f (Function.update a j false) := by
  by_contra hne
  have hall : ∀ j a, f (Function.update a j true) = f (Function.update a j false) := by
    intro j a
    by_contra hja
    exact hne ⟨j, a, hja⟩
  have key := Algebraic.BooleanCube.update_induction a₀ a₁ (fun v => f v = f a₀) rfl (by
    intro v j c hv
    rw [← hv]
    have e : f (Function.update v j c) = f (Function.update v j (v j)) := by
      cases c <;> cases hvj : v j
      · rfl
      · exact (hall j v).symm
      · exact hall j v
      · rfl
    rw [e, Function.update_eq_self])
  exact h key.symm

/-- The depth of the inner function is at most the depth of the composition,
when the outer function is sensitive at some point. -/
theorem formulaDepth_inner_le_compose {f : Cslib.BooleanFunction m} {g : Cslib.BooleanFunction n}
    {j : Fin m} {a : Fin m → Bool}
    (hf : f (Function.update a j true) ≠ f (Function.update a j false))
    {x₀ x₁ : Fin n → Bool} (h₀ : g x₀ = false) (h₁ : g x₁ = true) :
    formulaDepth g ≤ formulaDepth (compose f g) := by
  refine le_iInf fun H => ?_
  let pick : Bool → (Fin n → Bool) := fun b => if b then x₁ else x₀
  have gpick : ∀ b, g (pick b) = b := by
    intro b
    cases b <;> simp [pick, h₀, h₁]
  let σ : Fin (m * n) → Formula n := fun k =>
    if (finProdFinEquiv.symm k).1 = j then Formula.lit (finProdFinEquiv.symm k).2 true
    else Formula.const (pick (a (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2)
  have hσ : ∀ k, (σ k).depth ≤ 0 := by
    intro k
    simp only [σ]
    split_ifs <;> rfl
  have heval : ∀ x, (H.1.subst σ).eval x = f (Function.update a j (g x)) := by
    intro x
    rw [Formula.eval_subst, H.2]
    unfold compose
    congr 1
    funext j'
    by_cases hj : j' = j
    · subst hj
      rw [Function.update_self]
      congr 1
      funext i
      simp only [σ, finProdFinEquiv_symm_blockIndex]
      simp
    · rw [Function.update_of_ne hj]
      have : (fun i => (σ (blockIndex j' i)).eval x) = pick (a j') := by
        funext i
        simp only [σ, finProdFinEquiv_symm_blockIndex]
        simp [hj]
      rw [this, gpick]
  have hdepth : ((H.1.subst σ).depth : ℕ∞) ≤ H.1.depth := by
    exact_mod_cast (Formula.depth_subst_le σ hσ H.1).trans (by omega)
  cases hft : f (Function.update a j true) <;> cases hff : f (Function.update a j false)
  · exact absurd (hft.trans hff.symm) hf
  · have hc : (H.1.subst σ).neg.Computes g := by
      intro x
      rw [Formula.eval_neg, heval]
      cases hx : g x
      · rw [hff]; rfl
      · rw [hft]; rfl
    refine (formulaDepth_le hc).trans ?_
    rw [Formula.depth_neg]
    exact hdepth
  · have hc : (H.1.subst σ).Computes g := by
      intro x
      rw [heval]
      cases hx : g x
      · exact hff
      · exact hft
    exact (formulaDepth_le hc).trans hdepth
  · exact absurd (hft.trans hff.symm) hf

/-- The depth of the outer function is at most the depth of the composition,
when the inner function is not constant. -/
theorem formulaDepth_outer_le_compose {f : Cslib.BooleanFunction m} {g : Cslib.BooleanFunction n}
    {x₀ x₁ : Fin n → Bool} (h₀ : g x₀ = false) (h₁ : g x₁ = true) :
    formulaDepth f ≤ formulaDepth (compose f g) := by
  refine le_iInf fun H => ?_
  let σ : Fin (m * n) → Formula m := fun k =>
    if x₁ (finProdFinEquiv.symm k).2 = x₀ (finProdFinEquiv.symm k).2 then
      Formula.const (x₀ (finProdFinEquiv.symm k).2)
    else if x₁ (finProdFinEquiv.symm k).2 then Formula.lit (finProdFinEquiv.symm k).1 true
    else Formula.lit (finProdFinEquiv.symm k).1 false
  have hσ : ∀ k, (σ k).depth ≤ 0 := by
    intro k
    simp only [σ]
    split_ifs <;> rfl
  have hblock : ∀ (b : Fin m → Bool) (j : Fin m),
      (fun i => (σ (blockIndex j i)).eval b) = if b j then x₁ else x₀ := by
    intro b j
    funext i
    simp only [σ, finProdFinEquiv_symm_blockIndex]
    cases hx1 : x₁ i <;> cases hx0 : x₀ i <;> cases hb : b j <;> simp [hx1, hx0, hb]
  have hc : (H.1.subst σ).Computes f := by
    intro b
    rw [Formula.eval_subst, H.2]
    unfold compose
    congr 1
    funext j
    rw [hblock]
    cases b j <;> simp [h₀, h₁]
  refine (formulaDepth_le hc).trans ?_
  exact_mod_cast (Formula.depth_subst_le σ hσ H.1).trans (by omega)

/-! ### Non-constant functions -/

/-- A Boolean function is non-constant when it takes two different values. -/
def NonConstant (f : Cslib.BooleanFunction n) : Prop :=
  ∃ x y, f x ≠ f y

/-- A non-constant function takes the value `false` somewhere and `true` somewhere. -/
theorem NonConstant.exists_eq_false_eq_true {f : Cslib.BooleanFunction n} (h : NonConstant f) :
    ∃ x₀ x₁, f x₀ = false ∧ f x₁ = true := by
  obtain ⟨x, y, hxy⟩ := h
  cases hx : f x <;> cases hy : f y
  · rw [hx, hy] at hxy
    exact absurd rfl hxy
  · exact ⟨x, y, hx, hy⟩
  · exact ⟨y, x, hy, hx⟩
  · rw [hx, hy] at hxy
    exact absurd rfl hxy

/-- A function that is not non-constant takes a single value. -/
theorem forall_eq_of_not_nonConstant {f : Cslib.BooleanFunction n} (h : ¬ NonConstant f) :
    ∀ x, f x = f fun _ => false := by
  intro x
  by_contra hx
  exact h ⟨x, fun _ => false, hx⟩

/-- A constant function has formula depth `0`. -/
theorem formulaDepth_eq_zero_of_forall_eq {f : Cslib.BooleanFunction n} {b : Bool}
    (h : ∀ x, f x = b) : formulaDepth f = 0 :=
  le_antisymm ((formulaDepth_le (F := Formula.const b) fun x => (h x).symm).trans le_rfl)
    zero_le

/-- Every formula has a leaf, so every formula size is at least `1`. -/
theorem one_le_formulaSize (f : Cslib.BooleanFunction n) : 1 ≤ formulaSize f :=
  le_iInf fun F => by exact_mod_cast Formula.one_le_leaves F.1

/-- A constant function has formula size `1`. -/
theorem formulaSize_eq_one_of_forall_eq {f : Cslib.BooleanFunction n} {b : Bool}
    (h : ∀ x, f x = b) : formulaSize f = 1 :=
  le_antisymm ((formulaSize_le (F := Formula.const b) fun x => (h x).symm).trans le_rfl)
    (one_le_formulaSize f)

/-- For non-constant `g`, the depth of `f` is at most the depth of `f ⋄ g`. -/
theorem formulaDepth_outer_le_compose_of_nonConstant {f : Cslib.BooleanFunction m}
    {g : Cslib.BooleanFunction n} (hg : NonConstant g) :
    formulaDepth f ≤ formulaDepth (compose f g) :=
  let ⟨_, _, h₀, h₁⟩ := hg.exists_eq_false_eq_true
  formulaDepth_outer_le_compose h₀ h₁

/-- For non-constant `f`, the depth of `g` is at most the depth of `f ⋄ g`. -/
theorem formulaDepth_inner_le_compose_of_nonConstant {f : Cslib.BooleanFunction m}
    {g : Cslib.BooleanFunction n} (hf : NonConstant f) :
    formulaDepth g ≤ formulaDepth (compose f g) := by
  obtain ⟨a₀, a₁, h⟩ := hf
  obtain ⟨j, a, hja⟩ := exists_sensitive_of_ne h
  by_cases hg : NonConstant g
  · obtain ⟨_, _, h₀, h₁⟩ := hg.exists_eq_false_eq_true
    exact formulaDepth_inner_le_compose hja h₀ h₁
  · rw [formulaDepth_eq_zero_of_forall_eq (forall_eq_of_not_nonConstant hg)]
    exact zero_le

/-! ### The conjecture -/

/-- The Karchmer–Raz–Wigderson conjecture, depth form, with additive slack `c`:
for all non-constant `f` on `m` bits and `g` on `n` bits,
`formulaDepth f + formulaDepth g ≤ formulaDepth (f ⋄ g) + c`. The slack `c` is
a single number, independent of `m`, `n`, `f` and `g`. The converse inequality
`formulaDepth (f ⋄ g) ≤ formulaDepth f + formulaDepth g` holds for all `f` and
`g` (`formulaDepth_compose_le`). -/
def KRWDepthWith (c : Nat) : Prop :=
  ∀ (m n : Nat) (f : Cslib.BooleanFunction m) (g : Cslib.BooleanFunction n),
    NonConstant f → NonConstant g →
      formulaDepth f + formulaDepth g ≤ formulaDepth (compose f g) + c

/-- The Karchmer–Raz–Wigderson conjecture, size form, with multiplicative slack
`c`: for all non-constant `f` on `m` bits and `g` on `n` bits,
`formulaSize f * formulaSize g ≤ c * formulaSize (f ⋄ g)`. The slack `c` is a
single number, independent of `m`, `n`, `f` and `g`. The converse inequality
`formulaSize (f ⋄ g) ≤ formulaSize f * formulaSize g` holds for all `f` and `g`
(`formulaSize_compose_le`). -/
def KRWSizeWith (c : Nat) : Prop :=
  ∀ (m n : Nat) (f : Cslib.BooleanFunction m) (g : Cslib.BooleanFunction n),
    NonConstant f → NonConstant g →
      formulaSize f * formulaSize g ≤ c * formulaSize (compose f g)

/-- **The KRW conjecture, depth form** (open): some constant additive slack
works, `∃ c, KRWDepthWith c`. -/
def KRWDepth : Prop :=
  ∃ c : Nat, KRWDepthWith c

/-- **The KRW conjecture, size form** (open): some constant multiplicative slack
works, `∃ c, KRWSizeWith c`. -/
def KRWSize : Prop :=
  ∃ c : Nat, KRWSizeWith c

/-- A larger additive slack gives a weaker statement. -/
theorem KRWDepthWith.mono {c c' : Nat} (h : KRWDepthWith c) (hc : c ≤ c') :
    KRWDepthWith c' := fun m n f g hf hg =>
  (h m n f g hf hg).trans (add_le_add le_rfl (by exact_mod_cast hc))

/-- A larger multiplicative slack gives a weaker statement. -/
theorem KRWSizeWith.mono {c c' : Nat} (h : KRWSizeWith c) (hc : c ≤ c') :
    KRWSizeWith c' := fun m n f g hf hg =>
  (h m n f g hf hg).trans (by gcongr)

/-! ### Both non-constancy hypotheses are needed

If `f` or `g` is constant then `f ⋄ g` is constant, of depth `0` and size `1`,
while the other function can have depth or size above any fixed slack. So
dropping either hypothesis from `KRWDepthWith c` or `KRWSizeWith c` gives a
false statement, whatever `c` is. The witness of large depth and size is the
conjunction of all `k` bits, whose formulas read every bit and so have at
least `k` leaves and depth at least `log₂ k`. -/

namespace Formula

/-- The coordinates read by some literal of a formula. -/
def vars : Formula n → Finset (Fin n)
  | lit i _ => {i}
  | const _ => ∅
  | and l r => l.vars ∪ r.vars
  | or l r => l.vars ∪ r.vars

theorem card_vars_le_leaves : ∀ F : Formula n, F.vars.card ≤ F.leaves
  | lit _ _ => by simp [vars, leaves]
  | const _ => by simp [vars, leaves]
  | and l r => by
    simp only [vars, leaves]
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add (card_vars_le_leaves l) (card_vars_le_leaves r))
  | or l r => by
    simp only [vars, leaves]
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add (card_vars_le_leaves l) (card_vars_le_leaves r))

/-- Changing a coordinate that a formula does not read leaves its value unchanged. -/
theorem eval_update_of_notMem_vars {i : Fin n} (b : Bool) (x : Fin n → Bool) :
    ∀ F : Formula n, i ∉ F.vars → F.eval (Function.update x i b) = F.eval x
  | lit j _, h => by
    have hji : j ≠ i := fun hji => h (by simp [vars, hji])
    simp [Function.update_of_ne hji]
  | const _, _ => rfl
  | and l r, h => by
    simp only [vars, Finset.mem_union, not_or] at h
    simp [eval_update_of_notMem_vars b x l h.1, eval_update_of_notMem_vars b x r h.2]
  | or l r, h => by
    simp only [vars, Finset.mem_union, not_or] at h
    simp [eval_update_of_notMem_vars b x l h.1, eval_update_of_notMem_vars b x r h.2]

/-- A formula reads every coordinate its function is sensitive to. -/
theorem mem_vars_of_computes {F : Formula n} {f : Cslib.BooleanFunction n} (hF : F.Computes f)
    {i : Fin n} {a : Fin n → Bool}
    (h : f (Function.update a i true) ≠ f (Function.update a i false)) : i ∈ F.vars := by
  by_contra hi
  apply h
  rw [← hF, ← hF, eval_update_of_notMem_vars _ _ _ hi, eval_update_of_notMem_vars _ _ _ hi]

theorem leaves_le_two_pow_depth : ∀ F : Formula n, F.leaves ≤ 2 ^ F.depth
  | lit _ _ => by simp [leaves, depth]
  | const _ => by simp [leaves, depth]
  | and l r => by
    simp only [leaves, depth, pow_succ]
    have hl := leaves_le_two_pow_depth l
    have hr := leaves_le_two_pow_depth r
    have hl' : 2 ^ l.depth ≤ 2 ^ max l.depth r.depth :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have hr' : 2 ^ r.depth ≤ 2 ^ max l.depth r.depth :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    omega
  | or l r => by
    simp only [leaves, depth, pow_succ]
    have hl := leaves_le_two_pow_depth l
    have hr := leaves_le_two_pow_depth r
    have hl' : 2 ^ l.depth ≤ 2 ^ max l.depth r.depth :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have hr' : 2 ^ r.depth ≤ 2 ^ max l.depth r.depth :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    omega

end Formula

/-- The conjunction of all `k` bits. -/
private def allTrue (k : Nat) : Cslib.BooleanFunction k :=
  fun x => decide (∀ i, x i = true)

private theorem allTrue_sensitive (k : Nat) (i : Fin k) :
    allTrue k (Function.update (fun _ => true) i true) ≠
      allTrue k (Function.update (fun _ => true) i false) := by
  simpa [allTrue] using ⟨i, by simp⟩

private theorem allTrue_nonConstant {k : Nat} (hk : 0 < k) : NonConstant (allTrue k) :=
  ⟨fun _ => true, fun _ => false, by simp [allTrue]; exact ⟨⟨0, hk⟩⟩⟩

private theorem le_leaves_of_computes_allTrue {k : Nat} {F : Formula k}
    (hF : F.Computes (allTrue k)) : k ≤ F.leaves := by
  have hsub : (Finset.univ : Finset (Fin k)) ⊆ F.vars := fun i _ =>
    Formula.mem_vars_of_computes hF (allTrue_sensitive k i)
  simpa using (Finset.card_le_card hsub).trans (Formula.card_vars_le_leaves F)

private theorem le_formulaSize_allTrue (k : Nat) : (k : ℕ∞) ≤ formulaSize (allTrue k) :=
  le_iInf fun F => by exact_mod_cast le_leaves_of_computes_allTrue F.2

private theorem le_formulaDepth_allTrue (c : Nat) :
    ((c + 1 : Nat) : ℕ∞) ≤ formulaDepth (allTrue (2 ^ (c + 1))) :=
  le_iInf fun F => by
    have h := (le_leaves_of_computes_allTrue F.2).trans (Formula.leaves_le_two_pow_depth F.1)
    exact_mod_cast (Nat.pow_le_pow_iff_right (by norm_num)).1 h

/-- Without non-constancy of `g`, the depth form fails for every slack `c`. -/
theorem not_forall_depth_of_constant_inner (c : Nat) :
    ¬ ∀ (m n : Nat) (f : Cslib.BooleanFunction m) (g : Cslib.BooleanFunction n),
      NonConstant f → formulaDepth f + formulaDepth g ≤ formulaDepth (compose f g) + c := by
  intro h
  have key := h _ 0 (allTrue (2 ^ (c + 1))) (fun _ => false)
    (allTrue_nonConstant (Nat.two_pow_pos _))
  rw [formulaDepth_eq_zero_of_forall_eq (b := false) (fun _ => rfl),
    formulaDepth_eq_zero_of_forall_eq (f := compose _ fun _ : Fin 0 → Bool => false)
      (b := allTrue _ fun _ => false) (fun _ => rfl), add_zero, zero_add] at key
  have := (le_formulaDepth_allTrue c).trans key
  norm_cast at this
  omega

/-- Without non-constancy of `f`, the depth form fails for every slack `c`. -/
theorem not_forall_depth_of_constant_outer (c : Nat) :
    ¬ ∀ (m n : Nat) (f : Cslib.BooleanFunction m) (g : Cslib.BooleanFunction n),
      NonConstant g → formulaDepth f + formulaDepth g ≤ formulaDepth (compose f g) + c := by
  intro h
  have key := h 0 _ (fun _ => false) (allTrue (2 ^ (c + 1)))
    (allTrue_nonConstant (Nat.two_pow_pos _))
  rw [formulaDepth_eq_zero_of_forall_eq (b := false) (fun _ => rfl),
    formulaDepth_eq_zero_of_forall_eq (f := compose (fun _ : Fin 0 → Bool => false) _)
      (b := false) (fun _ => rfl), zero_add, zero_add] at key
  have := (le_formulaDepth_allTrue c).trans key
  norm_cast at this
  omega

/-- Without non-constancy of `g`, the size form fails for every slack `c`. -/
theorem not_forall_size_of_constant_inner (c : Nat) :
    ¬ ∀ (m n : Nat) (f : Cslib.BooleanFunction m) (g : Cslib.BooleanFunction n),
      NonConstant f → formulaSize f * formulaSize g ≤ c * formulaSize (compose f g) := by
  intro h
  have key := h _ 0 (allTrue (c + 1)) (fun _ => false) (allTrue_nonConstant (Nat.succ_pos _))
  rw [formulaSize_eq_one_of_forall_eq (b := false) (fun _ => rfl),
    formulaSize_eq_one_of_forall_eq (f := compose _ fun _ : Fin 0 → Bool => false)
      (b := allTrue _ fun _ => false) (fun _ => rfl), mul_one, mul_one] at key
  have := (le_formulaSize_allTrue (c + 1)).trans key
  norm_cast at this
  omega

/-- Without non-constancy of `f`, the size form fails for every slack `c`. -/
theorem not_forall_size_of_constant_outer (c : Nat) :
    ¬ ∀ (m n : Nat) (f : Cslib.BooleanFunction m) (g : Cslib.BooleanFunction n),
      NonConstant g → formulaSize f * formulaSize g ≤ c * formulaSize (compose f g) := by
  intro h
  have key := h 0 _ (fun _ => false) (allTrue (c + 1)) (allTrue_nonConstant (Nat.succ_pos _))
  rw [formulaSize_eq_one_of_forall_eq (b := false) (fun _ => rfl),
    formulaSize_eq_one_of_forall_eq (f := compose (fun _ : Fin 0 → Bool => false) _)
      (b := false) (fun _ => rfl), one_mul, mul_one] at key
  have := (le_formulaSize_allTrue (c + 1)).trans key
  norm_cast at this
  omega

end KW
end Algebraic
