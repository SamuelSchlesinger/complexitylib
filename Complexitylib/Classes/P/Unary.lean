/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Encoding.Pairing
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Size
import Complexitylib.Classes.P.PairWithInput
import Complexitylib.Classes.P.Range
import Complexitylib.Classes.P.UnaryLength
import Complexitylib.Classes.P.Unary.Internal.Basic
import Complexitylib.Classes.P.Unary.Internal.Bounded
import Complexitylib.Classes.P.Unary.Internal.Log

/-!
# Polynomial-time numbers and tests

Rules for showing that a function to the natural numbers is polynomial-time
(`UnaryFn`: its value can be written in unary in polynomial time) and that a test
is (`FPPred`: a polynomial-time function outputs its verdict as one bit), stated
on numbers and propositions rather than on strings.

The rules cover
- the length of a polynomial-time output, constants, and the two halves of a
  pair, which is how a loop's body reads the loop's input and index;
- addition, multiplication, truncated subtraction, minimum and maximum, fixed
  powers and polynomials;
- comparisons, the Boolean connectives, and case distinction on a test;
- loops over the indices below a polynomial-time bound: a sum, a count, the
  first index at which a test passes, a maximum, and iterating an update whose
  values stay below a polynomial-time bound;
- division and remainder, capped powers, binary length and logarithms, which are
  derived from the loops.

A loop's body reads the loop's input `z` and the index `i` from the string
`pair z (1^i)`, as in `Complexitylib.Classes.P.Range`: `UnaryFn.lift` and
`FPPred.lift` read a rule on `z` there, and `UnaryFn.index` reads `i`. For
example, `z ↦ |z| / 3` is polynomial-time by
`(UnaryFn.length id_mem_FP).div (UnaryFn.const 3)`.

## Main results

- `UnaryFn.mem_FP`, `UnaryFn.of_eq`, `FPPred.of_iff` — moving between the rules
  and `FP`
- `UnaryFn.length`, `UnaryFn.const`, `UnaryFn.lift`, `UnaryFn.index`
- `UnaryFn.add`, `UnaryFn.mul`, `UnaryFn.sub`, `UnaryFn.min`, `UnaryFn.max`,
  `UnaryFn.pow`, `UnaryFn.polyEval`
- `FPPred.le`, `FPPred.lt`, `FPPred.eq`, `FPPred.and`, `FPPred.or`, `FPPred.not`
- `FPPred.ite_mem_FP`, `UnaryFn.ite` — case distinction
- `UnaryFn.sum`, `UnaryFn.count`, `UnaryFn.find`, `UnaryFn.bmax`,
  `UnaryFn.iterate` — loops
- `UnaryFn.div`, `UnaryFn.mod`, `UnaryFn.powMin`, `UnaryFn.pow_of_le`,
  `UnaryFn.size`, `UnaryFn.log`, `UnaryFn.clog`
-/

public section

namespace Complexity

variable {f g n a b c k : List Bool → ℕ} {p q : List Bool → Prop}

/-! ## Between numbers and strings -/

/-- A polynomial-time number is a polynomial-time function that writes it in
unary. -/
theorem unaryFn_iff : UnaryFn f ↔ (fun z => List.replicate (f z) true) ∈ FP := Iff.rfl

/-- Writing a polynomial-time number in unary is polynomial-time. -/
theorem UnaryFn.mem_FP (hf : UnaryFn f) : (fun z => List.replicate (f z) true) ∈ FP := hf

/-- A polynomial-time number can be written with any repeated bit. -/
theorem UnaryFn.replicate_mem_FP (hf : UnaryFn f) (bit : Bool) :
    (fun z => List.replicate (f z) bit) ∈ FP := by
  cases bit
  · exact mem_FP_of_eq (Cobham.mulLenFn_mem_FP hf (constFn_mem_FP [false])) fun _ => by simp
  · exact hf

/-- `UnaryFn` respects pointwise equality. -/
theorem UnaryFn.of_eq (hf : UnaryFn f) (h : ∀ z, f z = g z) : UnaryFn g :=
  mem_FP_of_eq hf fun z => by rw [h z]

/-- A polynomial-time number of a polynomial-time function of the input is
polynomial-time. -/
theorem UnaryFn.comp {h : List Bool → List Bool} (hf : UnaryFn f) (hh : h ∈ FP) :
    UnaryFn fun z => f (h z) :=
  mem_FP_comp hh hf

/-- A decided test is polynomial-time when its one-bit verdict is. -/
theorem FPPred.of_flag {v : List Bool → Bool} (hv : (fun z => [v z]) ∈ FP) :
    FPPred fun z => v z = true :=
  ⟨v, hv, fun _ => Iff.rfl⟩

/-- The one-bit verdict of a polynomial-time test is polynomial-time. -/
theorem FPPred.flag_mem_FP [DecidablePred p] (hp : FPPred p) :
    (fun z => [decide (p z)]) ∈ FP := by
  obtain ⟨v, hv, hpv⟩ := hp
  refine mem_FP_of_eq hv fun z => ?_
  by_cases h : p z
  · rw [decide_eq_true h, (hpv z).mp h]
  · rw [decide_eq_false h, Bool.eq_false_iff.mpr fun hv' => h ((hpv z).mpr hv')]

/-- `FPPred` respects pointwise equivalence. -/
theorem FPPred.of_iff (hp : FPPred p) (h : ∀ z, p z ↔ q z) : FPPred q := by
  obtain ⟨v, hv, hpv⟩ := hp
  exact ⟨v, hv, fun z => (h z).symm.trans (hpv z)⟩

/-- A polynomial-time test of a polynomial-time function of the input is
polynomial-time. -/
theorem FPPred.comp {h : List Bool → List Bool} (hp : FPPred p) (hh : h ∈ FP) :
    FPPred fun z => p (h z) := by
  obtain ⟨v, hv, hpv⟩ := hp
  exact ⟨fun z => v (h z), mem_FP_comp hh hv, fun z => hpv (h z)⟩

/-! ## Lengths, constants and pairs -/

/-- The length of a polynomial-time output is a polynomial-time number. -/
theorem UnaryFn.length {h : List Bool → List Bool} (hh : h ∈ FP) :
    UnaryFn fun z => (h z).length :=
  mem_FP_comp hh unaryLength_mem_FP

/-- A constant is a polynomial-time number. -/
theorem UnaryFn.const (m : ℕ) : UnaryFn fun _ => m :=
  constFn_mem_FP _

/-- A constant test is polynomial-time. -/
theorem FPPred.const (P : Prop) [Decidable P] : FPPred fun _ => P :=
  ⟨fun _ => decide P, constFn_mem_FP _, fun _ => decide_eq_true_iff.symm⟩

/-- A loop's body can read a polynomial-time number of the loop's input `z` off
`pair z (1^i)`. -/
theorem UnaryFn.lift (hf : UnaryFn f) : UnaryFn fun w => f (pairFst w) :=
  hf.comp Cobham.fstBlock_mem_FP

/-- A loop's body can run a polynomial-time test of the loop's input `z` on
`pair z (1^i)`. -/
theorem FPPred.lift (hp : FPPred p) : FPPred fun w => p (pairFst w) :=
  hp.comp Cobham.fstBlock_mem_FP

/-- A loop's body can read the index `i` off `pair z (1^i)`. -/
theorem UnaryFn.index : UnaryFn fun w => (pairSnd w).length :=
  UnaryFn.length Cobham.sndBlock_mem_FP

/-! ## Arithmetic -/

/-- **Addition** is polynomial-time. -/
theorem UnaryFn.add (hf : UnaryFn f) (hg : UnaryFn g) : UnaryFn fun z => f z + g z :=
  mem_FP_of_eq (Cobham.appendFn_mem_FP hf hg) fun _ => (List.replicate_add _ _ _).symm

/-- **Multiplication** is polynomial-time. -/
theorem UnaryFn.mul (hf : UnaryFn f) (hg : UnaryFn g) : UnaryFn fun z => f z * g z :=
  (UnaryFn.length (Cobham.mulLenFn_mem_FP hf hg)).of_eq fun z => by
    simp only [List.length_replicate]

/-- **Truncated subtraction** is polynomial-time. -/
theorem UnaryFn.sub (hf : UnaryFn f) (hg : UnaryFn g) : UnaryFn fun z => f z - g z :=
  mem_FP_of_eq (dropLenFn_mem_FP hg hf) fun z => by
    rw [List.length_replicate, List.drop_replicate]

/-- **The minimum** is polynomial-time. -/
theorem UnaryFn.min (hf : UnaryFn f) (hg : UnaryFn g) : UnaryFn fun z => min (f z) (g z) :=
  mem_FP_of_eq (Cobham.takeLenFn_mem_FP hf hg) fun z => by
    rw [List.length_replicate, List.take_replicate]

/-- **The maximum** is polynomial-time. -/
theorem UnaryFn.max (hf : UnaryFn f) (hg : UnaryFn g) : UnaryFn fun z => max (f z) (g z) :=
  (hf.add (hg.sub hf)).of_eq fun z => by omega

/-- **A fixed power** of a polynomial-time number is polynomial-time. -/
theorem UnaryFn.pow (hf : UnaryFn f) (d : ℕ) : UnaryFn fun z => f z ^ d := by
  induction d with
  | zero => exact (UnaryFn.const 1).of_eq fun _ => (pow_zero _).symm
  | succ d ih => exact (ih.mul hf).of_eq fun _ => (pow_succ _ _).symm

/-- **A polynomial** in a polynomial-time number is polynomial-time. In
particular `z ↦ p.eval |z|` is, by `UnaryFn.polyEval p (UnaryFn.length id_mem_FP)`. -/
theorem UnaryFn.polyEval (p : Polynomial ℕ) (hf : UnaryFn f) :
    UnaryFn fun z => p.eval (f z) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact (hp.add hq).of_eq fun _ => (Polynomial.eval_add ..).symm
  | monomial d a =>
    exact ((UnaryFn.const a).mul (hf.pow d)).of_eq fun _ => (Polynomial.eval_monomial ..).symm

/-! ## Comparisons and connectives -/

/-- **Comparison** is polynomial-time. -/
theorem FPPred.le (hf : UnaryFn f) (hg : UnaryFn g) : FPPred fun z => f z ≤ g z :=
  ⟨fun z => decide (f z ≤ g z),
    mem_FP_of_eq (lenLeFlagFn_mem_FP hg hf) fun z => by
      rw [lenLeFlag_eq_decide, List.length_replicate, List.length_replicate],
    fun _ => decide_eq_true_iff.symm⟩

/-- **Strict comparison** is polynomial-time. -/
theorem FPPred.lt (hf : UnaryFn f) (hg : UnaryFn g) : FPPred fun z => f z < g z :=
  (FPPred.le (hf.add (UnaryFn.const 1)) hg).of_iff fun _ => Nat.add_one_le_iff

/-- **Conjunction** of polynomial-time tests is polynomial-time. -/
theorem FPPred.and (hp : FPPred p) (hq : FPPred q) : FPPred fun z => p z ∧ q z := by
  obtain ⟨v, hv, hpv⟩ := hp
  obtain ⟨u, hu, hqu⟩ := hq
  refine ⟨fun z => v z && u z, mem_FP_of_eq (andBitFn_mem_FP hv hu) fun z => ?_,
    fun z => ?_⟩
  · rw [andBit_singleton]
  · dsimp only
    rw [hpv, hqu, Bool.and_eq_true]

/-- **Disjunction** of polynomial-time tests is polynomial-time. -/
theorem FPPred.or (hp : FPPred p) (hq : FPPred q) : FPPred fun z => p z ∨ q z := by
  obtain ⟨v, hv, hpv⟩ := hp
  obtain ⟨u, hu, hqu⟩ := hq
  refine ⟨fun z => v z || u z, mem_FP_of_eq (orBitFn_mem_FP hv hu) fun z => ?_,
    fun z => ?_⟩
  · rw [orBit_singleton]
  · dsimp only
    rw [hpv, hqu, Bool.or_eq_true]

/-- **Negation** of a polynomial-time test is polynomial-time. -/
theorem FPPred.not (hp : FPPred p) : FPPred fun z => ¬ p z := by
  obtain ⟨v, hv, hpv⟩ := hp
  refine ⟨fun z => !v z, mem_FP_of_eq (notBitFn_mem_FP hv) fun z => ?_, fun z => ?_⟩
  · rw [notBit_singleton]
  · dsimp only
    rw [hpv, Bool.not_eq_true']
    exact Bool.eq_false_iff.symm

/-- **Equality** of polynomial-time numbers is polynomial-time. -/
theorem FPPred.eq (hf : UnaryFn f) (hg : UnaryFn g) : FPPred fun z => f z = g z :=
  ((FPPred.le hf hg).and (FPPred.le hg hf)).of_iff fun _ => le_antisymm_iff.symm

/-! ## Case distinction -/

/-- **Case distinction** on a polynomial-time test, between polynomial-time
strings, is polynomial-time. -/
theorem FPPred.ite_mem_FP [DecidablePred p] {x y : List Bool → List Bool} (hp : FPPred p)
    (hx : x ∈ FP) (hy : y ∈ FP) : (fun z => if p z then x z else y z) ∈ FP := by
  obtain ⟨v, hv, hpv⟩ := hp
  refine mem_FP_of_eq (Cobham.selectHeadFn_mem_FP hv hx hy) fun z => ?_
  rw [selectHead_singleton]
  by_cases h : p z
  · rw [ite_eq_left ((hpv z).mp h), ite_eq_left h]
  · rw [ite_eq_right (mt (hpv z).mpr h), ite_eq_right h]

/-- **Case distinction** on a polynomial-time test, between polynomial-time
numbers, is polynomial-time. -/
theorem UnaryFn.ite [DecidablePred p] (hp : FPPred p) (hf : UnaryFn f) (hg : UnaryFn g) :
    UnaryFn fun z => if p z then f z else g z :=
  mem_FP_of_eq (FPPred.ite_mem_FP hp hf hg) fun z =>
    (apply_ite (fun m => List.replicate m true) (p z) (f z) (g z)).symm

/-! ## Loops over a range of indices -/

/-- **A sum over a range is polynomial-time.** If `n` and the body `f` are
polynomial-time, then so is the sum of `f (pair z (1^i))` over `i < n z`. -/
theorem UnaryFn.sum (hn : UnaryFn n) (hf : UnaryFn f) :
    UnaryFn fun z => ∑ i ∈ Finset.range (n z), f (pair z (List.replicate i true)) :=
  mem_FP_of_eq (mem_FP_comp (mem_FP_pairWithInput hn) (countOver_mem_FP hf)) fun z => by
    rw [Function.comp_apply, countOver_eq_replicate, length_countOver]
    simp only [List.length_replicate]

/-- **A count over a range is polynomial-time.** If `n` and the test `p` are
polynomial-time, then so is the number of `i < n z` such that `p` holds of
`pair z (1^i)`. -/
theorem UnaryFn.count [DecidablePred p] (hn : UnaryFn n) (hp : FPPred p) :
    UnaryFn fun z =>
      ((Finset.range (n z)).filter fun i => p (pair z (List.replicate i true))).card :=
  (hn.sum (UnaryFn.ite hp (UnaryFn.const 1) (UnaryFn.const 0))).of_eq fun _ =>
    (Finset.card_filter _ _).symm

/-- **A search over a range is polynomial-time.** If `n` and the test `p` are
polynomial-time, then so is the least `i < n z` such that `p` holds of
`pair z (1^i)`, or `n z` if there is none. -/
theorem UnaryFn.find [DecidablePred p] (hn : UnaryFn n) (hp : FPPred p) :
    UnaryFn fun z =>
      (List.range (n z)).findIdx fun i => decide (p (pair z (List.replicate i true))) := by
  -- On `pair z (1^j)`, the number of `k ≤ j` at which the test passes.
  have hinner : UnaryFn fun w => ((Finset.range ((pairSnd w).length + 1)).filter
      fun k => p (pair (pairFst w) (List.replicate k true))).card :=
    ((UnaryFn.index.add (UnaryFn.const 1)).count (hp.comp (Cobham.pairFn_mem_FP
      (mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP)
      Cobham.sndBlock_mem_FP))).of_eq fun w => by
        simp only [Function.comp_apply, pairFst_pair, pairSnd_pair]
  refine (hn.count (FPPred.eq hinner (UnaryFn.const 0))).of_eq fun z => ?_
  rw [findIdx_range_eq_card (fun i => p (pair z (List.replicate i true)))]
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]

/-- **A maximum over a range is polynomial-time.** If `n` and the body `f` are
polynomial-time, then so is the largest value of `f (pair z (1^i))` over
`i < n z`, or `0` if `n z = 0`. -/
theorem UnaryFn.bmax (hn : UnaryFn n) (hf : UnaryFn f) :
    UnaryFn fun z => (Finset.range (n z)).sup fun i => f (pair z (List.replicate i true)) :=
  (UnaryFn.length (mem_FP_comp (mem_FP_pairWithInput hn) (maxFn_mem_FP hf))).of_eq fun z => by
    rw [Function.comp_apply, maxFn_eq, maxOver_eq_sup]
    simp only [List.length_replicate]

/-- **A loop on a number is polynomial-time** while its values stay below a
polynomial-time bound. Starting from `a z`, the loop applies the update
`x ↦ s z x` `k z` times; the update reads `pair z (1^x)`, and every value along
the way is at most `B z`. -/
theorem UnaryFn.iterate {s : List Bool → ℕ → ℕ} {B : List Bool → ℕ}
    (hs : UnaryFn fun w => s (pairFst w) (pairSnd w).length) (ha : UnaryFn a)
    (hk : UnaryFn k) (hB : UnaryFn B) (hbound : ∀ z, ∀ j ≤ k z, (s z)^[j] (a z) ≤ B z) :
    UnaryFn fun z => (s z)^[k z] (a z) :=
  unaryFn_iterate_internal hs ha hk hB hbound

/-! ## Division, powers and logarithms -/

/-- **Division** is polynomial-time, with `f z / 0 = 0`. -/
theorem UnaryFn.div (hf : UnaryFn f) (hg : UnaryFn g) : UnaryFn fun z => f z / g z :=
  (hf.count ((FPPred.lt (UnaryFn.const 0) hg.lift).and
      (FPPred.le ((UnaryFn.index.add (UnaryFn.const 1)).mul hg.lift) hf.lift))).of_eq
    fun z => by
      simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
      exact (div_eq_card_filter_range _ _).symm

/-- **The remainder** is polynomial-time, with `f z % 0 = f z`. -/
theorem UnaryFn.mod (hf : UnaryFn f) (hg : UnaryFn g) : UnaryFn fun z => f z % g z :=
  (hf.sub (hg.mul (hf.div hg))).of_eq fun _ => (Nat.mod_def _ _).symm

/-- **A capped power is polynomial-time**: `min (b z ^ k z) (c z)`, when `b`, `k`
and `c` are polynomial-time. The cap keeps the value polynomially bounded. (Inside
the `UnaryFn` namespace a bare `min` means `UnaryFn.min`, hence `Min.min`.) -/
theorem UnaryFn.powMin (hb : UnaryFn b) (hk : UnaryFn k) (hc : UnaryFn c) :
    UnaryFn fun z => Min.min (b z ^ k z) (c z) := by
  have hs : UnaryFn fun w => Min.min (b (pairFst w) * (pairSnd w).length) (c (pairFst w)) :=
    (hb.lift.mul UnaryFn.index).min hc.lift
  refine (UnaryFn.iterate (s := fun z x => Min.min (b z * x) (c z)) hs
    ((UnaryFn.const 1).min hc) hk hc fun z j _ => ?_).of_eq fun z => ?_
  · rw [min_mul_iterate]
    exact min_le_right _ _
  · rw [min_mul_iterate]

/-- **A power below a polynomial-time bound is polynomial-time.** -/
theorem UnaryFn.pow_of_le (hb : UnaryFn b) (hk : UnaryFn k) (hc : UnaryFn c)
    (h : ∀ z, b z ^ k z ≤ c z) : UnaryFn fun z => b z ^ k z :=
  (hb.powMin hk hc).of_eq fun z => min_eq_left (h z)

/-- **The binary length** `Nat.size` of a polynomial-time number is
polynomial-time. -/
theorem UnaryFn.size (hf : UnaryFn f) : UnaryFn fun z => Nat.size (f z) :=
  (hf.count (FPPred.le ((UnaryFn.const 2).powMin UnaryFn.index
      (hf.lift.add (UnaryFn.const 1))) hf.lift)).of_eq fun z => by
    simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
    exact (size_eq_card_filter_range _).symm

/-- **The floor logarithm** `Nat.log` of polynomial-time numbers is
polynomial-time. -/
theorem UnaryFn.log (hb : UnaryFn b) (hf : UnaryFn f) :
    UnaryFn fun z => Nat.log (b z) (f z) :=
  (hf.count ((FPPred.lt (UnaryFn.const 1) hb.lift).and
      (FPPred.le (hb.lift.powMin (UnaryFn.index.add (UnaryFn.const 1))
        (hf.lift.add (UnaryFn.const 1))) hf.lift))).of_eq fun z => by
    simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
    exact (log_eq_card_filter_range _ _).symm

/-- **The ceiling logarithm** `Nat.clog` of polynomial-time numbers is
polynomial-time. -/
theorem UnaryFn.clog (hb : UnaryFn b) (hf : UnaryFn f) :
    UnaryFn fun z => Nat.clog (b z) (f z) :=
  (hf.count ((FPPred.lt (UnaryFn.const 1) hb.lift).and
      (FPPred.lt (hb.lift.powMin UnaryFn.index hf.lift) hf.lift))).of_eq fun z => by
    simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
    exact (clog_eq_card_filter_range _ _).symm

end Complexity
