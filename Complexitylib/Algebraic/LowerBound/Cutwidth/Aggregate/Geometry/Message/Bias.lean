/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Message.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Rectangle
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Quarter bias of conjunction messages

A conjunction summary that tests two distinct selected primary inputs is true on
at most one quarter of the selected assignments. The proof overwrites the two
forced coordinates to inject four copies of the accepting assignments into all
assignments; repetitions and contradictory literals need no separate assumptions.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

/-- Fixing two distinct Boolean coordinates leaves at most a quarter of all assignments. -/
theorem four_mul_card_le_of_forces_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : (ι → Bool) → Prop) [DecidablePred P] (i j : ι) (hne : i ≠ j) (a b : Bool)
    (hP : ∀ x, P x → x i = a ∧ x j = b) :
    4 * Fintype.card {x // P x} ≤ 2 ^ Fintype.card ι := by
  let f : {x // P x} × (Bool × Bool) → (ι → Bool) := fun s =>
    Function.update (Function.update s.1.1 i s.2.1) j s.2.2
  have hf : Function.Injective f := by
    rintro ⟨x, u, v⟩ ⟨y, u', v'⟩ h
    have hu : u = u' := by
      simpa [f, hne] using congrFun h i
    have hv : v = v' := by
      simpa [f] using congrFun h j
    have hxy : x = y := by
      apply Subtype.ext
      funext k
      by_cases hki : k = i
      · subst k
        exact (hP x x.2).1.trans (hP y y.2).1.symm
      by_cases hkj : k = j
      · subst k
        exact (hP x x.2).2.trans (hP y y.2).2.symm
      simpa [f, hki, hkj] using congrFun h k
    exact Prod.ext hxy (Prod.ext hu hv)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_prod, Fintype.card_fun, Nat.mul_comm, Nat.mul_assoc] using hcard

/-- Two selected literal slots force the corresponding assignment coordinates. -/
theorem conjunctionSummary_forces_pair {r n g : ℕ} (polarity : Fin r → Bool)
    (wires : Fin r → Wire n g) (U : Finset (Fin n)) (s t : Fin r)
    (i j : U) (hs : wires s = .input i) (ht : wires t = .input j)
    (x : U → Bool)
    (hx : conjunctionSummary polarity wires U
      (Wire.elim (Cutwidth.glue U x (fun _ => false)) (fun _ => false)) = true) :
    x i = polarity s ∧ x j = polarity t := by
  have hall : ∀ slot, Capacity.selected U (wires slot) →
      Wire.elim (Cutwidth.glue U x (fun _ => false)) (fun _ => false)
        (wires slot) = polarity slot := by
    simpa [conjunctionSummary] using hx
  constructor
  · simpa [hs] using hall s (by simp [hs, Capacity.selected, i.2])
  · simpa [ht] using hall t (by simp [ht, Capacity.selected, j.2])

/-- A selected conjunction with two distinct primary variables has quarter bias. -/
theorem conjunctionSummary_quarter {r n g : ℕ} (polarity : Fin r → Bool)
    (wires : Fin r → Wire n g) (U : Finset (Fin n)) (s t : Fin r)
    (i j : U) (hne : i ≠ j) (hs : wires s = .input i) (ht : wires t = .input j) :
    4 * (Finset.univ.filter fun x : U → Bool => conjunctionSummary polarity wires U
      (Wire.elim (Cutwidth.glue U x (fun _ => false)) (fun _ => false)) = true).card ≤
      2 ^ U.card := by
  have h := four_mul_card_le_of_forces_pair
    (fun x : U → Bool => conjunctionSummary polarity wires U
      (Wire.elim (Cutwidth.glue U x (fun _ => false)) (fun _ => false)) = true)
    i j hne (polarity s) (polarity t)
    (fun x hx => conjunctionSummary_forces_pair polarity wires U s t i j hs ht x hx)
  simpa [Fintype.card_subtype] using h

/-- A conjunction line has two distinct primary variables selected by the cut. -/
def SelectedPair {n g : ℕ} (line : Line signature n g) (U : Finset (Fin n)) : Prop :=
  line.op.isConjunction = true ∧ ∃ i ∈ primaryInputs line, ∃ j ∈ primaryInputs line,
    i ≠ j ∧ i ∈ U ∧ j ∈ U

instance {n g : ℕ} (line : Line signature n g) (U : Finset (Fin n)) :
    Decidable (SelectedPair line U) := by
  unfold SelectedPair
  infer_instance

/-- Multiple-primary conjunctions supply two distinct designated primary variables. -/
theorem multiPrimary_iff_exists_pair {n g : ℕ} (line : Line signature n g) :
    multiPrimary line = true ↔ line.op.isConjunction = true ∧
      ∃ i ∈ primaryInputs line, ∃ j ∈ primaryInputs line, i ≠ j := by
  simp only [multiPrimary, Bool.and_eq_true, decide_eq_true_eq]
  change (line.op.isConjunction = true ∧ 1 < (primaryInputs line).card) ↔ _
  rw [Finset.one_lt_card]

/-- A selected pair belongs to an actual multiple-primary conjunction. -/
theorem SelectedPair.multiPrimary {n g : ℕ} {line : Line signature n g}
    {U : Finset (Fin n)} (h : SelectedPair line U) : multiPrimary line = true := by
  rcases h with ⟨hc, i, hi, j, hj, hij, _, _⟩
  exact (multiPrimary_iff_exists_pair line).mpr ⟨hc, i, hi, j, hj, hij⟩

/-- Selecting every input makes the pair condition exactly the geometric gate predicate. -/
theorem selectedPair_univ_iff {n g : ℕ} (line : Line signature n g) :
    SelectedPair line Finset.univ ↔ multiPrimary line = true := by
  simp [SelectedPair, multiPrimary_iff_exists_pair]

/-- The actual line message has quarter bias whenever the selected-pair witness holds. -/
theorem lineSummary_quarter_of_selectedPair {n g : ℕ} (line : Line signature n g)
    (U : Finset (Fin n)) (h : SelectedPair line U) :
    4 * (Finset.univ.filter fun x : U → Bool => lineSummary line U
      (Wire.elim (Cutwidth.glue U x (fun _ => false)) (fun _ => false)) = true).card ≤
      2 ^ U.card := by
  rcases line with ⟨op, wires⟩
  cases op with
  | affine r bias coefficient =>
    simp [SelectedPair, Op.isConjunction] at h
  | conjunction r polarity negated =>
    rcases h with ⟨_, i, hi, j, hj, hij, hiU, hjU⟩
    obtain ⟨s, hs⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨t, ht⟩ := (Finset.mem_filter.mp hj).2
    have hne : (⟨i, hiU⟩ : U) ≠ ⟨j, hjU⟩ := fun heq => hij (congrArg Subtype.val heq)
    convert conjunctionSummary_quarter polarity wires U s t
      ⟨i, hiU⟩ ⟨j, hjU⟩ hne hs ht using 1
    congr 2

/-- The extra output-message coordinate does not change a gate's quarter bias. -/
theorem outputKey_quarter_of_selectedPair {n g : ℕ} (p : Program signature n g)
    (U : Finset (Fin n)) (out : Wire n g) (gate : Fin g)
    (h : SelectedPair (p.lines gate) U) :
    4 * (Finset.univ.filter fun x : U → Bool =>
      outputKey p U out (Cutwidth.glue U x (fun _ => false)) gate.castSucc = true).card ≤
      Fintype.card (U → Bool) := by
  simpa [outputKey, key, Fintype.card_fun] using
    lineSummary_quarter_of_selectedPair (p.lines gate) U h

private theorem primaryInputs_map_castSucc {n g : ℕ} (line : Line signature n g) :
    primaryInputs (line.mapWires Wire.Renaming.castSucc) = primaryInputs line := by
  ext i
  simp only [primaryInputs, Finset.mem_filter, Finset.mem_univ, true_and,
    Line.mapWires_op, Line.mapWires_wires, Wire.Renaming.castSucc_apply]
  apply exists_congr
  intro slot
  cases line.wires slot <;> simp

private theorem multiPrimary_map_castSucc {n g : ℕ} (line : Line signature n g) :
    multiPrimary (line.mapWires Wire.Renaming.castSucc) = multiPrimary line := by
  simp [multiPrimary, primaryInputs_map_castSucc]

/-- The recursive geometric gate count equals the number of qualifying actual lines. -/
theorem multiCount_eq_card_filter {n g : ℕ} (p : Program signature n g) :
    multiCount p = (Finset.univ.filter fun gate => multiPrimary (p.lines gate) = true).card := by
  rw [Finset.card_filter]
  induction p with
  | empty => simp [multiCount]
  | gate p line ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [multiCount, Program.lines_gate_castSucc, Program.lines_gate_last,
      multiPrimary_map_castSucc]
    rw [ih]

end Algebraic.Aggregate.Geometry
