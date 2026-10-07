/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.Determinant

/-!
# Rational hitting lists: executable

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Executable.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.ExecutableGenerator
open Matrix DeterminantAlgorithm

/-- Dense, staged integer input tables. No quotient-field element is computed. -/
def inputTables (n N e : ℕ) (x : Fin 3 → ℕ) : Vector (Table (Generator.matrixDimension e)) (n+1) :=
  Vector.ofFn fun a => tabulate (Generator.integralLift n N e x a)

@[simp] lemma inputTables_denote (n N e : ℕ) (x : Fin 3 → ℕ) (a : Fin (n+1)) :
    denote ((inputTables n N e x).get a) = Generator.integralLift n N e x a := by
  simp [inputTables]

/-- Cramer's numerators are computed by the staged division-free algorithm. -/
def normalizedEntry {d : ℕ} (A B : Table d) (den : ℤ) (i j : Fin d) : ℚ :=
  Rat.divInt (determinant (tabulate ((denote A).updateCol i (fun r => denote B r j)))) den

lemma normalizedEntry_spec {d : ℕ} (A B : Table d) (hA : (denote A).det ≠ 0) (i j : Fin d) :
    normalizedEntry A B (determinant A) i j =
      (((denote A).map (Int.castRingHom ℚ))⁻¹*(denote B).map (Int.castRingHom ℚ)) i j := by
  rw [normalizedEntry,determinant_eq,denote_tabulate,determinant_eq]
  exact (EncodingBounds.normalized_entry_ratio (denote A) (denote B) hA i j).symm

/-- A finite vector of dense rational matrix tables. -/
abbrev RationalTable (n d : ℕ) := Vector (Vector (Vector ℚ d) d) n

/-- Read a dense rational table as a matrix substitution. -/
def tuple {n d : ℕ} (T : RationalTable n d) : Tuple n d :=
  fun a i j => ((T.get a).get i).get j

/-- Compute the normalized tuple entrywise using determinant ratios. -/
def normalized {n d : ℕ} (A : Vector (Table d) (n+1)) (den : ℤ) : RationalTable n d :=
  Vector.ofFn fun a => Vector.ofFn fun i => Vector.ofFn fun j =>
    normalizedEntry (A.get 0) (A.get a.succ) den i j

@[simp] lemma tuple_normalized {n d : ℕ} (A : Vector (Table d) (n+1)) (den : ℤ)
    (a : Fin n) (i j : Fin d) :
    tuple (normalized A den) a i j = normalizedEntry (A.get 0) (A.get a.succ) den i j := by
  simp [tuple,normalized]

/-- The only singularity test; all repeated algebra is materialized in dense tables. -/
def atPoint (n N e : ℕ) (x : Fin 3 → ℕ) : Option (Tuple n (Generator.matrixDimension e)) :=
  let A := inputTables n N e x
  let den := determinant (A.get 0)
  if den = 0 then none else some (tuple (normalized A den))

lemma U_det_eq_zero (n N e : ℕ) (x : Fin 3 → ℕ) :
    (Generator.integralLift n N e x 0).det = 0 ↔ (Generator.rationalLift n N e x 0).det = 0 := by
  have he := congrArg Matrix.det (Generator.U_cast n N e x 0)
  rw [Matrix.det_smul] at he
  simp only [Fintype.card_fin] at he
  change ((Generator.integralLift n N e x 0).map (fun z : ℤ => (z : ℚ))).det =
    (CyclotomicRing.dimension e : ℚ)^(Generator.matrixDimension e) * (Generator.rationalLift n N
      e x 0).det at he
  have hc : (CyclotomicRing.dimension e : ℚ)^(Generator.matrixDimension e) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (CyclotomicRing.dimension_pos e).ne')
  constructor
  · intro h
    have hv : (((Generator.integralLift n N e x 0).det : ℤ) : ℚ) = 0 := by simp [h]
    rw [Int.cast_det,he] at hv
    exact (mul_eq_zero.mp hv).resolve_left hc
  · intro h
    have hv : (((Generator.integralLift n N e x 0).det : ℤ) : ℚ) = 0 := by
      rw [Int.cast_det,he,h,mul_zero]
    exact_mod_cast hv

/-- Exact pointwise equality, including points rejected by the original determinant test. -/
theorem atPoint_spec (n N e : ℕ) (x : Fin 3 → ℕ) :
    atPoint n N e x = Generator.atPoint n N e x := by
  simp only [atPoint,determinant_eq,inputTables_denote,Generator.atPoint]
  by_cases hz : (Generator.rationalLift n N e x 0).det = 0
  · simp [hz,(U_det_eq_zero n N e x).mpr hz]
  · have hu := mt (U_det_eq_zero n N e x).mp hz
    simp only [hz,hu,ite_false,Option.some.injEq]
    funext a i j
    rw [tuple_normalized]
    have hh := normalizedEntry_spec ((inputTables n N e x).get 0)
      ((inputTables n N e x).get a.succ) (by simpa using hu) i j
    simp only [inputTables_denote,determinant_eq] at hh
    rw [hh,Generator.tupleAt_integer n N e x hz a]

/-- A computable generator preserving the list and its order. -/
def output (n N e H : ℕ) : Output n where
  dimension := Generator.matrixDimension e
  dimension_pos := Nat.mul_pos (CyclotomicRing.dimension_pos e) (CyclotomicRing.degree_pos e)
  tuples := (Generator.grid H).filterMap fun x => atPoint n N e (fun i => (x i).val+1)

theorem output_spec (n N e H : ℕ) : output n N e H = Generator.output n N e H := by
  simp only [output,Generator.output,atPoint_spec]

/-- The executable hitting list for the selected parameter values. -/
def list (n s : ℕ) : Output n :=
  output n (Parameters.truncation n s) (Parameters.exponent n s) (Parameters.gridSize n s)

theorem list_spec (n s : ℕ) : list n s = Generator.list n s := output_spec ..

/-- The complete binary encoding of the executable hitting list. -/
def encoded (n s : ℕ) : List Bool := encodeOutput (list n s)

theorem encoded_spec (n s : ℕ) : encoded n s = encodeOutput (Generator.list n s) := by
  rw [encoded,list_spec]

end RationalHitting.ExecutableGenerator


namespace RationalHitting.ExecutableGenerator

/-- The hitting property and output-size bounds for the computed list. -/


theorem exact_output (n s : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s) :
    (list n s).dimension ≤ 256*(n+s+1)^10 ∧
    (encodeOutput (list n s)).length ≤ PolynomialBounds.outputConstant*(n+s+1)^104 ∧
    Hits s (list n s) := by
  rw [list_spec]
  exact ⟨Generator.list_dimension_bound n s,Generator.list_output_bound n s hn,
    Generator.list_hits n s hs⟩

/-- A finite-state implementation with polynomial transition count. -/


def Implementation : Prop :=
  ∃ (m : ℕ) (G : Machine m) (C k : ℕ), 0 < C ∧ 0 < k ∧
    ∀ n s : ℕ, 1 ≤ n → 1 ≤ s → OutputsWithin G s (C*(n+s+1)^k) (list n s)

/-- The finite-state implementation and list bounds imply the main statement. -/
theorem main_of_implementation (hi : Implementation) : MainStatement := by
  obtain ⟨m,G,C,k,hC,hk,hG⟩ := hi
  refine ⟨m,G,C+256+PolynomialBounds.outputConstant,k+104,by omega,by omega,?_⟩
  intro n s hn hs
  have hm : 1 ≤ n+s+1 := by omega
  obtain ⟨hd,ho,hh⟩ := exact_output n s hn hs
  refine ⟨list n s,?_,?_,?_,hh⟩
  · exact hd.trans (Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right hm (by omega)))
  · exact ho.trans (Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right hm (by omega)))
  · obtain ⟨t,ht,a,hr,hhalt,hout⟩ := hG n s hn hs
    exact ⟨t,ht.trans (Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right hm (by omega))),a,hr,hhalt,hout⟩

end RationalHitting.ExecutableGenerator


/- Quantitative compilation measured in ordinary TM0 transitions. -/

end Complexity
