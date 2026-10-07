/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Diagrams
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Internal.Syntactic

/-!
# One-way-liveness proof: Recognition

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Automata/Recognition.lean

Module and namespace names, imports, and formatting are adapted to complexitylib.
The machine definitions are shared through `Models.FiniteAutomaton.Defs`.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

/-- The scanned cells are the two fixed markers surrounding the ordinary word. -/
lemma scanned_list {Alpha : Type} (w : List Alpha) :
    List.ofFn (scanned w) = Symbol.left :: (w.map Symbol.letter ++ [Symbol.right]) := by
  rw [List.ofFn_succ]
  have hleft : scanned w (0 : Fin (w.length+2)) = .left := by simp [scanned]
  rw [hleft, List.ofFn_succ']
  congr 1
  have hre : scanned w (Fin.last (w.length)).succ = .right :=
    (scanned_eq_right_iff _ _).mpr rfl
  rw [hre, List.concat_eq_append]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn, List.getElem_map]
    simp [scanned, show i+1 < w.length+1 by omega]

namespace CellNetwork
variable {Alpha Q : Type} [Fintype Q] (M : Machine Alpha Q)

lemma fullDiagram_markers (finish : Q) (w : List Alpha) :
    fullDiagram M finish w =
      bodyDiagram M finish .left * (w.map (fun a => bodyDiagram M finish (.letter a))).prod *
        bodyDiagram M finish .right := by
  unfold fullDiagram
  have h : (List.ofFn fun i : Fin (w.length+2) => bodyDiagram M finish (scanned w i)) =
      (List.ofFn (scanned w)).map (bodyDiagram M finish) := by rw [List.map_ofFn]; rfl
  rw [h, scanned_list]
  simp only [List.map_cons, List.map_append, List.map_nil, List.map_map,
    List.prod_cons, List.prod_append, List.prod_nil, mul_one, Function.comp_def, mul_assoc]

/-- A diagram accepts when no compatible coloring separates its test ports. -/
noncomputable def recognitionTest (finish : Q) (a : Pairing (Port Q ⊕ Port Q)) : Prop :=
  ¬ ∃ l r, (bodyDiagram M finish .left * a * bodyDiagram M finish .right).Compatible
    (Sum.elim l r) ∧ Separated M finish l r

lemma recognitionTest_iff (finish : Q) (ht : M.transition finish .right = none)
    (w : List Alpha) :
    recognitionTest M finish (w.map (fun a => bodyDiagram M finish (.letter a))).prod ↔
      Relation.ReflTransGen (M.Step w) (outCell w.length false,M.initial)
        (outCell w.length true,finish) := by
  rw [recognitionTest, ← fullDiagram_markers]
  exact diagram_recognizes_reach M finish ht w

end CellNetwork

namespace Machine
variable {H Q : Type} [Fintype H] [Fintype Q] (M : Machine (BRel H) Q)

lemma liveness_rank_bound (hM : ∀ w, M.Accepts false w ↔ BRel.Live w)
    (x y : H) (hxy : x ≠ y) : rankLoss (Fintype.card H) ≤ 4 * (Fintype.card Q + 1)^2 := by
  classical
  let S := M.sinkCopy
  have ht : S.transition none .right = none := rfl
  have hr (w : List (BRel H)) :
      CellNetwork.recognitionTest S none
        (w.map (fun a => CellNetwork.bodyDiagram S none (.letter a))).prod ↔ BRel.Live w := by
    rw [CellNetwork.recognitionTest_iff S none ht]
    exact (M.sinkCopy_accepts w).trans (hM w)
  have hb := matching_recognition_degree
    (fun a => CellNetwork.bodyDiagram S none (.letter a))
    (CellNetwork.recognitionTest S none) hr x y hxy
  have hc : Fintype.card (CellNetwork.Port (Option Q)) = 4 * (Fintype.card Q + 1)^2 := by
    simp only [CellNetwork.Port, CellNetwork.Slot, Fintype.card_prod, Fintype.card_bool,
      Fintype.card_option]
    ring
  rwa [hc] at hb

end Machine

/-- The representation uses four ports per ordered state pair. One sink state
suffices under reflexive acceptance; a fresh initial row handles positive runs. -/
theorem deterministic_lower_bound (h : ℕ) (hh : 2 ≤ h) (positive : Bool) (s : ℕ)
    (D : DMachine (Alphabet h) s) (hD : D.Recognizes positive (oneWayLiveness h)) :
    2 ^ ((h - 2) / 31) ≤ 4 * (s + if positive then 2 else 1)^2 := by
  let x : Fin h := ⟨0, by omega⟩
  let y : Fin h := ⟨1, by omega⟩
  have hxy : x ≠ y := by intro he; have := congrArg Fin.val he; simp [x,y] at this
  cases positive with
  | false =>
    have hb := D.toMachine.liveness_rank_bound hD x y hxy
    simpa only [rankLoss, Fintype.card_fin, Bool.false_eq_true, ↓reduceIte] using hb
  | true =>
    have hd (w) : D.toMachine.positiveCopy.Accepts false w ↔ BRel.Live w :=
      (D.toMachine.positiveCopy_accepts w).trans (hD w)
    have hb := D.toMachine.positiveCopy.liveness_rank_bound hd x y hxy
    simpa only [rankLoss, Fintype.card_fin, Fintype.card_option, ↓reduceIte,
      Nat.add_assoc] using hb

end Complexity.FiniteAutomaton
