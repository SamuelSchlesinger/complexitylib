/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionNormalization
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs

/-!
# Unrestricted depth-three lower bound: sparse test codes

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/SparseTestCodes.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4 uDepth5 uDepth6 uDepth7 uDepth8 uDepth9 uDepth10 uDepth11
universe uDepth12 uDepth13 uDepth14 uDepth15 uDepth16 uDepth17 uDepth18

noncomputable section

open scoped Classical

namespace DepthThreeLowerBound

/-- A finite encoding of a sparse clause. -/
abbrev SparseClauseCode (V : Type uDepth1) (b : ℕ) := Fin b → Option (Literal V)
/-- A finite encoding of a sparse CNF test. -/
abbrev SparseTestCode (V : Type uDepth2) (b L : ℕ) := Fin L → Option (SparseClauseCode V b)

namespace SparseClauseCode

/-- Decode a sparse clause code to its set of literals. -/
def decode {V : Type uDepth3} [Fintype V] {b : ℕ} (c : SparseClauseCode V b) : Clause V :=
  Finset.univ.filter (fun l => ∃ i, c i = some l)

@[simp] theorem mem_decode {V : Type uDepth4} [Fintype V] {b : ℕ}
    (c : SparseClauseCode V b) (l : Literal V) :
    l ∈ c.decode ↔ ∃ i, c i = some l := by
  simp [decode]

@[simp] theorem decode_none {V : Type uDepth5} [Fintype V] (b : ℕ) :
    decode (fun _ : Fin b => (none : Option (Literal V))) = ∅ := by
  ext l
  simp

theorem exists_decode_of_card_le {V : Type uDepth6} [Fintype V]
    (C : Clause V) {b : ℕ} (hC : C.card ≤ b) :
    ∃ c : SparseClauseCode V b, c.decode = C := by
  have hsize : Fintype.card ↥C ≤ Fintype.card (Fin b) := by simpa using hC
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hsize
  let c : SparseClauseCode V b :=
    Function.extend e (fun l : ↥C => some l.val) (fun _ => none)
  refine ⟨c, ?_⟩
  ext l
  rw [mem_decode]
  constructor
  · rintro ⟨i, hi⟩
    change Function.extend e (fun l : ↥C => some l.val) (fun _ => none) i = some l at hi
    rw [Function.extend_def] at hi
    split_ifs at hi with hex
    · have heq : (Classical.choose hex).val = l := Option.some.inj hi
      exact heq ▸ (Classical.choose hex).property
  · intro hl
    refine ⟨e ⟨l, hl⟩, ?_⟩
    exact e.injective.extend_apply (fun l : ↥C => some l.val) (fun _ => none) ⟨l, hl⟩

theorem exists_decode_of_normalized {V : Type uDepth7} [Fintype V]
    (C : Clause V) {b : ℕ} (hn : C.Normalized) (hw : C.width ≤ b) :
    ∃ c : SparseClauseCode V b, c.decode = C :=
  exists_decode_of_card_le C (hn.card_eq_width.trans_le hw)

theorem card_eq {V : Type uDepth8} [Fintype V] (b : ℕ) :
    Fintype.card (SparseClauseCode V b) = (2 * Fintype.card V + 1) ^ b := by
  simp [SparseClauseCode, Literal, Nat.mul_comm]

end SparseClauseCode

namespace SparseTestCode

/-- Decode a sparse test code to its CNF. -/
def decode {V : Type uDepth9} [Fintype V] {b : ℕ} :
    {L : ℕ} → SparseTestCode V b L → CNF V
  | 0, _ => []
  | _ + 1, c =>
      match c 0 with
      | none => decode (fun i => c i.succ)
      | some d => d.decode :: decode (fun i => c i.succ)

/-- Evaluate the CNF decoded from a sparse test code. -/
def eval {V : Type uDepth10} [Fintype V] {b L : ℕ}
    (c : SparseTestCode V b L) (x : Cube V) : Bool := c.decode.eval x

@[simp] theorem decode_cons_none {V : Type uDepth11} [Fintype V] {b L : ℕ}
    (c : SparseTestCode V b L) : decode (Fin.cons none c) = c.decode := by
  simp [decode]

@[simp] theorem decode_cons_some {V : Type uDepth12} [Fintype V] {b L : ℕ}
    (d : SparseClauseCode V b) (c : SparseTestCode V b L) :
    decode (Fin.cons (some d) c) = d.decode :: c.decode := by
  simp [decode]

@[simp] theorem decode_none {V : Type uDepth13} [Fintype V] (b L : ℕ) :
    decode (fun _ : Fin L => (none : Option (SparseClauseCode V b))) = [] := by
  induction L with
  | zero => rfl
  | succ L ih => simpa [decode] using ih

@[simp] theorem eval_none {V : Type uDepth14} [Fintype V] (b L : ℕ) (x : Cube V) :
    eval (fun _ : Fin L => (none : Option (SparseClauseCode V b))) x = true := by
  simp [eval]

theorem eval_cons_empty {V : Type uDepth15} [Fintype V] {b L : ℕ}
    (c : SparseTestCode V b L) (x : Cube V) :
    eval (Fin.cons (some (fun _ : Fin b => (none : Option (Literal V)))) c) x = false := by
  simp [eval]

theorem exists_decode_of_normalized {V : Type uDepth16} [Fintype V]
    (H : CNF V) (b : ℕ) :
    ∀ L, H.Normalized → H.WidthAtMost b → H.length ≤ L →
      ∃ c : SparseTestCode V b L, c.decode = H := by
  induction H with
  | nil =>
      intro L _ _ _
      exact ⟨fun _ => none, decode_none b L⟩
  | cons C H ih =>
      intro L hn hw hlen
      cases L with
      | zero => simp at hlen
      | succ L =>
          have hnC : C.Normalized := hn C (by simp)
          have hwC : C.width ≤ b := hw C (by simp)
          obtain ⟨d, hd⟩ := SparseClauseCode.exists_decode_of_normalized C hnC hwC
          have hnH : CNF.Normalized H := fun D hD => hn D (by simp [hD])
          have hwH : CNF.WidthAtMost H b := fun D hD => hw D (by simp [hD])
          have hlenH : H.length ≤ L := Nat.le_of_succ_le_succ hlen
          obtain ⟨c, hc⟩ := ih L hnH hwH hlenH
          refine ⟨Fin.cons (some d) c, ?_⟩
          rw [decode_cons_some, hd, hc]

theorem exists_eval_eq {V : Type uDepth17} [Fintype V]
    (H : CNF V) {b L : ℕ} (hw : H.WidthAtMost b) (hlen : H.length ≤ L) :
    ∃ c : SparseTestCode V b L, ∀ x, c.eval x = H.eval x := by
  have hnormlen : H.normalize.length ≤ H.length := by
    unfold CNF.normalize
    exact List.length_filter_le _ _
  obtain ⟨c, hc⟩ := exists_decode_of_normalized H.normalize b L
    (CNF.normalize_normalized H) (CNF.normalize_widthAtMost hw) (hnormlen.trans hlen)
  refine ⟨c, fun x => ?_⟩
  change c.decode.eval x = H.eval x
  rw [hc, CNF.eval_normalize]

theorem card_eq {V : Type uDepth18} [Fintype V] (b L : ℕ) :
    Fintype.card (SparseTestCode V b L) = ((2 * Fintype.card V + 1) ^ b + 1) ^ L := by
  simp only [SparseTestCode, SparseClauseCode, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_option, Literal, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm]

end SparseTestCode

end DepthThreeLowerBound

end

end Complexity
