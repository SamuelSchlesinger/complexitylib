/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Halver.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Superconcentrator.Internal.Bound

/-!
# Proofs for ε-halvers

Let `N` be a comparator network on `n` wires with `s` comparators.

* **The wire graph.** Number the vertices by time: input terminals `0`, the ends of comparator
  `c` by `c + 1`, and output terminals by `s + 1` (`rank`). Every wire segment leaves
  `lastStop w t`, of rank at most `t`, and enters a vertex of rank `t + 1` on the same wire, so the
  graph is loopless. Two wire segments leaving the same vertex lie on the same wire, and if one
  entered a comparator before the other, the later one would leave a vertex of larger rank. So at
  most one wire segment leaves each vertex, at most one enters it, and at most one link meets it:
  the maximum degree is three. There are `2 n + 2 s` vertices and `n + 3 s` edges.
* **Token conservation** (`sub_le_card_cut`). On input `x ∈ {0, 1}ⁿ`, a wire segment carries
  the value of its wire, and the link of a comparator carries `1` when its `minWire` input is `1`
  and its `maxWire` input is `0`: the one that moves. For a vertex set `L`, the potential at time
  `t` is the number of wires carrying `1` whose last vertex before `t` lies in `L`. Comparator
  `t` changes it by minus the net flow out of `L` along its two incoming segments and its link,
  so summing over all edges, the net flow out of `L` is the number of ones at input terminals in
  `L` minus the number at output terminals in `L`. Every edge leaving `L` carries at most one
  token and every edge entering it at least none, so for any two inputs `x` and `x'` the cut of
  `L` has at least `net x - net x'` edges.
* **Connectivity** (`wireGraph_connected`). Every vertex is joined to the input terminal of its
  wire, and the link of a comparator joins its two wires. If a set of wires closed under the
  comparators held `0 < k ≤ n/2` wires, the indicator input of the set, and of its complement,
  would be fixed by the network, and an `ε`-halver with `ε < 1/2` would put at most `ε k` of its
  wires in each half.
* **The cut lemma** (`exists_le_card_cut`). In a linear order of the vertices take the lower set
  `L` with exactly `h = ⌊n/2⌋` input terminals, and let `τ` top output terminals lie in `L`. With
  ones on the inputs in `L`, at most `ε h` ones end in the bottom half, so `net ≥ h - τ - ε h`;
  with zeros on the inputs in `L`, at most `ε h` zeros end in the top half, so `net ≤ ε h - τ`.
  So the cut of `L` has at least `(1 - 2 ε) h` edges.
-/

@[expose] public section

open scoped Classical

namespace Algebraic.Cutwidth.Halver.Internal

open ComparatorNetwork Multigraph Relation Filter

variable {n s : ℕ} (N : ComparatorNetwork n s)

/-! ### Evaluation -/

section Evaluation

variable {α : Type*} [LinearOrder α]

theorem state_succ (x : Fin n → α) (c : Fin s) :
    N.state x (c + 1) = N.apply c (N.state x c) := by
  simp [ComparatorNetwork.state, c.isLt]

theorem apply_minWire (c : Fin s) (x : Fin n → α) :
    N.apply c x (N.minWire c) = min (x (N.minWire c)) (x (N.maxWire c)) := by
  simp [ComparatorNetwork.apply]

theorem apply_maxWire (c : Fin s) (x : Fin n → α) :
    N.apply c x (N.maxWire c) = max (x (N.minWire c)) (x (N.maxWire c)) := by
  simp [ComparatorNetwork.apply, Ne.symm (N.minWire_ne_maxWire c)]

theorem apply_of_ne (c : Fin s) (x : Fin n → α) {w : Fin n} (h₁ : N.minWire c ≠ w)
    (h₂ : N.maxWire c ≠ w) : N.apply c x w = x w := by
  simp [ComparatorNetwork.apply, Ne.symm h₁, Ne.symm h₂]

/-- A comparator whose two wires carry the same value changes nothing. -/
theorem apply_eq_self (c : Fin s) (x : Fin n → α) (h : x (N.minWire c) = x (N.maxWire c)) :
    N.apply c x = x := by
  funext w
  by_cases h₁ : w = N.minWire c
  · subst h₁
    rw [apply_minWire, h, min_self]
  · by_cases h₂ : w = N.maxWire c
    · subst h₂
      rw [apply_maxWire, h, max_self]
    · exact apply_of_ne N c x (Ne.symm h₁) (Ne.symm h₂)

/-- An input on which every comparator sees two equal values is fixed by the network. -/
theorem eval_eq_self (x : Fin n → α) (h : ∀ c, x (N.minWire c) = x (N.maxWire c)) :
    N.eval x = x := by
  have : ∀ t, N.state x t = x := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      by_cases ht : t < s
      · have := state_succ N x ⟨t, ht⟩
        simp only at this
        rw [this, ih, apply_eq_self N _ x (h _)]
      · simp [ComparatorNetwork.state, ht, ih]
  exact this s

end Evaluation

/-! ### Stops along a wire -/

/-- The comparators before time `t` acting on wire `w`. -/
def touchSet (w : Fin n) (t : ℕ) : Finset (Fin s) :=
  Finset.univ.filter fun c : Fin s => (c : ℕ) < t ∧ (N.minWire c = w ∨ N.maxWire c = w)

theorem mem_touchSet {w : Fin n} {t : ℕ} {c : Fin s} :
    c ∈ touchSet N w t ↔ (c : ℕ) < t ∧ (N.minWire c = w ∨ N.maxWire c = w) := by
  simp [touchSet]

theorem lastStop_eq (w : Fin n) (t : ℕ) :
    N.lastStop w t = if h : (touchSet N w t).Nonempty then
      .gate ((touchSet N w t).max' h) (decide (N.maxWire ((touchSet N w t).max' h) = w))
    else .input w := by
  unfold ComparatorNetwork.lastStop touchSet
  congr

/-- The time of a vertex: `0` for input terminals, `c + 1` for the ends of comparator `c`, and
`s + 1` for output terminals. -/
def rank : WireVertex n s → ℕ
  | .input _ => 0
  | .gate c _ => c + 1
  | .output _ => s + 1

/-- The wire of a vertex. -/
def wire : WireVertex n s → Fin n
  | .input w => w
  | .output w => w
  | .gate c b => N.sideWire c b

theorem sideWire_false (c : Fin s) : N.sideWire c false = N.minWire c := rfl

theorem sideWire_true (c : Fin s) : N.sideWire c true = N.maxWire c := rfl

/-- The wire on side `decide (maxWire c = w)` of a comparator acting on `w` is `w`. -/
theorem sideWire_decide {c : Fin s} {w : Fin n} (h : N.minWire c = w ∨ N.maxWire c = w) :
    N.sideWire c (decide (N.maxWire c = w)) = w := by
  by_cases hw : N.maxWire c = w
  · simp [hw, sideWire_true]
  · simp only [hw, decide_false, sideWire_false]
    exact h.resolve_right hw

/-- The two sides of a comparator lie on distinct wires. -/
theorem sideWire_injective (c : Fin s) : Function.Injective (N.sideWire c) := by
  intro b b' h
  cases b <;> cases b'
  · rfl
  · exact absurd h (N.minWire_ne_maxWire c)
  · exact absurd h.symm (N.minWire_ne_maxWire c)
  · rfl

theorem rank_lastStop_le (w : Fin n) (t : ℕ) : rank (N.lastStop w t) ≤ t := by
  rw [lastStop_eq]
  split_ifs with h
  · have := (mem_touchSet N).1 ((touchSet N w t).max'_mem h)
    simp only [rank]
    omega
  · simp [rank]

theorem le_rank_lastStop {w : Fin n} {t : ℕ} {c : Fin s} (hc : (c : ℕ) < t)
    (hw : N.minWire c = w ∨ N.maxWire c = w) : (c : ℕ) + 1 ≤ rank (N.lastStop w t) := by
  have hmem : c ∈ touchSet N w t := (mem_touchSet N).2 ⟨hc, hw⟩
  rw [lastStop_eq, dite_eq_left ⟨c, hmem⟩]
  have := (touchSet N w t).le_max' c hmem
  simp only [rank]
  exact Nat.succ_le_succ (Fin.le_def.1 this)

theorem wire_lastStop (w : Fin n) (t : ℕ) : wire N (N.lastStop w t) = w := by
  rw [lastStop_eq]
  split_ifs with h
  · exact sideWire_decide N ((mem_touchSet N).1 ((touchSet N w t).max'_mem h)).2
  · rfl

theorem lastStop_zero (w : Fin n) : N.lastStop w 0 = .input w := by
  rw [lastStop_eq, dite_eq_right]
  rintro ⟨c, hc⟩
  exact absurd ((mem_touchSet N).1 hc).1 (Nat.not_lt_zero _)

theorem lastStop_succ_of_touch {w : Fin n} (c : Fin s) (hw : N.minWire c = w ∨ N.maxWire c = w) :
    N.lastStop w (c + 1) = .gate c (decide (N.maxWire c = w)) := by
  have hmem : c ∈ touchSet N w (c + 1) := (mem_touchSet N).2 ⟨Nat.lt_succ_self _, hw⟩
  have hmax : (touchSet N w (c + 1)).max' ⟨c, hmem⟩ = c := by
    refine le_antisymm ((touchSet N w (c + 1)).max'_le _ _ fun y hy => ?_)
      ((touchSet N w (c + 1)).le_max' c hmem)
    have := ((mem_touchSet N).1 hy).1
    exact Fin.le_def.2 (by omega)
  rw [lastStop_eq, dite_eq_left ⟨c, hmem⟩, hmax]

theorem lastStop_succ_of_not_touch {w : Fin n} (c : Fin s) (h₁ : N.minWire c ≠ w)
    (h₂ : N.maxWire c ≠ w) : N.lastStop w (c + 1) = N.lastStop w c := by
  have : touchSet N w (c + 1) = touchSet N w c := by
    ext y
    simp only [mem_touchSet]
    constructor
    · rintro ⟨hy, hyw⟩
      refine ⟨lt_of_le_of_ne (Nat.lt_succ_iff.1 hy) fun hyc => ?_, hyw⟩
      have : y = c := Fin.ext hyc
      subst this
      exact hyw.elim h₁ h₂
    · rintro ⟨hy, hyw⟩
      exact ⟨by omega, hyw⟩
  rw [lastStop_eq, lastStop_eq, this]

/-! ### The wire graph -/

theorem wireGraph_fst_last (w : Fin n) : N.wireGraph.fst (.last w) = N.lastStop w s := rfl

theorem wireGraph_fst_into (c : Fin s) (b : Bool) :
    N.wireGraph.fst (.into c b) = N.lastStop (N.sideWire c b) c := rfl

theorem wireGraph_fst_link (c : Fin s) : N.wireGraph.fst (.link c) = .gate c false := rfl

theorem wireGraph_snd_last (w : Fin n) : N.wireGraph.snd (.last w) = .output w := rfl

theorem wireGraph_snd_into (c : Fin s) (b : Bool) :
    N.wireGraph.snd (.into c b) = .gate c b := rfl

theorem wireGraph_snd_link (c : Fin s) : N.wireGraph.snd (.link c) = .gate c true := rfl

/-- The wire graph has no loops. -/
theorem wireGraph_loopless : N.wireGraph.Loopless := by
  intro e
  cases e with
  | last w =>
    intro h
    have := rank_lastStop_le N w s
    rw [wireGraph_fst_last, wireGraph_snd_last] at h
    rw [h] at this
    simp [rank] at this
  | into c b =>
    intro h
    have := rank_lastStop_le N (N.sideWire c b) c
    rw [wireGraph_fst_into, wireGraph_snd_into] at h
    rw [h] at this
    simp [rank] at this
  | link c =>
    intro h
    simp [wireGraph_fst_link, wireGraph_snd_link] at h

/-- The wire of a wire segment. -/
def segWire : WireEdge n s → Fin n
  | .last w => w
  | .into c b => N.sideWire c b
  | .link c => N.minWire c

/-- The time at which a wire segment ends. -/
def segTime : WireEdge n s → ℕ
  | .last _ => s
  | .into c _ => c
  | .link c => c

/-- A wire segment, as opposed to a link. -/
def IsSegment : WireEdge n s → Prop
  | .link _ => False
  | _ => True

theorem fst_eq_lastStop {e : WireEdge n s} (he : IsSegment e) :
    N.wireGraph.fst e = N.lastStop (segWire N e) (segTime e) := by
  cases e with
  | last w => rfl
  | into c b => rfl
  | link c => exact he.elim

/-- A wire segment ending at time `t < s` enters a comparator acting on its wire. -/
theorem exists_touch_of_segTime_lt {e : WireEdge n s} (he : IsSegment e) (ht : segTime e < s) :
    ∃ c : Fin s, (c : ℕ) = segTime e ∧
      (N.minWire c = segWire N e ∨ N.maxWire c = segWire N e) := by
  cases e with
  | last w => exact absurd ht (lt_irrefl _)
  | into c b =>
    refine ⟨c, rfl, ?_⟩
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  | link c => exact he.elim

/-- Two wire segments ending at the same time on the same wire are equal. -/
theorem eq_of_segWire_eq_of_segTime_eq {e e' : WireEdge n s} (he : IsSegment e)
    (he' : IsSegment e') (hw : segWire N e = segWire N e') (ht : segTime e = segTime e') :
    e = e' := by
  cases e with
  | last w =>
    cases e' with
    | last w' => exact congrArg _ hw
    | into c' b' => exact absurd ht (by simp [segTime]; omega)
    | link c' => exact he'.elim
  | into c b =>
    cases e' with
    | last w' => exact absurd ht (by simp [segTime]; omega)
    | into c' b' =>
      have hc : c = c' := Fin.ext ht
      subst hc
      rw [sideWire_injective N c hw]
    | link c' => exact he'.elim
  | link c => exact he.elim

/-- **At most one wire segment leaves a vertex.** -/
theorem eq_of_fst_eq {e e' : WireEdge n s} (he : IsSegment e) (he' : IsSegment e')
    (h : N.wireGraph.fst e = N.wireGraph.fst e') : e = e' := by
  rw [fst_eq_lastStop N he, fst_eq_lastStop N he'] at h
  have hw : segWire N e = segWire N e' := by
    rw [← wire_lastStop N (segWire N e) (segTime e), h, wire_lastStop]
  -- a segment ending earlier enters a comparator before the other segment starts
  have key : ∀ {e e' : WireEdge n s}, IsSegment e → IsSegment e' →
      segWire N e = segWire N e' →
      N.lastStop (segWire N e) (segTime e) = N.lastStop (segWire N e') (segTime e') →
      ¬ segTime e < segTime e' := by
    intro e e' he he' hw h hlt
    have hs : segTime e' ≤ s := by
      cases e' with
      | last w => exact le_rfl
      | into c b => exact c.isLt.le
      | link c => exact he'.elim
    obtain ⟨c, hc, htouch⟩ := exists_touch_of_segTime_lt N he (by omega)
    have h₁ := rank_lastStop_le N (segWire N e) (segTime e)
    have h₂ := le_rank_lastStop N (t := segTime e') (by omega) (hw ▸ htouch)
    rw [h] at h₁
    omega
  have ht : segTime e = segTime e' := by
    rcases lt_trichotomy (segTime e) (segTime e') with hlt | heq | hgt
    · exact absurd hlt (key he he' hw h)
    · exact heq
    · exact absurd hgt (key he' he hw.symm h.symm)
  exact eq_of_segWire_eq_of_segTime_eq N he he' hw ht

/-- **At most one wire segment enters a vertex.** -/
theorem eq_of_snd_eq {e e' : WireEdge n s} (he : IsSegment e) (he' : IsSegment e')
    (h : N.wireGraph.snd e = N.wireGraph.snd e') : e = e' := by
  cases e with
  | last w =>
    cases e' with
    | last w' => simpa [wireGraph_snd_last] using h
    | into c' b' => simp [wireGraph_snd_last, wireGraph_snd_into] at h
    | link c' => exact he'.elim
  | into c b =>
    cases e' with
    | last w' => simp [wireGraph_snd_last, wireGraph_snd_into] at h
    | into c' b' =>
      simp only [wireGraph_snd_into, WireVertex.gate.injEq] at h
      rw [h.1, h.2]
    | link c' => exact he'.elim
  | link c => exact he.elim

/-- **The wire graph has maximum degree three.** -/
theorem wireGraph_maxDegreeLE : N.wireGraph.MaxDegreeLE 3 := by
  intro v
  set A := Finset.univ.filter fun e => IsSegment e ∧ N.wireGraph.fst e = v
  set B := Finset.univ.filter fun e => IsSegment e ∧ N.wireGraph.snd e = v
  set C := Finset.univ.filter fun e : WireEdge n s =>
    ¬ IsSegment e ∧ (N.wireGraph.fst e = v ∨ N.wireGraph.snd e = v)
  have hsub : N.wireGraph.edgesAt v ⊆ A ∪ B ∪ C := by
    intro e he
    rw [mem_edgesAt] at he
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, A, B, C]
    by_cases hs : IsSegment e
    · rcases he with he | he
      · exact Or.inl (Or.inl ⟨hs, he⟩)
      · exact Or.inl (Or.inr ⟨hs, he⟩)
    · exact Or.inr ⟨hs, he⟩
  have hA : A.card ≤ 1 := Finset.card_le_one.2 fun e he e' he' => by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
    exact eq_of_fst_eq N he.1 he'.1 (he.2.trans he'.2.symm)
  have hB : B.card ≤ 1 := Finset.card_le_one.2 fun e he e' he' => by
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
    exact eq_of_snd_eq N he.1 he'.1 (he.2.trans he'.2.symm)
  have hC : C.card ≤ 1 := Finset.card_le_one.2 fun e he e' he' => by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
    cases e with
    | last w => exact absurd trivial he.1
    | into c b => exact absurd trivial he.1
    | link c =>
      cases e' with
      | last w => exact absurd trivial he'.1
      | into c b => exact absurd trivial he'.1
      | link c' =>
        simp only [wireGraph_fst_link, wireGraph_snd_link] at he he'
        congr 1
        rcases he.2 with h | h <;> rcases he'.2 with h' | h' <;>
          simpa using h.trans h'.symm
  have := Finset.card_le_card hsub
  have := Finset.card_union_le (A ∪ B) C
  have := Finset.card_union_le A B
  unfold degree
  omega

/-! ### Counting vertices and edges -/

/-- The vertices as a sum type. -/
def vertexEquiv : WireVertex n s ≃ Fin n ⊕ Fin n ⊕ (Fin s × Bool) where
  toFun
    | .input w => .inl w
    | .output w => .inr (.inl w)
    | .gate c b => .inr (.inr (c, b))
  invFun
    | .inl w => .input w
    | .inr (.inl w) => .output w
    | .inr (.inr (c, b)) => .gate c b
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with w | w | ⟨c, b⟩ <;> rfl

/-- The edges as a sum type. -/
def edgeEquiv : WireEdge n s ≃ Fin n ⊕ (Fin s × Bool) ⊕ Fin s where
  toFun
    | .last w => .inl w
    | .into c b => .inr (.inl (c, b))
    | .link c => .inr (.inr c)
  invFun
    | .inl w => .last w
    | .inr (.inl (c, b)) => .into c b
    | .inr (.inr c) => .link c
  left_inv e := by cases e <;> rfl
  right_inv e := by rcases e with w | ⟨c, b⟩ | c <;> rfl

theorem card_wireVertex : Fintype.card (WireVertex n s) = 2 * n + 2 * s := by
  rw [Fintype.card_congr vertexEquiv]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

theorem card_wireEdge : Fintype.card (WireEdge n s) = n + 3 * s := by
  rw [Fintype.card_congr edgeEquiv]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-! ### Token conservation -/

/-- `1` on vertices in `L` and `0` elsewhere. -/
def ind (L : Finset (WireVertex n s)) (v : WireVertex n s) : ℤ :=
  if v ∈ L then 1 else 0

/-- The tokens carried by an edge on input `x`: the value of its wire for a wire segment, and for
the link of a comparator `1` exactly when its `minWire` input is `1` and its `maxWire` input `0`.
-/
def flow (x : Fin n → Bool) : WireEdge n s → ℤ
  | .last w => (N.eval x w).toNat
  | .into c b => (N.state x c (N.sideWire c b)).toNat
  | .link c => (N.state x c (N.minWire c) && !N.state x c (N.maxWire c)).toNat

theorem flow_nonneg (x : Fin n → Bool) (e : WireEdge n s) : 0 ≤ flow N x e := by
  cases e <;> simp [flow]

theorem flow_le_one (x : Fin n → Bool) (e : WireEdge n s) : flow N x e ≤ 1 := by
  cases e <;> simp only [flow] <;> exact_mod_cast Bool.toNat_le _

/-- The net flow out of `L` along the edge `e`. -/
def crossing (x : Fin n → Bool) (L : Finset (WireVertex n s)) (e : WireEdge n s) : ℤ :=
  flow N x e * (ind L (N.wireGraph.fst e) - ind L (N.wireGraph.snd e))

/-- The number of wires carrying `1` at time `t` whose last vertex before time `t` lies in `L`. -/
def potential (x : Fin n → Bool) (L : Finset (WireVertex n s)) (t : ℕ) : ℤ :=
  ∑ w, ind L (N.lastStop w t) * (N.state x t w).toNat

/-- **Conservation at a comparator.** Comparator `c` lowers the potential by the net flow out of
`L` along its two incoming segments and its link. -/
theorem potential_sub_potential_succ (x : Fin n → Bool) (L : Finset (WireVertex n s))
    (c : Fin s) :
    potential N x L c - potential N x L (c + 1) =
      crossing N x L (.into c false) + crossing N x L (.into c true) +
        crossing N x L (.link c) := by
  have hne := N.minWire_ne_maxWire c
  unfold potential
  rw [← Finset.sum_sub_distrib, Fintype.sum_eq_add (N.minWire c) (N.maxWire c) hne]
  · rw [state_succ, apply_minWire, apply_maxWire,
      lastStop_succ_of_touch N c (Or.inl rfl), lastStop_succ_of_touch N c (Or.inr rfl)]
    simp only [decide_true, show decide (N.maxWire c = N.minWire c) = false from
      decide_eq_false (Ne.symm hne), crossing, flow, wireGraph_fst_into, wireGraph_snd_into,
      wireGraph_fst_link, wireGraph_snd_link, sideWire_false, sideWire_true]
    generalize ind L (N.lastStop (N.minWire c) c) = p
    generalize ind L (N.lastStop (N.maxWire c) c) = q
    generalize ind L (.gate c false) = p'
    generalize ind L (.gate c true) = q'
    cases N.state x c (N.minWire c) <;> cases N.state x c (N.maxWire c)
    · simp
    · simp
    · simp
      ring
    · simp
  · rintro w ⟨h₁, h₂⟩
    rw [state_succ, apply_of_ne N c _ (Ne.symm h₁) (Ne.symm h₂),
      lastStop_succ_of_not_touch N c (Ne.symm h₁) (Ne.symm h₂), sub_self]

/-- **Token conservation.** The net flow out of `L` is the number of ones at input terminals in
`L` minus the number at output terminals in `L`. -/
theorem sum_crossing (x : Fin n → Bool) (L : Finset (WireVertex n s)) :
    ∑ e, crossing N x L e =
      ∑ w, ind L (.input w) * (x w).toNat - ∑ w, ind L (.output w) * (N.eval x w).toNat := by
  rw [← Equiv.sum_comp edgeEquiv.symm, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp only [edgeEquiv, Equiv.coe_fn_symm_mk, Fintype.sum_bool]
  have htel : ∑ c : Fin s, (crossing N x L (.into c true) + crossing N x L (.into c false)) +
      ∑ c : Fin s, crossing N x L (.link c) = potential N x L 0 - potential N x L s := by
    rw [← Finset.sum_add_distrib]
    have := Fin.sum_univ_eq_sum_range
      (fun t => potential N x L t - potential N x L (t + 1)) s
    rw [Finset.sum_range_sub'] at this
    rw [← this]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [potential_sub_potential_succ]
    ring
  have hlast : ∑ w, crossing N x L (.last w) =
      potential N x L s - ∑ w, ind L (.output w) * (N.eval x w).toNat := by
    unfold potential
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [crossing, flow, wireGraph_fst_last, wireGraph_snd_last, ComparatorNetwork.eval]
    ring
  have hzero : potential N x L 0 = ∑ w, ind L (.input w) * (x w).toNat := by
    unfold potential
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [lastStop_zero]
    rfl
  linarith

/-- Counting the wires with a one whose terminal lies in `L`. -/
theorem sum_ind_mul_toNat (L : Finset (WireVertex n s)) (P : Fin n → WireVertex n s)
    (y : Fin n → Bool) :
    ∑ w, ind L (P w) * (y w).toNat =
      ((Finset.univ.filter fun w => P w ∈ L ∧ y w = true).card : ℤ) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold ind
  by_cases h : P w ∈ L <;> cases y w <;> simp [h]

/-- One edge carries a net flow of at most one token across `L`, in either direction. -/
theorem crossing_sub_crossing_le (x x' : Fin n → Bool) (L : Finset (WireVertex n s))
    (e : WireEdge n s) :
    crossing N x L e - crossing N x' L e ≤
      if N.wireGraph.fst e ∈ L ↔ N.wireGraph.snd e ∈ L then 0 else 1 := by
  have h₁ := flow_nonneg N x e
  have h₂ := flow_le_one N x e
  have h₃ := flow_nonneg N x' e
  have h₄ := flow_le_one N x' e
  unfold crossing ind
  by_cases hf : N.wireGraph.fst e ∈ L <;> by_cases hs : N.wireGraph.snd e ∈ L <;>
    simp [hf, hs] <;> linarith

/-- **The cut bound of token conservation.** For any two inputs `x` and `x'` and any vertex set
`L`, the cut of `L` has at least `net x - net x'` edges, where `net y` is the number of ones of
`y` at input terminals in `L` minus the number of ones of `N.eval y` at output terminals in
`L`. -/
theorem sub_le_card_cut (x x' : Fin n → Bool) (L : Finset (WireVertex n s)) :
    (((Finset.univ.filter fun w => .input w ∈ L ∧ x w = true).card : ℤ) -
        (Finset.univ.filter fun w => .output w ∈ L ∧ N.eval x w = true).card) -
      (((Finset.univ.filter fun w => .input w ∈ L ∧ x' w = true).card : ℤ) -
        (Finset.univ.filter fun w => .output w ∈ L ∧ N.eval x' w = true).card) ≤
      (N.wireGraph.cut L).card := by
  have hsum : ∑ e, (crossing N x L e - crossing N x' L e) ≤
      ∑ e, (if N.wireGraph.fst e ∈ L ↔ N.wireGraph.snd e ∈ L then (0 : ℤ) else 1) :=
    Finset.sum_le_sum fun e _ => crossing_sub_crossing_le N x x' L e
  have hcut : ((N.wireGraph.cut L).card : ℤ) =
      ∑ e, (if N.wireGraph.fst e ∈ L ↔ N.wireGraph.snd e ∈ L then (0 : ℤ) else 1) := by
    unfold Multigraph.cut
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : N.wireGraph.fst e ∈ L ↔ N.wireGraph.snd e ∈ L <;> simp [h]
  rw [Finset.sum_sub_distrib, sum_crossing, sum_crossing, sum_ind_mul_toNat, sum_ind_mul_toNat,
    sum_ind_mul_toNat, sum_ind_mul_toNat] at hsum
  rw [hcut]
  linarith

/-! ### Connectivity -/

/-- Every vertex is joined to the input terminal of its wire. -/
theorem reflTransGen_input_wire (v : WireVertex n s) :
    ReflTransGen N.wireGraph.Adj v (.input (wire N v)) := by
  suffices ∀ k, ∀ v : WireVertex n s, rank v = k →
      ReflTransGen N.wireGraph.Adj v (.input (wire N v)) from this _ v rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro v hv
    cases v with
    | input w => exact .refl
    | output w =>
      have hadj : N.wireGraph.Adj (.output w) (N.lastStop w s) :=
        ⟨.last w, Or.inr ⟨rfl, rfl⟩⟩
      have hr := rank_lastStop_le N w s
      have := ih _ (by simp only [rank] at hv; omega) (N.lastStop w s) rfl
      rw [wire_lastStop] at this
      exact .head hadj this
    | gate c b =>
      have hadj : N.wireGraph.Adj (.gate c b) (N.lastStop (N.sideWire c b) c) :=
        ⟨.into c b, Or.inr ⟨rfl, rfl⟩⟩
      have hr := rank_lastStop_le N (N.sideWire c b) c
      have := ih _ (by simp only [rank] at hv; omega) (N.lastStop (N.sideWire c b) c) rfl
      rw [wire_lastStop] at this
      exact .head hadj this

/-- The link of a comparator joins its two wires. -/
theorem reflTransGen_minWire_maxWire (c : Fin s) :
    ReflTransGen N.wireGraph.Adj (.input (N.minWire c)) (.input (N.maxWire c)) := by
  have h₁ : ReflTransGen N.wireGraph.Adj (.input (N.minWire c)) (.gate c false) :=
    reflTransGen_adj_symm (reflTransGen_input_wire N (.gate c false))
  have h₂ : N.wireGraph.Adj (.gate c false) (.gate c true) := ⟨.link c, Or.inl ⟨rfl, rfl⟩⟩
  exact (h₁.tail h₂).trans (reflTransGen_input_wire N (.gate c true))

/-- **Small closed sets of wires are empty.** If `N` is an `ε`-halver with `ε < 1/2` and a set
`S` of at most `n/2` wires is closed under the comparators, it is empty: the indicator input of
`S` and that of its complement are fixed by the network, and they would put at most `ε |S|` of
the wires of `S` in each half. -/
theorem eq_empty_of_closed {ε : ℝ} (hN : N.IsHalver ε) (hε : ε < 1 / 2) {S : Finset (Fin n)}
    (hS : ∀ c, N.minWire c ∈ S ↔ N.maxWire c ∈ S) (hk : S.card ≤ n / 2) : S = ∅ := by
  set x : Fin n → Bool := fun w => decide (w ∈ S) with hx
  set y : Fin n → Bool := fun w => decide (w ∉ S) with hy
  have hxe : N.eval x = x := eval_eq_self N x fun c => by simp [x, hS c]
  have hye : N.eval y = y := eval_eq_self N y fun c => by simp [y, hS c]
  have hxc : (Finset.univ.filter fun w => x w = true) = S := by
    ext w
    simp [x]
  have hyc : (Finset.univ.filter fun w => y w = false) = S := by
    ext w
    simp [y]
  have h₁ := (hN x).1 (by rw [hxc]; exact hk)
  have h₂ := (hN y).2 (by rw [hyc]; exact hk)
  rw [hxc, hxe] at h₁
  rw [hyc, hye] at h₂
  have hsub : S ⊆
      (Finset.univ.filter fun w : Fin n => (w : ℕ) < n / 2 ∧ x w = true) ∪
        (Finset.univ.filter fun w : Fin n => n / 2 ≤ (w : ℕ) ∧ y w = false) := by
    intro w hw
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, x, y,
      decide_eq_true_eq, decide_eq_false_iff_not, not_not]
    by_cases hlt : (w : ℕ) < n / 2
    · exact Or.inl ⟨hlt, hw⟩
    · exact Or.inr ⟨by omega, hw⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcard' : (S.card : ℝ) ≤
      ((Finset.univ.filter fun w : Fin n => (w : ℕ) < n / 2 ∧ x w = true).card : ℝ) +
        (Finset.univ.filter fun w : Fin n => n / 2 ≤ (w : ℕ) ∧ y w = false).card := by
    exact_mod_cast hcard
  have hk0 : (S.card : ℝ) ≤ 0 := by
    have : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    nlinarith
  exact Finset.card_eq_zero.1 (by exact_mod_cast le_antisymm hk0 (Nat.cast_nonneg _))

/-- **Lemma 8: closed sets of wires are trivial.** If `N` is an `ε`-halver with `ε < 1/2`, every
set of wires closed under the comparators is empty or all wires. -/
theorem eq_empty_or_eq_univ_of_closed {ε : ℝ} (hN : N.IsHalver ε) (hε : ε < 1 / 2)
    {S : Finset (Fin n)} (hS : ∀ c, N.minWire c ∈ S ↔ N.maxWire c ∈ S) :
    S = ∅ ∨ S = Finset.univ := by
  by_cases hk : S.card ≤ n / 2
  · exact Or.inl (eq_empty_of_closed N hN hε hS hk)
  · right
    have hc : Sᶜ.card ≤ n / 2 := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    have := eq_empty_of_closed N hN hε (S := Sᶜ) (fun c => by
      simp only [Finset.mem_compl]
      exact not_congr (hS c)) hc
    exact Finset.compl_eq_empty_iff _ |>.1 this

/-- **The wire graph of an `ε`-halver with `ε < 1/2` is connected.** -/
theorem wireGraph_connected {ε : ℝ} (hN : N.IsHalver ε) (hε : ε < 1 / 2) :
    N.wireGraph.Connected := by
  intro u v
  set w₀ := wire N u
  set S := Finset.univ.filter fun w => ReflTransGen N.wireGraph.Adj (.input w) (.input w₀)
  have hS : ∀ c, N.minWire c ∈ S ↔ N.maxWire c ∈ S := fun c => by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => (reflTransGen_adj_symm (reflTransGen_minWire_maxWire N c)).trans h,
      fun h => (reflTransGen_minWire_maxWire N c).trans h⟩
  have hw₀ : w₀ ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, .refl⟩
  have hall : ∀ w, ReflTransGen N.wireGraph.Adj (.input w) (.input w₀) := by
    rcases eq_empty_or_eq_univ_of_closed N hN hε hS with h | h
    · rw [h] at hw₀
      exact absurd hw₀ (Finset.notMem_empty _)
    · intro w
      have : w ∈ S := h ▸ Finset.mem_univ w
      simpa [S] using this
  have hv := (reflTransGen_input_wire N v).trans (hall (wire N v))
  exact (reflTransGen_input_wire N u).trans (reflTransGen_adj_symm hv)

/-- **The edge baseline.** An `ε`-halver with `ε < 1/2` on `n` wires has at least `n - 1`
comparators: its wire graph is connected. -/
theorem le_add_one {ε : ℝ} (hN : N.IsHalver ε) (hε : ε < 1 / 2) : n ≤ s + 1 := by
  have := Superconcentrator.Internal.card_le_card_add_one_of_connected
    (wireGraph_connected N hN hε)
  rw [card_wireVertex, card_wireEdge] at this
  omega

/-! ### The cut lemma and the bounds -/

/-- **The cut lemma for halvers.** Every linear order of the vertices of the wire graph of an
`ε`-halver has a lower set whose cut has at least `(1 - 2 ε) ⌊n/2⌋` edges. -/
theorem exists_le_card_cut {ε : ℝ} (hN : N.IsHalver ε) [LinearOrder (WireVertex n s)] :
    ∃ L : Finset (WireVertex n s), IsLowerSet (L : Set (WireVertex n s)) ∧
      (1 - 2 * ε) * ((n / 2 : ℕ) : ℝ) ≤ (N.wireGraph.cut L).card := by
  have hinj : Function.Injective (WireVertex.input : Fin n → WireVertex n s) :=
    fun _ _ h => WireVertex.input.inj h
  obtain ⟨L, hL, hcard⟩ := Superconcentrator.Internal.exists_isLowerSet_card_filter
    (Finset.univ.image (WireVertex.input : Fin n → WireVertex n s)) (k := n / 2)
    (by rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]; omega)
  refine ⟨L, hL, ?_⟩
  set h := n / 2 with hh
  set I := Finset.univ.filter fun w : Fin n => WireVertex.input w ∈ L with hI
  have hIcard : I.card = h := by
    rw [← hcard, ← Finset.card_image_of_injective I hinj]
    congr 1
    ext v
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, I]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, rfl⟩, hw⟩
    · rintro ⟨⟨w, rfl⟩, hw⟩
      exact ⟨w, hw, rfl⟩
  set x : Fin n → Bool := fun w => decide (WireVertex.input w ∈ L) with hx
  set x' : Fin n → Bool := fun w => decide (WireVertex.input w ∉ L) with hx'
  have hcons := sub_le_card_cut N x x' L
  have hin : (Finset.univ.filter fun w => WireVertex.input w ∈ L ∧ x w = true) = I := by
    ext w
    simp [x, I]
  have hin' : (Finset.univ.filter fun w => WireVertex.input w ∈ L ∧ x' w = true) = ∅ := by
    ext w
    simp [x']
  have hxc : (Finset.univ.filter fun w => x w = true) = I := by
    ext w
    simp [x, I]
  have hxc' : (Finset.univ.filter fun w => x' w = false) = I := by
    ext w
    simp [x', I]
  rw [hin, hin', Finset.card_empty, hIcard] at hcons
  have h₁ := (hN x).1 (by rw [hxc, hIcard])
  have h₂ := (hN x').2 (by rw [hxc', hIcard])
  rw [hxc, hIcard] at h₁
  rw [hxc', hIcard] at h₂
  -- `τ` top output terminals lie in `L`
  set τ := (Finset.univ.filter fun w : Fin n => n / 2 ≤ (w : ℕ) ∧
    WireVertex.output w ∈ L).card with hτ
  have ha : (Finset.univ.filter fun w => WireVertex.output w ∈ L ∧ N.eval x w = true).card ≤
      (Finset.univ.filter fun w : Fin n => (w : ℕ) < n / 2 ∧ N.eval x w = true).card + τ := by
    refine (Finset.card_le_card fun w hw => ?_).trans (Finset.card_union_le _ _)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hw ⊢
    by_cases hlt : (w : ℕ) < n / 2
    · exact Or.inl ⟨hlt, hw.2⟩
    · exact Or.inr ⟨by omega, hw.1⟩
  have hb : τ ≤ (Finset.univ.filter fun w => WireVertex.output w ∈ L ∧ N.eval x' w = true).card +
      (Finset.univ.filter fun w : Fin n => n / 2 ≤ (w : ℕ) ∧ N.eval x' w = false).card := by
    refine (Finset.card_le_card fun w hw => ?_).trans (Finset.card_union_le _ _)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hw ⊢
    cases hev : N.eval x' w
    · exact Or.inr ⟨hw.1, rfl⟩
    · exact Or.inl ⟨hw.2, rfl⟩
  have hcons' : ((h : ℤ) : ℝ) -
      ((Finset.univ.filter fun w => WireVertex.output w ∈ L ∧ N.eval x w = true).card : ℝ) -
      (0 - ((Finset.univ.filter fun w => WireVertex.output w ∈ L ∧
        N.eval x' w = true).card : ℝ)) ≤ (N.wireGraph.cut L).card := by
    have := (Int.cast_le (R := ℝ)).2 hcons
    push_cast at this
    simpa using this
  have ha' : ((Finset.univ.filter fun w => WireVertex.output w ∈ L ∧
      N.eval x w = true).card : ℝ) ≤
      ((Finset.univ.filter fun w : Fin n => (w : ℕ) < n / 2 ∧ N.eval x w = true).card : ℝ) +
        τ := by exact_mod_cast ha
  have hb' : (τ : ℝ) ≤ ((Finset.univ.filter fun w => WireVertex.output w ∈ L ∧
      N.eval x' w = true).card : ℝ) +
      ((Finset.univ.filter fun w : Fin n => n / 2 ≤ (w : ℕ) ∧ N.eval x' w = false).card : ℝ) := by
    exact_mod_cast hb
  push_cast at hcons'
  linarith

/-- **The finite bound.** Under the graph-ordering hypothesis `OrderingBound A η C`, an
`ε`-halver with `ε < 1/2` on `n` wires with `s` comparators satisfies
`(1 - 2 ε) ⌊n/2⌋ ≤ (A + η) (s - n)⁺ + 3 log₂ (2 n + 2 s) + C`. -/
theorem le_of_orderingBound {A η C ε : ℝ} (hord : OrderingBound A η C) (hN : N.IsHalver ε)
    (hε : ε < 1 / 2) :
    (1 - 2 * ε) * ((n / 2 : ℕ) : ℝ) ≤
      (A + η) * max ((s : ℝ) - n) 0 + 3 * Real.logb 2 (2 * n + 2 * s) + C := by
  obtain ⟨inst, bound⟩ := hord _ _ N.wireGraph (wireGraph_loopless N)
    (wireGraph_maxDegreeLE N) (wireGraph_connected N hN hε)
  obtain ⟨L, hL, hcut⟩ := @exists_le_card_cut _ _ N _ hN inst
  have hb := bound L hL
  rw [card_wireEdge, card_wireVertex] at hb
  push_cast at hb
  rw [show (n : ℝ) + 3 * s - (2 * n + 2 * s) = s - n by ring] at hb
  linarith

/-- **The asymptotic bound for a general ordering coefficient.** -/
theorem eventually_le_size_of_orderingBound {A : ℝ} (hA : 0 < A)
    (hord : ∀ η : ℝ, 0 < η → ∃ C : ℝ, OrderingBound A η C) {ε δ : ℝ} (hε₀ : 0 ≤ ε)
    (hε : ε < 1 / 2) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ (s : ℕ) (N : ComparatorNetwork n s), N.IsHalver ε →
      (1 + (1 - 2 * ε) / (2 * A) - δ) * n ≤ s := by
  obtain ⟨C, hC⟩ := hord (A ^ 2 * (δ / 2) / 2) (by positivity)
  filter_upwards [Superconcentrator.Internal.eventually_le_of_bound_of_baseline hA
    (half_pos hδ) (D := 2) (B := 2) (by norm_num) (by norm_num) C,
    eventually_ge_atTop ⌈(1 - 2 * ε) / (2 * A) / (δ / 2)⌉₊] with n hn hnδ
  intro s N hN
  have hb := le_of_orderingBound N hC hN hε
  have hbase := le_add_one N hN hε
  have h0 : (0 : ℝ) ≤ 1 - 2 * ε := by linarith
  have hhalf : ((n : ℝ) - 1) / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have hle : ((n / 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n 2
  have key := hn ((1 - 2 * ε) * ((n / 2 : ℕ) : ℝ)) (2 * n) (n + s) (by positivity)
    (by nlinarith) le_rfl
    (by
      have : (n : ℝ) ≤ s + 1 := by exact_mod_cast hbase
      linarith)
    (by positivity)
    (by
      rw [show (n : ℝ) + s - 2 * n = s - n by ring,
        show (2 : ℝ) * (n + s) = 2 * n + 2 * s by ring]
      exact hb)
  set κ := (1 - 2 * ε) / (2 * A) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hκn : κ ≤ δ / 2 * n := by
    have : κ / (δ / 2) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hnδ)
    rwa [div_le_iff₀ (half_pos hδ), mul_comm] at this
  have hdiv : κ * ((n : ℝ) - 1) ≤ (1 - 2 * ε) * ((n / 2 : ℕ) : ℝ) / A := by
    rw [hκ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hA]
    have : 0 ≤ A * (1 - 2 * ε) := mul_nonneg hA.le h0
    nlinarith
  nlinarith

end Algebraic.Cutwidth.Halver.Internal
