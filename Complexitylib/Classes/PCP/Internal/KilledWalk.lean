/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Power

/-!
# Killed walks

The walk law Dinur's powering step actually needs: at every step the walk stops
with probability `1 / q`, so its length is geometric rather than fixed.

A dart label is a pair of sequences: `T` edge labels and `T` stop signals. The
walk follows the edge labels until the first signal equal to `0` — the
**stopping index** — and its endpoint is where it stopped. Uniform labels
therefore realise a geometric length exactly, truncated at `T`, with the labels
past the stopping index carrying multiplicity but no meaning.

## Why geometric and not fixed length

Soundness decodes an assignment of the powered system by plurality and needs the
opinions at the two ends of a checked step to be truthful. Summed over the
checked steps that amounts to `∑ a_i · b_j` over the prefix length `i` and the
suffix length `j`. With walks of *fixed* length those are tied by `i + j = t - 1`
and the sum can vanish — the two ends can be truthful at complementary lengths
and never at the same step, so nothing is charged. Killing makes
`i` and `j` **independent**, so the sum factorises into a product of two
plurality bounds. That factorisation is the whole reason for this construction.

## Reversal

Reversing a killed walk reverses only its effective prefix and leaves both the
tail and the stop signals alone. Since the signals are untouched, the reversed
walk stops at the same index, which is what makes reversal an involution — the
requirement for the powered graph to be an undirected regular graph at all.

## Main definitions

- `stopAt` — the stopping index of a signal sequence
- `RegGraph.preWalk`, `RegGraph.extWalk` — the effective prefix, and
  overwriting it
- `RegGraph.killedEnd`, `RegGraph.killedRev` — the endpoint and the reversal
- `RegGraph.killedPower` — the resulting regular graph

## Main results

- `signal_ne_zero_of_lt`, `signal_eq_zero_of_stopAt_lt`, `stopAt_eq_of` — what
  the stopping index means
- `lt_stopAt_iff` — reaching step `i` depends only on the first `i + 1` signals
- `card_lt_stopAt`, `card_le_stopAt`, `card_stopAt_eq` — how many signal
  sequences run for a given number of steps
- `RegGraph.card_preWalk_eq`, `RegGraph.card_killed_fibre` — the weight an
  effective walk carries
- `RegGraph.killedEnd_killedRev`, `RegGraph.killedRev_killedRev` — reversal
  undoes itself
- `RegGraph.deg_killedPower` — the degree is `deg ^ T * q ^ T`
-/

@[expose] public section

namespace Complexity

/-- The step at which a killed walk stops: the first index carrying the signal
`0`, or `T` if there is none. -/
def stopAt {T q : ℕ} (c : Fin T → Fin q) : ℕ :=
  (List.finRange T).findIdx fun i => (c i).val == 0

theorem stopAt_le {T q : ℕ} (c : Fin T → Fin q) : stopAt c ≤ T := by
  have h := List.findIdx_le_length (p := fun i : Fin T => (c i).val == 0)
    (xs := List.finRange T)
  simpa [stopAt] using h

/-- Before the stopping index every signal is nonzero. -/
theorem signal_ne_zero_of_lt {T q : ℕ} (c : Fin T → Fin q) {j : ℕ} (hj : j < stopAt c) :
    (c ⟨j, lt_of_lt_of_le hj (stopAt_le c)⟩).val ≠ 0 := by
  have h := List.not_of_lt_findIdx (p := fun i : Fin T => (c i).val == 0)
    (xs := List.finRange T) hj
  rw [List.getElem_finRange] at h
  simpa using h

/-- At the stopping index, if it is reached, the signal is zero. -/
theorem signal_eq_zero_of_stopAt_lt {T q : ℕ} (c : Fin T → Fin q) (h : stopAt c < T) :
    (c ⟨stopAt c, h⟩).val = 0 := by
  have hlen : stopAt c < (List.finRange T).length := by simpa using h
  have hg := List.findIdx_getElem (p := fun i : Fin T => (c i).val == 0)
    (xs := List.finRange T) (w := hlen)
  erw [List.getElem_finRange] at hg
  simpa [stopAt, Fin.cast] using hg

/-- The stopping index is pinned down by the two properties above. -/
theorem stopAt_eq_of {T q : ℕ} (c : Fin T → Fin q) {m : ℕ} (hm : m ≤ T)
    (hlt : ∀ (j : ℕ) (hj : j < m), (c ⟨j, lt_of_lt_of_le hj hm⟩).val ≠ 0)
    (hat : ∀ h : m < T, (c ⟨m, h⟩).val = 0) : stopAt c = m := by
  rcases lt_trichotomy (stopAt c) m with hlt' | heq | hgt
  · have hsT : stopAt c < T := lt_of_lt_of_le hlt' hm
    exact absurd (signal_eq_zero_of_stopAt_lt c hsT) (hlt (stopAt c) hlt')
  · exact heq
  · have hmT : m < T := lt_of_lt_of_le hgt (stopAt_le c)
    exact absurd (hat hmT) (signal_ne_zero_of_lt c hgt)

/-- The walk is still running at step `i` exactly when the first `i + 1`
signals are all nonzero. This is the form the crossing decomposition needs: the
event "the walk reaches step `i`" depends only on the first `i + 1` signal
coordinates, so it splits off as a factor. -/
theorem lt_stopAt_iff {T q : ℕ} (c : Fin T → Fin q) {i : ℕ} (hi : i < T) :
    i < stopAt c ↔ ∀ (j : ℕ) (hj : j ≤ i), (c ⟨j, lt_of_le_of_lt hj hi⟩).val ≠ 0 := by
  constructor
  · intro h j hj
    exact signal_ne_zero_of_lt c (lt_of_le_of_lt hj h)
  · intro h
    by_contra hcon
    have hle : stopAt c ≤ i := by omega
    have hsT : stopAt c < T := lt_of_le_of_lt hle hi
    exact h (stopAt c) hle (signal_eq_zero_of_stopAt_lt c hsT)

/-- **The signal count.** The walks still running at step `i` are exactly those
whose first `i + 1` signals are all nonzero, and those coordinates are free of
one another, so they number `(q-1) ^ (i+1) * q ^ (T-i-1)`. This is the factor
that the crossing decomposition peels off. -/
theorem card_lt_stopAt {T q : ℕ} {i : ℕ} (hi : i < T) :
    (Finset.univ.filter fun c : Fin T → Fin q => i < stopAt c).card
      = (q - 1) ^ (i + 1) * q ^ (T - i - 1) := by
  classical
  have hset : (Finset.univ.filter fun c : Fin T → Fin q => i < stopAt c)
      = Fintype.piFinset fun j : Fin T =>
          if j.val ≤ i then Finset.univ.filter (fun x : Fin q => x.val ≠ 0)
          else Finset.univ := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    rw [lt_stopAt_iff c hi]
    constructor
    · intro h j
      by_cases hj : j.val ≤ i
      · simp only [hj, ite_true, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa using h j.val hj
      · simp [hj]
    · intro h j hj
      have hmem := h ⟨j, lt_of_le_of_lt hj hi⟩
      simp only [hj, ite_true, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact hmem
  have hnz : (Finset.univ.filter (fun x : Fin q => x.val ≠ 0)).card = q - 1 := by
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · subst hq0
      simp
    · have hcompl : (Finset.univ.filter (fun x : Fin q => x.val ≠ 0)).card
          + (Finset.univ.filter (fun x : Fin q => ¬ x.val ≠ 0)).card = q := by
        rw [Finset.card_filter_add_card_filter_not]
        simp
      have hone : (Finset.univ.filter (fun x : Fin q => ¬ x.val ≠ 0)).card = 1 := by
        have hsingle : (Finset.univ.filter (fun x : Fin q => ¬ x.val ≠ 0)) = {⟨0, hq0⟩} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not,
            Finset.mem_singleton]
          constructor
          · intro hx; exact Fin.ext hx
          · intro hx; rw [hx]
        rw [hsingle, Finset.card_singleton]
      omega
  have hle : (Finset.univ.filter fun j : Fin T => j.val ≤ i).card = i + 1 := by
    have himg : (Finset.univ.filter fun j : Fin T => j.val ≤ i).image Fin.val
        = Finset.range (i + 1) := by
      ext n
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_range]
      constructor
      · rintro ⟨j, hj, rfl⟩; omega
      · intro hn
        exact ⟨⟨n, by omega⟩, by simpa using by omega, rfl⟩
    have hcard := congrArg Finset.card himg
    rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_range] at hcard
    exact hcard
  have hgt : (Finset.univ.filter fun j : Fin T => ¬ j.val ≤ i).card = T - i - 1 := by
    have hsum : (Finset.univ.filter fun j : Fin T => j.val ≤ i).card
        + (Finset.univ.filter fun j : Fin T => ¬ j.val ≤ i).card = T := by
      rw [Finset.card_filter_add_card_filter_not]
      simp
    omega
  rw [hset, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, hnz, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, hle, hgt]

/-- The walks that are still running *at* step `m`, i.e. run for at least `m`
steps. -/
theorem card_le_stopAt {T q : ℕ} {m : ℕ} (hm : m ≤ T) :
    (Finset.univ.filter fun c : Fin T → Fin q => m ≤ stopAt c).card
      = (q - 1) ^ m * q ^ (T - m) := by
  cases m with
  | zero =>
      have huniv : (Finset.univ.filter fun c : Fin T → Fin q => 0 ≤ stopAt c)
          = Finset.univ := by
        ext c
        simp
      rw [huniv]
      simp
  | succ k =>
      have hk : k < T := by omega
      have hsame : (Finset.univ.filter fun c : Fin T → Fin q => k + 1 ≤ stopAt c)
          = (Finset.univ.filter fun c : Fin T → Fin q => k < stopAt c) := by
        ext c
        simp
      rw [hsame, card_lt_stopAt hk]
      congr 1

/-- **The exact-length signal count.** The walks of effective length exactly `m`
number `(q-1) ^ m * q ^ (T-m-1)`: the first `m` signals are nonzero, the `m`-th
is zero, and the rest are free. -/
theorem card_stopAt_eq {T q : ℕ} (hq : 0 < q) {m : ℕ} (hm : m < T) :
    (Finset.univ.filter fun c : Fin T → Fin q => stopAt c = m).card
      = (q - 1) ^ m * q ^ (T - m - 1) := by
  classical
  have hsub : (Finset.univ.filter fun c : Fin T → Fin q => m < stopAt c)
      ⊆ (Finset.univ.filter fun c : Fin T → Fin q => m ≤ stopAt c) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    omega
  have hdiff : (Finset.univ.filter fun c : Fin T → Fin q => stopAt c = m)
      = (Finset.univ.filter fun c : Fin T → Fin q => m ≤ stopAt c)
        \ (Finset.univ.filter fun c : Fin T → Fin q => m < stopAt c) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_lt]
    omega
  rw [hdiff, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
    card_le_stopAt (le_of_lt hm), card_lt_stopAt hm]
  have hsplit : q ^ (T - m) = q * q ^ (T - m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hsplit, pow_succ]
  cases q with
  | zero => omega
  | succ p =>
      have hone : p + 1 - 1 = p := by omega
      rw [hone]
      refine Nat.sub_eq_of_eq_add ?_
      ring

namespace RegGraph

variable (G : RegGraph)

/-! ### Prefixes -/

/-- The first `ℓ` labels of a length-`T` sequence. -/
def preWalk {T : ℕ} (s : Fin T → G.D) {ℓ : ℕ} (h : ℓ ≤ T) : Fin ℓ → G.D :=
  fun j => s ⟨j.val, lt_of_lt_of_le j.isLt h⟩

/-- Overwrite the first `ℓ` labels of a sequence. -/
def extWalk {T ℓ : ℕ} (r : Fin ℓ → G.D) (s : Fin T → G.D) : Fin T → G.D :=
  fun i => if h : i.val < ℓ then r ⟨i.val, h⟩ else s i

theorem preWalk_extWalk {T ℓ : ℕ} (h : ℓ ≤ T) (r : Fin ℓ → G.D) (s : Fin T → G.D) :
    G.preWalk (G.extWalk r s) h = r := by
  funext j
  simp [preWalk, extWalk, j.isLt]

theorem extWalk_extWalk {T ℓ : ℕ} (r r' : Fin ℓ → G.D) (s : Fin T → G.D) :
    G.extWalk r' (G.extWalk r s) = G.extWalk r' s := by
  funext i
  by_cases hi : i.val < ℓ <;> simp [extWalk, hi]

theorem extWalk_preWalk {T ℓ : ℕ} (h : ℓ ≤ T) (s : Fin T → G.D) :
    G.extWalk (G.preWalk s h) s = s := by
  funext i
  by_cases hi : i.val < ℓ <;> simp [extWalk, preWalk, hi]

/-- How many label sequences begin with a prescribed length-`m` walk: the first
`m` coordinates are pinned and the rest are free. -/
theorem card_preWalk_eq {T m : ℕ} (hm : m ≤ T) (w : Fin m → G.D) :
    (Finset.univ.filter fun s : Fin T → G.D => G.preWalk s hm = w).card
      = G.deg ^ (T - m) := by
  classical
  have hset : (Finset.univ.filter fun s : Fin T → G.D => G.preWalk s hm = w)
      = Fintype.piFinset fun j : Fin T =>
          if hj : j.val < m then {w ⟨j.val, hj⟩} else Finset.univ := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j
      by_cases hj : j.val < m
      · simp only [hj, dite_eq_left, Finset.mem_singleton]
        have hval := congrFun h ⟨j.val, hj⟩
        simpa [RegGraph.preWalk] using hval
      · simp [hj]
    · intro h
      funext j
      have hmem := h ⟨j.val, lt_of_lt_of_le j.isLt hm⟩
      simp only [j.isLt, dite_eq_left, Finset.mem_singleton] at hmem
      simpa [RegGraph.preWalk] using hmem
  have hlt : (Finset.univ.filter fun j : Fin T => j.val < m).card = m := by
    have himg : (Finset.univ.filter fun j : Fin T => j.val < m).image Fin.val
        = Finset.range m := by
      ext n
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_range]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact hj
      · intro hn
        exact ⟨⟨n, by omega⟩, by simpa using hn, rfl⟩
    have hcard := congrArg Finset.card himg
    rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_range] at hcard
    exact hcard
  have hge : (Finset.univ.filter fun j : Fin T => ¬ j.val < m).card = T - m := by
    have hsum : (Finset.univ.filter fun j : Fin T => j.val < m).card
        + (Finset.univ.filter fun j : Fin T => ¬ j.val < m).card = T := by
      rw [Finset.card_filter_add_card_filter_not]
      simp
    omega
  rw [hset, Fintype.card_piFinset]
  simp only [apply_dite Finset.card, Finset.card_singleton, Finset.card_univ,
    dite_eq_ite]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, hlt, hge]
  simp

/-- **The fibre count.** The killed-walk labels whose effective walk is exactly
a prescribed length-`m` walk number `deg ^ (T-m) * (q-1) ^ m * q ^ (T-m-1)`: the
two conditions constrain the edge labels and the signals separately, so the
counts multiply. This is the weight each effective walk carries, and it is
geometric in `m` — the law both the plurality and the conditional prefix and
suffix follow. -/
theorem card_killed_fibre {T q m : ℕ} (hq : 0 < q) (hm : m < T) (w : Fin m → G.D) :
    (Finset.univ.filter fun x : (Fin T → G.D) × (Fin T → Fin q) =>
        G.preWalk x.1 (le_of_lt hm) = w ∧ stopAt x.2 = m).card
      = G.deg ^ (T - m) * ((q - 1) ^ m * q ^ (T - m - 1)) := by
  classical
  have hset : (Finset.univ.filter fun x : (Fin T → G.D) × (Fin T → Fin q) =>
      G.preWalk x.1 (le_of_lt hm) = w ∧ stopAt x.2 = m)
      = (Finset.univ.filter fun s : Fin T → G.D => G.preWalk s (le_of_lt hm) = w)
        ×ˢ (Finset.univ.filter fun c : Fin T → Fin q => stopAt c = m) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  rw [hset, Finset.card_product, G.card_preWalk_eq (le_of_lt hm) w, card_stopAt_eq hq hm]

/-! ### Killed walks -/

/-- Where a killed walk ends: it follows the edge labels up to the stopping
index. -/
def killedEnd {T q : ℕ} (v : G.V) (s : Fin T → G.D) (c : Fin T → Fin q) : G.V :=
  G.walkEnd (stopAt c) v (G.preWalk s (stopAt_le c))

/-- A killed walk reversed: the effective prefix is reversed, the tail and the
stop signals are left alone. -/
def killedRev {T q : ℕ} (v : G.V) (s : Fin T → G.D) (c : Fin T → Fin q) : Fin T → G.D :=
  G.extWalk (G.revWalk v (G.preWalk s (stopAt_le c))) s

theorem killedEnd_killedRev {T q : ℕ} (v : G.V) (s : Fin T → G.D) (c : Fin T → Fin q) :
    G.killedEnd (G.killedEnd v s c) (G.killedRev v s c) c = v := by
  rw [killedEnd, killedRev, killedEnd, G.preWalk_extWalk (stopAt_le c)]
  exact G.walkEnd_revWalk v (G.preWalk s (stopAt_le c))

theorem killedRev_killedRev {T q : ℕ} (v : G.V) (s : Fin T → G.D) (c : Fin T → Fin q) :
    G.killedRev (G.killedEnd v s c) (G.killedRev v s c) c = s := by
  rw [killedRev, killedRev, G.preWalk_extWalk (stopAt_le c), killedEnd,
    G.revWalk_revWalk, G.extWalk_extWalk, G.extWalk_preWalk]

/-! ### The killed power graph -/

/-- The killed power of `G`: a dart label is `T` edge labels together with `T`
stop signals, and the neighbour is where the walk stops. -/
def killedPower (G : RegGraph) (q T : ℕ) (hq : 0 < q) : RegGraph where
  V := G.V
  D := (Fin T → G.D) × (Fin T → Fin q)
  decEqV := G.decEqV
  decEqD := by
    haveI := G.decEqD
    infer_instance
  fintypeV := G.fintypeV
  fintypeD := by
    haveI := G.fintypeD
    haveI := G.decEqD
    infer_instance
  nonemptyD := by
    have := G.nonemptyD
    have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
    infer_instance
  rot x := (G.killedEnd x.1 x.2.1 x.2.2, (G.killedRev x.1 x.2.1 x.2.2, x.2.2))
  rot_involutive := by
    rintro ⟨v, s, c⟩
    dsimp only
    rw [G.killedEnd_killedRev, G.killedRev_killedRev]

@[simp] theorem V_killedPower (q T : ℕ) (hq : 0 < q) : (G.killedPower q T hq).V = G.V := rfl

@[simp] theorem order_killedPower (q T : ℕ) (hq : 0 < q) :
    (G.killedPower q T hq).order = G.order := rfl

theorem nbr_killedPower (q T : ℕ) (hq : 0 < q) (v : G.V)
    (x : (Fin T → G.D) × (Fin T → Fin q)) :
    (G.killedPower q T hq).nbr v x = G.killedEnd v x.1 x.2 := rfl

/-- The killed power is regular of degree `deg ^ T * q ^ T`. -/
theorem deg_killedPower (q T : ℕ) (hq : 0 < q) :
    (G.killedPower q T hq).deg = G.deg ^ T * q ^ T := by
  have h : Fintype.card ((Fin T → G.D) × (Fin T → Fin q)) = G.deg ^ T * q ^ T := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin]
    rfl
  calc (G.killedPower q T hq).deg
      = Fintype.card ((Fin T → G.D) × (Fin T → Fin q)) := Fintype.card_congr (Equiv.refl _)
    _ = G.deg ^ T * q ^ T := h

end RegGraph

end Complexity
