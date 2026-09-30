/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Space.BitstringFold.Defs
public import Complexitylib.Classes.Space.Iterate
public import Complexitylib.Classes.P.InitializedIterate
public import Complexitylib.Classes.Containments.Internal.SavitchBits

/-!
# A polynomial-space controller for an ordered bitstring fold

A fixed-width binary counter and an accumulator suffice. The existing
initialized controller preserves the input, and `SpaceIter` supplies the
machine and its space account. No list of all candidates is stored.
-/

@[expose] public section

namespace Complexity.SpaceIter.BitstringFold

open Cobham

/-- Four fields: completion flag, answer flag, cursor, accumulator. -/
def pack (done answer cursor acc : List Bool) : List Bool :=
  pair done (pair answer (pair cursor acc))

/-- The saved verdict, read by a total pair projection. -/
def answer (s : List Bool) : List Bool := pairFst (pairSnd s)
/-- The fixed-width candidate counter. -/
def cursor (s : List Bool) : List Bool := pairFst (pairSnd (pairSnd s))
/-- The accumulator, which may be empty without emptying the encoded state. -/
def acc (s : List Bool) : List Bool := pairSnd (pairSnd (pairSnd s))

theorem pack_length (d a c v : List Bool) :
    (pack d a c v).length = 2 * d.length + 2 * a.length + 2 * c.length + v.length + 6 := by
  simp [pack, pair_length]; omega

theorem pack_ne_nil (d a c v : List Bool) : pack d a c v ≠ [] := by
  intro h
  have := congrArg List.length h
  simp [pack_length] at this

theorem pack_head (d a : Bool) (c v x : List Bool) :
    (pair (pack [d] [a] c v) x).headD false = d := rfl

/-- Process the current candidate, or publish the saved verdict after completion. -/
def step (update : List Bool → List Bool → List Bool → List Bool)
    (accept : List Bool → List Bool → Bool) (x s : List Bool) : List Bool :=
  selectHead (pairFst s ++ [false])
    (pack (answer s) (answer s) (cursor s) (acc s))
    (pack (bumpFlag (cursor s)) [accept x (update x (cursor s) (acc s))]
      (bumpCode (cursor s)) (update x (cursor s) (acc s)))

theorem step_running (update : List Bool → List Bool → List Bool → List Bool)
    (accept : List Bool → List Bool → Bool) (x c v : List Bool) (a : Bool) :
    step update accept x (pack [false] [a] c v) =
      pack [bumpOver c] [accept x (update x c v)] (bumpBits c) (update x c v) := by
  simp [step, pack, cursor, acc, selectHead]

theorem step_done (update : List Bool → List Bool → List Bool → List Bool)
    (accept : List Bool → List Bool → Bool) (x c v : List Bool) (a : Bool) :
    step update accept x (pack [true] [a] c v) = pack [a] [a] c v := by
  simp [step, pack, answer, cursor, acc, selectHead]

theorem step_ne_nil (update : List Bool → List Bool → List Bool → List Bool)
    (accept : List Bool → List Bool → Bool) (x s : List Bool) :
    step update accept x s ≠ [] := by
  cases h : pairFst s with
  | nil =>
      simpa [step, h, selectHead] using
        pack_ne_nil (bumpFlag (cursor s)) [accept x (update x (cursor s) (acc s))]
          (bumpCode (cursor s)) (update x (cursor s) (acc s))
  | cons b tail =>
      cases b <;> simp only [step, h, List.cons_append, selectHead, List.head?_cons,
        ↓reduceIte] <;> apply pack_ne_nil

/-- Begin with the zero candidate and the supplied seed. -/
def initial (seed : List Bool → List Bool) (accept : List Bool → List Bool → Bool)
    (w : Polynomial ℕ) (x : List Bool) : List Bool :=
  pack [false] [accept x (seed x)] (polyRuler w x) (seed x)

/-- Preserve the original input while initializing once and then folding. -/
def controller (seed : List Bool → List Bool)
    (update : List Bool → List Bool → List Bool → List Bool)
    (accept : List Bool → List Bool → Bool) (w : Polynomial ℕ) : List Bool → List Bool :=
  initializedStep (initial seed accept w) (step update accept)

theorem initial_ne_nil (seed : List Bool → List Bool)
    (accept : List Bool → List Bool → Bool) (w : Polynomial ℕ) (x : List Bool) :
    initial seed accept w x ≠ [] := pack_ne_nil _ _ _ _

theorem orbit_ne_nil (seed : List Bool → List Bool)
    (update : List Bool → List Bool → List Bool → List Bool)
    (accept : List Bool → List Bool → Bool) (w : Polynomial ℕ) (x : List Bool) (i : ℕ) :
    (step update accept x)^[i] (initial seed accept w x) ≠ [] := by
  cases i with
  | zero => exact initial_ne_nil _ _ _ _
  | succ i => rw [Function.iterate_succ_apply']; exact step_ne_nil _ _ _ _

theorem controller_iterate (seed : List Bool → List Bool)
    (update : List Bool → List Bool → List Bool → List Bool)
    (accept : List Bool → List Bool → Bool) (w : Polynomial ℕ) (x : List Bool) (i : ℕ) :
    (controller seed update accept w)^[i + 1] (pair [] x) =
      pair ((step update accept x)^[i] (initial seed accept w x)) x :=
  initializedStep_iterate _ _ _ _ (fun j _ => orbit_ne_nil _ _ _ _ _ j)

theorem zero_bits (width : ℕ) : bitsOfLenLE width 0 = List.replicate width false := by
  induction width with
  | zero => rfl
  | succ width ih => simp [bitsOfLenLE, ih, List.replicate_succ]

theorem cursor_length (width i : ℕ) :
    (bumpBits^[i] (List.replicate width false)).length = width := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', bumpBits_length, ih]

theorem cursor_value (width i : ℕ) (hi : i < 2 ^ width) :
    bumpBits^[i] (List.replicate width false) = Nat.toBitsLE width i := by
  rw [← zero_bits, bumpBits_iterate width i hi, bitsOfLenLE_eq_toBitsLE]

theorem cursor_over (width i : ℕ) (hi : i < 2 ^ width) :
    bumpOver (bumpBits^[i] (List.replicate width false)) = decide (i + 1 = 2 ^ width) := by
  rw [← zero_bits, bumpBits_iterate width i hi]
  apply Bool.eq_iff_iff.mpr
  rw [bumpOver_iff, bitsOfLenLE_length, binValLE_bitsOfLenLE width i hi]
  simp only [decide_eq_true_eq]
  omega

/-- The ordinary orbit computes each prefix, raising its flag exactly at the endpoint. -/
theorem orbit (seed : List Bool → List Bool)
    (update : List Bool → List Bool → List Bool → List Bool)
    (accept : List Bool → List Bool → Bool) (w : Polynomial ℕ) (x : List Bool) :
    ∀ i ≤ 2 ^ w.eval x.length,
      (step update accept x)^[i] (initial seed accept w x) =
        pack [decide (i = 2 ^ w.eval x.length)]
          [accept x (bitstringFoldPrefix (update x) (seed x) (w.eval x.length) i)]
          (bumpBits^[i] (polyRuler w x))
          (bitstringFoldPrefix (update x) (seed x) (w.eval x.length) i) := by
  intro i
  induction i with
  | zero =>
      intro _
      simp [initial, bitstringFoldPrefix, Nat.ne_of_lt (Nat.two_pow_pos (w.eval x.length))]
  | succ i ih =>
      intro hi
      have hlt : i < 2 ^ w.eval x.length := by omega
      rw [Function.iterate_succ_apply', ih (by omega)]
      simp only [Nat.ne_of_lt hlt, decide_false]
      rw [step_running, Function.iterate_succ_apply']
      rw [show bumpOver (bumpBits^[i] (polyRuler w x)) =
        decide (i + 1 = 2 ^ w.eval x.length) from cursor_over _ _ hlt]
      rw [bitstringFoldPrefix, show bumpBits^[i] (polyRuler w x) =
        Nat.toBitsLE (w.eval x.length) i from cursor_value _ _ hlt]

theorem orbit_final (seed : List Bool → List Bool)
    (update : List Bool → List Bool → List Bool → List Bool)
    (accept : List Bool → List Bool → Bool) (w : Polynomial ℕ) (x : List Bool) :
    (step update accept x)^[2 ^ w.eval x.length + 1] (initial seed accept w x) =
      pack [accept x (bitstringFold (update x) (seed x) (w.eval x.length))]
        [accept x (bitstringFold (update x) (seed x) (w.eval x.length))]
        (bumpBits^[2 ^ w.eval x.length] (polyRuler w x))
        (bitstringFold (update x) (seed x) (w.eval x.length)) := by
  rw [Function.iterate_succ_apply', orbit _ _ _ _ _ _ le_rfl]
  simp only [decide_true, step_done, bitstringFold]

theorem pack_mem_FP {d a c v : List Bool → List Bool}
    (hd : d ∈ FP) (ha : a ∈ FP) (hc : c ∈ FP) (hv : v ∈ FP) :
    (fun z => pack (d z) (a z) (c z) (v z)) ∈ FP :=
  mem_FP_pair hd (mem_FP_pair ha (mem_FP_pair hc hv))

theorem update_mem_FP {update : List Bool → List Bool → List Bool → List Bool}
    (hu : (fun z => update (pairFst z) (pairFst (pairSnd z))
      (pairSnd (pairSnd z))) ∈ FP)
    {x c v : List Bool → List Bool} (hx : x ∈ FP) (hc : c ∈ FP) (hv : v ∈ FP) :
    (fun z => update (x z) (c z) (v z)) ∈ FP := by
  simpa only [Function.comp_def, pairFst_pair, pairSnd_pair] using
    mem_FP_comp (mem_FP_pair hx (mem_FP_pair hc hv)) hu

theorem accept_mem_FP {accept : List Bool → List Bool → Bool}
    (ha : (fun z => [accept (pairFst z) (pairSnd z)]) ∈ FP)
    {x v : List Bool → List Bool} (hx : x ∈ FP) (hv : v ∈ FP) :
    (fun z => [accept (x z) (v z)]) ∈ FP := by
  simpa only [Function.comp_def, pairFst_pair, pairSnd_pair] using
    mem_FP_comp (mem_FP_pair hx hv) ha

theorem step_mem_FP {update : List Bool → List Bool → List Bool → List Bool}
    {accept : List Bool → List Bool → Bool}
    (hu : (fun z => update (pairFst z) (pairFst (pairSnd z))
      (pairSnd (pairSnd z))) ∈ FP)
    (ha : (fun z => [accept (pairFst z) (pairSnd z)]) ∈ FP)
    {x s : List Bool → List Bool} (hx : x ∈ FP) (hs : s ∈ FP) :
    (fun z => step update accept (x z) (s z)) ∈ FP := by
  have hd := mem_FP_comp hs pairFst_mem_FP
  have ht := mem_FP_comp hs pairSnd_mem_FP
  have hab : (fun z => answer (s z)) ∈ FP := mem_FP_comp ht pairFst_mem_FP
  have htt := mem_FP_comp ht pairSnd_mem_FP
  have hc : (fun z => cursor (s z)) ∈ FP := mem_FP_comp htt pairFst_mem_FP
  have hv : (fun z => acc (s z)) ∈ FP := mem_FP_comp htt pairSnd_mem_FP
  have hn := update_mem_FP hu hx hc hv
  exact selectHeadFn_mem_FP (appendFn_mem_FP hd (constFn_mem_FP [false]))
    (pack_mem_FP hab hab hc hv)
    (pack_mem_FP (bumpFlagFn_mem_FP hc) (accept_mem_FP ha hx hn)
      (bumpCodeFn_mem_FP hc) hn)

theorem controller_mem_FP {seed : List Bool → List Bool}
    {update : List Bool → List Bool → List Bool → List Bool}
    {accept : List Bool → List Bool → Bool} (w : Polynomial ℕ) (hs : seed ∈ FP)
    (hu : (fun z => update (pairFst z) (pairFst (pairSnd z))
      (pairSnd (pairSnd z))) ∈ FP)
    (ha : (fun z => [accept (pairFst z) (pairSnd z)]) ∈ FP) :
    controller seed update accept w ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  apply initializedStep_mem_FP
  · exact pack_mem_FP (constFn_mem_FP [false]) (accept_mem_FP ha hid hs)
      (polyRulerFn_mem_FP w hid) hs
  · exact step_mem_FP hu ha pairSnd_mem_FP pairFst_mem_FP

theorem packed_length (d a : Bool) (c v x : List Bool) :
    (pair (pack [d] [a] c v) x).length =
      4 * c.length + 2 * v.length + x.length + 22 := by
  simp [pair_length, pack_length]; omega

theorem mem_PSPACE_internal {seed : List Bool → List Bool}
    {update : List Bool → List Bool → List Bool → List Bool}
    {accept : List Bool → List Bool → Bool} (w v : Polynomial ℕ) (hs : seed ∈ FP)
    (hu : (fun z => update (pairFst z) (pairFst (pairSnd z))
      (pairSnd (pairSnd z))) ∈ FP)
    (ha : (fun z => [accept (pairFst z) (pairSnd z)]) ∈ FP)
    (hbound : ∀ x i, i ≤ 2 ^ w.eval x.length →
      (bitstringFoldPrefix (update x) (seed x) (w.eval x.length) i).length ≤
        v.eval x.length) :
    {x | accept x (bitstringFold (update x) (seed x) (w.eval x.length)) = true} ∈ PSPACE := by
  refine mem_PSPACE_of_iterate (controller_mem_FP w hs hu ha)
    (4 * w + 2 * v + Polynomial.X + 22) (w + 1)
    (fun x => 2 ^ w.eval x.length + 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x i hi
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    cases i with
    | zero => simp only [Function.iterate_zero_apply, pair_length, List.length_nil]; omega
    | succ j =>
        rw [controller_iterate]
        by_cases hj : j ≤ 2 ^ w.eval x.length
        · rw [orbit _ _ _ _ _ j hj, packed_length]
          have hc := cursor_length (w.eval x.length) j
          have hv := hbound x j hj
          change (bumpBits^[j] (polyRuler w x)).length = w.eval x.length at hc
          omega
        · have hj' : j = 2 ^ w.eval x.length + 1 := by omega
          subst j
          rw [orbit_final, packed_length]
          have hc := cursor_length (w.eval x.length) (2 ^ w.eval x.length)
          have hv := hbound x (2 ^ w.eval x.length) le_rfl
          change (bumpBits^[2 ^ w.eval x.length] (polyRuler w x)).length =
            w.eval x.length at hc
          change (bitstringFold (update x) (seed x) (w.eval x.length)).length ≤
            v.eval x.length at hv
          omega
  · intro x; exact Nat.le_add_left 1 _
  · intro x
    have hp := Nat.two_pow_pos (w.eval x.length)
    simp only [Polynomial.eval_add, Polynomial.eval_one, pow_succ]
    omega
  · intro x i hi hlt
    cases i with
    | zero => omega
    | succ j =>
        have hj : j < 2 ^ w.eval x.length := by omega
        rw [controller_iterate, orbit _ _ _ _ _ j (by omega), pack_head]
        simp [Nat.ne_of_lt hj]
  · intro x
    rw [controller_iterate, orbit _ _ _ _ _ _ le_rfl, pack_head]
    simp
  · intro x
    rw [controller_iterate, orbit_final]
    intro h
    have := congrArg List.length h
    simp at this
  · intro x
    rw [controller_iterate, orbit_final, pack_head]
    rfl

/-- Boolean OR uses a one-bit accumulator, independently of the number of candidates. -/
theorem or_prefix_length (p : List Bool → Bool) (width i : ℕ) :
    (bitstringFoldPrefix (fun c a => [a.headD false || p c]) [false] width i).length = 1 := by
  cases i <;> simp [bitstringFoldPrefix]

theorem or_prefix_iff (p : List Bool → Bool) (width i : ℕ) :
    (bitstringFoldPrefix (fun c a => [a.headD false || p c]) [false] width i).headD false = true
      ↔ ∃ j < i, p (Nat.toBitsLE width j) = true := by
  induction i with
  | zero => simp [bitstringFoldPrefix]
  | succ i ih =>
      simp only [bitstringFoldPrefix, List.headD_cons, Bool.or_eq_true, ih,
        Nat.exists_lt_succ_right]

theorem or_fold_iff (p : List Bool → Bool) (width : ℕ) :
    (bitstringFold (fun c a => [a.headD false || p c]) [false] width).headD false = true
      ↔ ∃ c, c.length = width ∧ p c = true := by
  rw [bitstringFold, or_prefix_iff]
  constructor
  · rintro ⟨j, _, hp⟩
    exact ⟨Nat.toBitsLE width j, Nat.length_toBitsLE _ _, hp⟩
  · rintro ⟨c, hc, hp⟩
    refine ⟨Nat.fromBitsLE c, ?_, ?_⟩
    · simpa [hc] using Nat.fromBitsLE_lt_pow_length c
    · rwa [← hc, Nat.toBitsLE_fromBitsLE]

theorem head_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun z => [(f z).headD false]) ∈ FP := by
  refine mem_FP_of_eq (notBitFn_mem_FP (notBitFn_mem_FP hf)) fun z => ?_
  cases f z with
  | nil => rfl
  | cons b tail => cases b <;> rfl

theorem or_eq (a : List Bool) (b : Bool) : orBit a [b] = [a.headD false || b] := by
  cases a with
  | nil => cases b <;> rfl
  | cons c tail => cases c <;> cases b <;> rfl

theorem exists_bitstring_mem_PSPACE_internal {p : List Bool → List Bool → Bool}
    (w : Polynomial ℕ) (hp : (fun z => [p (pairFst z) (pairSnd z)]) ∈ FP) :
    {x | ∃ c, c.length = w.eval x.length ∧ p x c = true} ∈ PSPACE := by
  have hc := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hv := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hu : (fun z => [(pairSnd (pairSnd z)).headD false ||
      p (pairFst z) (pairFst (pairSnd z))]) ∈ FP := by
    refine mem_FP_of_eq (orBitFn_mem_FP hv (accept_mem_FP hp pairFst_mem_FP hc)) ?_
    intro z; exact or_eq _ _
  have h := mem_PSPACE_internal (seed := fun _ => [false])
    (update := fun x c a => [a.headD false || p x c])
    (accept := fun _ a => a.headD false) w 1 (constFn_mem_FP [false]) hu
    (head_mem_FP pairSnd_mem_FP) (fun x i _ => by
      simpa only [Polynomial.eval_one] using (or_prefix_length (p x) (w.eval x.length) i).le)
  have heq : {x | (bitstringFold (fun c a => [a.headD false || p x c])
        [false] (w.eval x.length)).headD false = true} =
      {x | ∃ c, c.length = w.eval x.length ∧ p x c = true} :=
    Set.ext fun x => or_fold_iff (p x) (w.eval x.length)
  rwa [heq] at h

end Complexity.SpaceIter.BitstringFold
