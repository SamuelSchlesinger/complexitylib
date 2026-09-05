/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine
public import Complexitylib.Asymptotics
public import Complexitylib.Classes.FiniteCounting

/-!
# The counting class `#P`

**#P** (sharp-P) is the class of functions that count the accepting leaves of a
polynomial-time nondeterministic computation tree (roadmap track L5).

This is deliberately distinct from `NTM.acceptCount`, which counts fixed-length
choice strings for probabilistic semantics. If a machine halts early, all
extensions of that random string must retain their multiplicity when computing a
probability, but the halted computation is only one leaf of a nondeterministic
tree. `NTM.acceptLeafCount` implements the latter convention and is invariant
under extending any clock by which every path has halted.

## Main definitions and results

- `SharpP` — the counting class
- `NTM.acceptCount_le` — a machine has at most `2 ^ T` accepting fixed-clock
  choice strings among the `2 ^ T` length-`T` strings
- `NTM.acceptLeafCount_eq_of_le_of_allPathsHaltIn` — accepting-leaf counts do not
  depend on the choice of a sufficient clock
- `SharpP.le_two_pow` — every `#P` function is bounded by `2 ^ T(|x|)` for its
  polynomial clock `T`
-/


public section

namespace Complexity

namespace NTM

variable {n : ℕ}

/-- Count accepting leaves in the nondeterministic computation tree rooted at
`c`, truncated after at most `T` transitions. A halted configuration contributes
one leaf, rather than one copy for every unused suffix of the choice string. -/
def acceptLeafCountFrom (tm : NTM n) : ℕ → Cfg n tm.Q → ℕ
  | 0, c => if tm.halted c ∧ c.output.cells 1 = Γ.one then 1 else 0
  | T + 1, c =>
      if tm.halted c then
        if c.output.cells 1 = Γ.one then 1 else 0
      else
        tm.acceptLeafCountFrom T (tm.trace 1 (fun _ => false) c) +
          tm.acceptLeafCountFrom T (tm.trace 1 (fun _ => true) c)

/-- Number of accepting leaves reached from the initial configuration within
`T` transitions. Unlike `acceptCount`, this counts an early-halting path once. -/
def acceptLeafCount (tm : NTM n) (x : List Bool) (T : ℕ) : ℕ :=
  tm.acceptLeafCountFrom T (tm.initCfg x)

/-- An accepting computation tree of height at most `T` has at most `2 ^ T`
leaves. -/
theorem acceptLeafCountFrom_le (tm : NTM n) (c : Cfg n tm.Q) (T : ℕ) :
    tm.acceptLeafCountFrom T c ≤ 2 ^ T := by
  induction T generalizing c with
  | zero =>
      rw [acceptLeafCountFrom]
      split <;> omega
  | succ T ih =>
      by_cases hhalt : tm.halted c
      · rw [acceptLeafCountFrom, ite_eq_left hhalt, Nat.pow_succ]
        split
        · have hpow : 0 < 2 ^ T := by positivity
          omega
        · omega
      · rw [acceptLeafCountFrom, ite_eq_right hhalt, Nat.pow_succ]
        have hfalse := ih (tm.trace 1 (fun _ => false) c)
        have htrue := ih (tm.trace 1 (fun _ => true) c)
        omega

/-- A machine has at most `2 ^ T` accepting leaves within `T` transitions. -/
theorem acceptLeafCount_le (tm : NTM n) (x : List Bool) (T : ℕ) :
    tm.acceptLeafCount x T ≤ 2 ^ T :=
  tm.acceptLeafCountFrom_le (tm.initCfg x) T

/-- Once every depth-`T` choice sequence has reached a halted configuration,
extending the tree-height bound by `d` does not change its accepting leaves. -/
private theorem acceptLeafCountFrom_add_eq (tm : NTM n) (c : Cfg n tm.Q)
    (T d : ℕ)
    (hhalt : ∀ choices : Fin T → Bool, tm.halted (tm.trace T choices c)) :
    tm.acceptLeafCountFrom (T + d) c = tm.acceptLeafCountFrom T c := by
  induction T generalizing c with
  | zero =>
      have hc : tm.halted c := by
        simpa [NTM.trace] using hhalt (fun i => Fin.elim0 i)
      cases d with
      | zero => rfl
      | succ d =>
          rw [Nat.zero_add, acceptLeafCountFrom, acceptLeafCountFrom, ite_eq_left hc]
          by_cases hout : c.output.cells 1 = Γ.one <;> simp [hc, hout]
  | succ T ih =>
      by_cases hc : tm.halted c
      · rw [show T + 1 + d = (T + d) + 1 by omega]
        rw [acceptLeafCountFrom, acceptLeafCountFrom, ite_eq_left hc, ite_eq_left hc]
      · have hbranch (b : Bool) :
            ∀ choices : Fin T → Bool,
              tm.halted
                (tm.trace T choices (tm.trace 1 (fun _ => b) c)) := by
          intro choices
          let choices' : Fin (T + 1) → Bool := Fin.cases b choices
          simpa [choices', NTM.trace, hc] using hhalt choices'
        rw [Nat.succ_add]
        simp only [acceptLeafCountFrom, hc, ite_false]
        rw [ih _ (hbranch false), ih _ (hbranch true)]

/-- Once every path has halted by `T`, extending the observation clock to any
`T' ≥ T` leaves the accepting-leaf count unchanged. -/
theorem acceptLeafCount_eq_of_le_of_allChoicesHalt (tm : NTM n) (x : List Bool)
    {T T' : ℕ} (hle : T ≤ T')
    (hhalt : ∀ choices : Fin T → Bool,
      tm.halted (tm.trace T choices (tm.initCfg x))) :
    tm.acceptLeafCount x T' = tm.acceptLeafCount x T := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact tm.acceptLeafCountFrom_add_eq (tm.initCfg x) T d hhalt

/-- A pointwise-larger sufficient clock gives the same accepting-leaf count. -/
theorem acceptLeafCount_eq_of_le_of_allPathsHaltIn {T T' : ℕ → ℕ}
    (tm : NTM n) (hle : ∀ m, T m ≤ T' m) (hhalt : tm.AllPathsHaltIn T)
    (x : List Bool) :
    tm.acceptLeafCount x (T' x.length) = tm.acceptLeafCount x (T x.length) :=
  tm.acceptLeafCount_eq_of_le_of_allChoicesHalt x (hle x.length) (hhalt x)

end NTM

/-- The number of accepting choice sequences is at most the total number of
    choice sequences, `2 ^ T`: it is the cardinality of a subset of the `2 ^ T`
    length-`T` random strings. -/
theorem NTM.acceptCount_le {n : ℕ} (N : NTM n) (x : List Bool) (T : ℕ) :
    N.acceptCount x T ≤ 2 ^ T := by
  unfold NTM.acceptCount
  calc (Finset.univ.filter _).card
      ≤ (Finset.univ : Finset (Fin T → Bool)).card := Finset.card_filter_le _ _
    _ = 2 ^ T := by rw [Finset.card_univ, card_finArrowBool]

/-- **#P** (sharp-P): the class of functions `f : List Bool → ℕ` counting the
    accepting leaves of a polynomial-time nondeterministic machine. `f ∈ SharpP`
    when some NTM halts on every path within a polynomial time bound `T` and
    `f x` equals its accepting-leaf count. Unlike fixed-clock PTM probability,
    unused choice bits after an early halt do not duplicate a computation leaf. -/
def SharpP : Set (List Bool → ℕ) :=
  {f | ∃ (m : ℕ) (N : NTM m) (T : ℕ → ℕ) (k : ℕ),
    N.AllPathsHaltIn T ∧ T =O (· ^ k) ∧
    ∀ x, f x = N.acceptLeafCount x (T x.length)}

/-- Every `#P` function is bounded by `2 ^ T(|x|)` for its polynomial clock `T`:
    a witness that `#P` functions have at-most-exponential values. -/
theorem SharpP.le_two_pow {f : List Bool → ℕ} (hf : f ∈ SharpP) :
    ∃ T : ℕ → ℕ, (∃ k, T =O (· ^ k)) ∧ ∀ x, f x ≤ 2 ^ T x.length := by
  obtain ⟨m, N, T, k, _, hpoly, hval⟩ := hf
  exact ⟨T, ⟨k, hpoly⟩,
    fun x => (hval x).le.trans (N.acceptLeafCount_le x (T x.length))⟩

/-- **GapP**: the class of integer-valued functions expressible as the difference
    of two `#P` functions (equivalently, accepting minus rejecting paths of a
    polynomial-time nondeterministic machine). -/
def GapP : Set (List Bool → ℤ) :=
  {h | ∃ f g : List Bool → ℕ, f ∈ SharpP ∧ g ∈ SharpP ∧ ∀ x, h x = (f x : ℤ) - (g x : ℤ)}

/-- `GapP` is closed under negation: swap the two `#P` functions. -/
theorem GapP.neg_mem {h : List Bool → ℤ} (hh : h ∈ GapP) :
    (fun x => -h x) ∈ GapP := by
  obtain ⟨f, g, hf, hg, hval⟩ := hh
  refine ⟨g, f, hg, hf, fun x => ?_⟩
  show -h x = (g x : ℤ) - (f x : ℤ)
  rw [hval x]; ring

end Complexity
