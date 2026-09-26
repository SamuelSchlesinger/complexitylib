/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.EventProb
public import Complexitylib.Classes.NP
public import Complexitylib.Classes.P.Cobham
public import Complexitylib.Classes.P.Composition
public import Complexitylib.Classes.P.Cobham.Internal.ConsBit
public import Complexitylib.Classes.P.Cobham.Internal.FstBlock
public import Complexitylib.Classes.P.Cobham.Internal.Vec
public import Complexitylib.Classes.P.Preimage
public import Complexitylib.Circuits.BitString
public import Complexitylib.Encoding.DataEncode

/-!
# Probabilistically checkable proofs: definitions

`PCP r q` is the class of languages with a probabilistically checkable proof
system: a polynomial-time verifier that, on an input of length `n`, flips
`r n` coins, reads at most `q n` bits of a proof string, always accepts a
correct proof of a member, and rejects every purported proof of a non-member
with probability at least `1/2`. This is the class `PCP[r(n), q(n)]` of
Arora–Barak, Definition 11.5, and of
<https://en.wikipedia.org/wiki/PCP_(complexity)>: "the class of problems for
which a probabilistically checkable proof of a solution can be given, such that
the proof can be checked in polynomial time using `r(n)` bits of randomness and
by reading `q(n)` bits of the proof, correct proofs are always accepted, and
incorrect proofs are rejected with probability at least `1/2`."

As in `Complexitylib.Classes.Interactive`, the verifier is machine-free: its
two computations are a query-selection function in `FP` and a verdict language
in `P`, both applied to encoded tuples. The verifier is *non-adaptive* — the
positions it reads are a function of the input and the coins alone, not of
earlier answers — which is the standard choice (Arora–Barak, Definition 11.5)
and costs only a `2^q` blow-up in query count against the adaptive variant.

## Main definitions

- `PCPVerifier` — query positions as an `FP`-computable function of the encoded
  input and coins, and a verdict in `P` on the input, the coins, and the bits
  read
- `PCPVerifier.Accepts`, `PCPVerifier.acceptEvent`
- `PCP` — the class `PCP[r(n), q(n)]`
- `Constructible` — a resource bound that can be written out in unary

## Main results

- `PCP_mono_queries` — more queries only enlarge the class (monotonicity in the
  number of coins is not proved: the verifier must use exactly `r n` coins)
- `P_subset_PCP` — the definition contains `P` for every `r` and `q`: the
  verifier reads nothing and ignores its coins

## Conventions

The verifier uses *exactly* `r n` coins, never fewer: a verifier wanting fewer
can ignore the surplus, so this loses nothing, and it keeps the coin count a
parameter of the class rather than a field the verifier could smuggle
non-uniform information into. The query count is an upper bound `≤ q n` since
the position list is produced by the `FP` function and carries no hidden
information.

The proof is a finite string; a position beyond its end reads as `false`. This
is no restriction, as the verifier's positions are polynomially many bits long,
so a proof of length `q n · 2 ^ r n` suffices, matching the usual convention.

Completeness `1` and soundness `1/2` are hard-wired, following the
`PCP[r, q]` convention rather than the `2/3`–`1/3` of
`Complexitylib.Classes.Randomized`.

-/

@[expose] public section

namespace Complexity

/-! ## Verifiers -/

/-- A (non-adaptive) PCP verifier: from the encoded input and coins it computes
a list of proof positions in polynomial time, and from the input, the coins, and
the bits found there it decides in polynomial time. -/
structure PCPVerifier where
  /-- The proof positions queried on input `x` with coins `r`. -/
  positions : List Bool → List Bool → List ℕ
  /-- That computation is polynomial-time, as a function of `pair x r` producing
  the `DataEncode` bitstring of the position list. -/
  positions_mem : ∃ f ∈ FP, ∀ x r : List Bool,
    f (pair x r) = DataEncode.bitstringEncode (positions x r)
  /-- The verdict, on `pair (pair x r) a` where `a` lists the bits read. -/
  verdict : Language
  /-- That verdict is polynomial-time decidable. -/
  verdict_mem : verdict ∈ P

namespace PCPVerifier

/-- The bits of the proof `π` at the listed positions; a position past the end
of the proof reads as `false`. -/
def answers (π : List Bool) (ps : List ℕ) : List Bool :=
  ps.map fun i => π.getD i false

/-- The verifier accepts input `x` and proof `π` with coins `r`. -/
def Accepts (V : PCPVerifier) (x π r : List Bool) : Prop :=
  pair (pair x r) (answers π (V.positions x r)) ∈ V.verdict

open Classical in
/-- The coin strings of length `t` on which `V` accepts `x` with proof `π`. -/
noncomputable def acceptEvent (V : PCPVerifier) (t : ℕ) (x π : List Bool) :
    Finset (Fin t → Bool) :=
  Finset.univ.filter fun r => V.Accepts x π (BitString.toList r)

/-- The verifier reads at most `q n` bits of the proof on inputs of length `n`,
whatever its coins. -/
def QueryBounded (V : PCPVerifier) (q : ℕ → ℕ) : Prop :=
  ∀ x r : List Bool, (V.positions x r).length ≤ q x.length

end PCPVerifier

/-! ## The class -/

/-- **`PCP[r(n), q(n)]`**: languages with a polynomial-time verifier using `r n`
random bits and reading at most `q n` bits of the proof, such that a member has
a proof the verifier always accepts, while every proof of a non-member is
rejected with probability at least `1/2`. -/
def PCP (r q : ℕ → ℕ) : Set Language :=
  {L | ∃ V : PCPVerifier, V.QueryBounded q ∧
    (∀ x ∈ L, ∃ π : List Bool, eventProb (V.acceptEvent (r x.length) x π) = 1) ∧
    (∀ x ∉ L, ∀ π : List Bool, eventProb (V.acceptEvent (r x.length) x π) ≤ 1 / 2)}

/-! ## Elementary properties -/

/-- The verifier that reads no bits of the proof, ignores its coins, and
decides `L` on the input it recovers from the encoded view. -/
private noncomputable def inputVerifier (L : Language) (hL : L ∈ P) : PCPVerifier where
  positions _ _ := []
  positions_mem :=
    ⟨fun _ => DataEncode.bitstringEncode ([] : List ℕ),
      constFn_mem_FP _, fun _ _ => rfl⟩
  verdict := (fun z => pairFst (pairFst z)) ⁻¹' L
  verdict_mem := by
    refine mem_P_preimage ?_ hL
    exact mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP

/-- **`P ⊆ PCP[r, q]`** for every `r` and `q`: the verifier never looks at the
proof or its coins. -/
theorem P_subset_PCP (r q : ℕ → ℕ) : P ⊆ PCP r q := by
  intro L hL
  refine ⟨inputVerifier L hL, fun _ _ => by simp [inputVerifier], ?_, ?_⟩
  · intro x hx
    refine ⟨[], ?_⟩
    have hev : (inputVerifier L hL).acceptEvent (r x.length) x [] = Finset.univ := by
      ext ρ
      simp [PCPVerifier.acceptEvent, PCPVerifier.Accepts, inputVerifier, hx]
    rw [hev, eventProb_univ]
  · intro x hx π
    have hev : (inputVerifier L hL).acceptEvent (r x.length) x π = ∅ := by
      ext ρ
      simp [PCPVerifier.acceptEvent, PCPVerifier.Accepts, inputVerifier, hx]
    rw [hev, eventProb_empty]
    norm_num

/-- More queries only enlarge the class. -/
theorem PCP_mono_queries {r q q' : ℕ → ℕ} (hq : ∀ n, q n ≤ q' n) :
    PCP r q ⊆ PCP r q' := by
  rintro L ⟨V, hV, hc, hs⟩
  exact ⟨V, fun x ρ => (hV x ρ).trans (hq _), hc, hs⟩

/-! ## Constructible bounds -/

/-- A resource bound is **constructible** when it can be written out in unary in
polynomial time.

Some such requirement is not optional. `PCP r q` constrains the verifier but says
nothing about `r`, so without it the union below is not a complexity class at
all: `Complexitylib.Classes.PCP.Internal.BoundNotConstructible` proves that for
*every* set `A ⊆ ℕ`, computable or not, the language of inputs whose length lies
in `A` satisfies the `PCP` conditions with `r` the indicator of `A` — a bound
that is `O(1)`, hence `O(log n)`. That puts continuum-many languages in the
union while `NP` is countable, so the unrestricted equation is false. Textbook
statements of the theorem carry the same requirement tacitly, by taking the
bounds to be constructible functions. -/
def Constructible (r : ℕ → ℕ) : Prop :=
  (fun x : List Bool => List.replicate (r x.length) true) ∈ FP

end Complexity
