/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.EventProb
public import Complexitylib.Classes.P.Composition
public import Complexitylib.Classes.P.Cobham.Internal.FstBlock
public import Complexitylib.Classes.P.Cobham.Internal.SndBlock
public import Complexitylib.Classes.P.Preimage
public import Complexitylib.Circuits.BitString
public import Complexitylib.Encoding.DataEncode
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Interactive proof classes: `MA`, `AM`, and `IP`

⚠️ Unreviewed by Bolton

A verifier here is a *language in `P`* — equivalently a polynomial-time
predicate — applied to the encoded tuple of everything it sees, and its private
coins are a uniformly random point of `Fin t → Bool` measured by `eventProb`.
This keeps the definitions machine-free and auditable, in the style of
`Complexitylib.Classes.NP.Witness`'s use of `pairLang`.

The three classes differ in who speaks when:

- `MA` — Merlin sends a proof `w`, then Arthur flips coins and checks
  `pair (pair x w) r`. The proof cannot depend on the coins.
- `AM` — Arthur flips *public* coins `r` first, then Merlin answers `w`, and
  the check is on `pair (pair x r) w`. Merlin's answer may depend on the coins,
  so the existential sits inside the probability.
- `IP` — a `Protocol` runs a bounded number of rounds: the verifier's next
  message is a polynomial-time function of the input, its private coins and the
  transcript so far, and the prover replies by a `ProverStrategy`, which sees
  the transcript but never the coins. Completeness asks for one strategy that
  convinces the verifier; soundness quantifies over every strategy.

## Main definitions

- `Transcript`, `ProverStrategy`, `Protocol`, `Protocol.transcript`,
  `Protocol.Accepts`, `Protocol.acceptEvent`
- `MA`, `AM`, `IP`

## Main results

- `P_subset_MA`, `P_subset_AM` — the definitions contain `P`, by ignoring the
  proof and the coins

## Conventions

Completeness `2/3` and soundness `1/3` are hard-wired, as in
`Complexitylib.Classes.Randomized`. Message lengths are bounded by
`Protocol.msgLen` — the prover's by `ProverStrategy.Bounded`, which soundness in
`IP` quantifies over, and the verifier's by `Protocol.vmsg_len`. An unbounded
message would blow up the transcript the polynomial-time verifier has to read,
and after polynomially many rounds the verifier would no longer be polynomial in
the input at all. The prover is adaptive — it is a function of the transcript,
not a single witness string.

## TODO

- Embed `MA` into `IP` as a one-round protocol with an empty verifier message.
- Amplification: sequential repetition and the resulting threshold robustness.
- `NP ⊆ MA` through the witness characterization interface.

`IP ⊆ PSPACE` is proved in `Complexitylib.Classes.Containments.IPSubsetPSPACE`.
-/

@[expose] public section

namespace Complexity

/-! ## Merlin–Arthur -/

open Classical in
/-- The coin strings on which the verifier `V` accepts input `x` with proof
`w`. -/
noncomputable def merlinEvent (V : Language) (t : ℕ) (x w : List Bool) :
    Finset (Fin t → Bool) :=
  Finset.univ.filter fun r => pair (pair x w) (BitString.toList r) ∈ V

/-- **MA** (Merlin–Arthur): Merlin sends a polynomially bounded proof, and
Arthur checks it with a polynomial-time predicate and polynomially many private
coins, accepting a member with probability at least `2/3` and a non-member with
probability at most `1/3` whatever the proof. -/
def MA : Set Language :=
  {L | ∃ (p : Polynomial ℕ) (V : Language), V ∈ P ∧
    (∀ x ∈ L, ∃ w : List Bool, w.length ≤ p.eval x.length ∧
      2 / 3 ≤ eventProb (merlinEvent V (p.eval x.length) x w)) ∧
    (∀ x ∉ L, ∀ w : List Bool, w.length ≤ p.eval x.length →
      eventProb (merlinEvent V (p.eval x.length) x w) ≤ 1 / 3)}

/-! ## Arthur–Merlin -/

open Classical in
/-- The public coin strings that Merlin can answer: those admitting a
polynomially bounded reply the verifier accepts. -/
noncomputable def arthurEvent (V : Language) (q t : ℕ) (x : List Bool) :
    Finset (Fin t → Bool) :=
  Finset.univ.filter fun r =>
    ∃ w : List Bool, w.length ≤ q ∧ pair (pair x (BitString.toList r)) w ∈ V

/-- **AM** (Arthur–Merlin): Arthur flips public coins first and Merlin answers
them, so the existential over Merlin's reply sits inside the probability. -/
def AM : Set Language :=
  {L | ∃ (p : Polynomial ℕ) (V : Language), V ∈ P ∧
    (∀ x ∈ L, 2 / 3 ≤ eventProb (arthurEvent V (p.eval x.length) (p.eval x.length) x)) ∧
    (∀ x ∉ L, eventProb (arthurEvent V (p.eval x.length) (p.eval x.length) x) ≤ 1 / 3)}

/-! ## Interactive protocols -/

/-- The messages exchanged so far, in order: the verifier speaks on even
positions and the prover on odd ones. -/
abbrev Transcript := List (List Bool)

/-- A prover strategy: the next message as a function of the visible
transcript. The prover is adaptive and never sees the verifier's coins. -/
def ProverStrategy := Transcript → List Bool

/-- A strategy respects a message-length bound. -/
def ProverStrategy.Bounded (S : ProverStrategy) (m : ℕ) : Prop :=
  ∀ τ : Transcript, (S τ).length ≤ m

/-- The encoded view handed to the verifier: the input, its coins, and the
transcript so far. -/
def protocolView (x r : List Bool) (τ : Transcript) : List Bool :=
  pair (pair x r) (DataEncode.bitstringEncode τ)

/-- An interactive protocol: a round count, a private-coin count, a
message-length bound, the verifier's next message as a polynomial-time function
of the encoded input, coins and transcript, and its final verdict as a
polynomial-time predicate of the same.

`msgLen` bounds *both* sides' messages: the prover's through
`ProverStrategy.Bounded`, the verifier's through `vmsg_len`. Bounding the
verifier is not a convenience — without it the transcript grows by a polynomial
each round, so after polynomially many rounds the view, and with it the
verifier's own running time, is no longer polynomial in the input. -/
structure Protocol where
  /-- Number of rounds, as a function of the input length. -/
  rounds : ℕ → ℕ
  /-- Number of private coins, as a function of the input length. -/
  coins : ℕ → ℕ
  /-- Bound on the length of either side's messages. -/
  msgLen : ℕ → ℕ
  /-- The verifier's next message, computed from `pair (pair x r) ⌜τ⌝`. -/
  vmsg : List Bool → List Bool
  /-- That computation is polynomial-time. -/
  vmsg_mem : vmsg ∈ FP
  /-- The verifier's messages respect the length bound, so the transcript stays
  polynomially long however many rounds are played. -/
  vmsg_len : ∀ (x r : List Bool) (τ : Transcript),
    (vmsg (protocolView x r τ)).length ≤ msgLen x.length
  /-- The verifier's final verdict, on `pair (pair x r) ⌜τ⌝`. -/
  verdict : Language
  /-- That verdict is polynomial-time decidable. -/
  verdict_mem : verdict ∈ P

namespace Protocol

/-- The encoded view handed to the verifier: the input, its coins, and the
transcript so far. -/
abbrev view (x r : List Bool) (τ : Transcript) : List Bool := protocolView x r τ

/-- The transcript after `n` rounds of `prot` on input `x` with coins `r`
against the strategy `S`: each round appends the verifier's message and then
the prover's reply. -/
def transcript (prot : Protocol) (S : ProverStrategy) (x r : List Bool) :
    ℕ → Transcript
  | 0 => []
  | n + 1 =>
      let τ := prot.transcript S x r n
      let v := prot.vmsg (view x r τ)
      τ ++ [v, S (τ ++ [v])]

/-- The verifier accepts the completed interaction. -/
def Accepts (prot : Protocol) (S : ProverStrategy) (x r : List Bool) : Prop :=
  view x r (prot.transcript S x r (prot.rounds x.length)) ∈ prot.verdict

open Classical in
/-- The coin strings on which the verifier accepts against `S`. -/
noncomputable def acceptEvent (prot : Protocol) (S : ProverStrategy) (x : List Bool) :
    Finset (Fin (prot.coins x.length) → Bool) :=
  Finset.univ.filter fun r => prot.Accepts S x (BitString.toList r)

end Protocol

/-- **IP**: languages with an interactive proof system whose round count, coin
count and message lengths are *given by polynomials*. Completeness asks for one
strategy convincing the verifier with probability at least `2/3`; soundness
bounds every length-respecting strategy by `1/3`.

The three counts are polynomials rather than merely polynomially bounded because
a verifier has to *know* them: it must stop after the right number of rounds and
read the right number of coins. An arbitrary polynomially bounded `ℕ → ℕ` need
not be computable at all, and a protocol carrying one would let the class contain
undecidable languages. -/
def IP : Set Language :=
  {L | ∃ (prot : Protocol) (rp cp mp : Polynomial ℕ),
    (∀ n, prot.rounds n = rp.eval n) ∧ (∀ n, prot.coins n = cp.eval n) ∧
    (∀ n, prot.msgLen n = mp.eval n) ∧
    (∀ x ∈ L, ∃ S : ProverStrategy, S.Bounded (prot.msgLen x.length) ∧
      2 / 3 ≤ eventProb (prot.acceptEvent S x)) ∧
    (∀ x ∉ L, ∀ S : ProverStrategy, S.Bounded (prot.msgLen x.length) →
      eventProb (prot.acceptEvent S x) ≤ 1 / 3)}

/-! ## Elementary containments -/

/-- The verifier that ignores the proof and the coins and decides `L` on the
input it can recover from the encoded view. -/
private theorem inputVerifier_mem_P {L : Language} (hL : L ∈ P) :
    (fun z => pairFst (pairFst z)) ⁻¹' L ∈ P := by
  refine mem_P_preimage ?_ hL
  exact mem_FP_comp Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP

/-- **`P ⊆ MA`.** Merlin sends nothing and Arthur ignores his coins. -/
theorem P_subset_MA : P ⊆ MA := by
  intro L hL
  refine ⟨0, (fun z => pairFst (pairFst z)) ⁻¹' L,
    inputVerifier_mem_P hL, ?_, ?_⟩
  · intro x hx
    refine ⟨[], by simp, ?_⟩
    have hev : merlinEvent ((fun z => pairFst (pairFst z)) ⁻¹' L)
        (Polynomial.eval x.length 0) x [] = Finset.univ := by
      ext r
      simp [merlinEvent, Set.mem_preimage, hx]
    rw [hev, eventProb_univ]
    norm_num
  · intro x hx w _
    have hev : merlinEvent ((fun z => pairFst (pairFst z)) ⁻¹' L)
        (Polynomial.eval x.length 0) x w = ∅ := by
      ext r
      simp [merlinEvent, Set.mem_preimage, hx]
    rw [hev, eventProb_empty]
    norm_num

/-- **`P ⊆ AM`.** Arthur's coins are irrelevant and Merlin's answer is empty. -/
theorem P_subset_AM : P ⊆ AM := by
  intro L hL
  refine ⟨0, (fun z => pairFst (pairFst z)) ⁻¹' L,
    inputVerifier_mem_P hL, ?_, ?_⟩
  · intro x hx
    have hev : arthurEvent ((fun z => pairFst (pairFst z)) ⁻¹' L)
        (Polynomial.eval x.length 0) (Polynomial.eval x.length 0) x = Finset.univ := by
      ext r
      simp only [arthurEvent, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact ⟨[], by simp, by simp [Set.mem_preimage, hx]⟩
    rw [hev, eventProb_univ]
    norm_num
  · intro x hx
    have hev : arthurEvent ((fun z => pairFst (pairFst z)) ⁻¹' L)
        (Polynomial.eval x.length 0) (Polynomial.eval x.length 0) x = ∅ := by
      ext r
      simp only [arthurEvent, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false, not_exists]
      intro w
      simp [Set.mem_preimage, hx]
    rw [hev, eventProb_empty]
    norm_num

end Complexity
