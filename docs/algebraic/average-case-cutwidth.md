# The average-case `(4 - ε) n` bound: proof sketch and formal plan

**Status.** Paper proof, written before formalization; formalized on
2026-09-26 in `Algebraic.LowerBound.Cutwidth.{Direction, Balanced, AverageCase}`
with no `sorry` and only the standard axioms. The formal statement is
`Cutwidth.eventually_card_agree_le_of_pathwidthBound` (pathwidth hypothesis)
and `Cutwidth.eventually_card_agree_le` (ordering hypothesis), with fixed-`n`
core `card_agree_le_of_bounds`; see the section *Formal statement* at the end.
Every step below is stated in the vocabulary of `Algebraic.LowerBound.Cutwidth`
so that the Lean development can be read against it line by line. The claim is *not* a consequence of the worst-case
cut-counting lemma: inputs whose past set is still small at a node sit in thin
rectangles on which a balanced function is unconstrained, and the K² charging
gives nothing there. The proof below uses the circuit's direction instead.

## Statement

A function `f : {0,1}ⁿ → {0,1}` is `(K, ν)`-balanced when for every split
`U` of the coordinates and every rectangle `P × Q` with `|P| ≥ K` and
`|Q| ≥ K`,

    (1/2 − ν)|P||Q| ≤ |{(p, q) ∈ P × Q : f(p, q) = 1}| ≤ (1/2 + ν)|P||Q|.

Li's sumset extractor with error `ν` is `(n^c, ν)`-balanced for the same
reason it is rectangle-free: a rectangle with both sides at least `K = n^c`
is the XOR of two independent sources of min-entropy `c log n`.

**Theorem (average case).** Assume the graph-ordering hypothesis. Let `f n`
be `(K n, ν)`-balanced with `K n ≤ n^c`. Then for every `ε > 0` there is
`δ > 0` such that for all large `n`, every circuit `g` with at most
`(4 − ε) n` gates satisfies

    |{x : g(x) = f n (x)}| ≤ (1/2 + 3ν) 2ⁿ + 2^{(1 − δ) n}.

## Ingredients

Throughout, `p`, `out` is a circuit with output gate `out`; `N` is its wiring
network; `α_x := traceAssignment p out x` is the unique satisfying assignment
of an accepted `x` (`eq_trace_of_satisfies`). Fix a lower set `L` of the
vertex order. Write `past(L)` for the variables read in `L`, `C(L)` for the
cut, and split the cut by direction:

    F(L) = {e ∈ C(L) : fst e ∈ L}     forward: produced inside, consumed outside
    B(L) = {e ∈ C(L) : snd e ∈ L}     backward: produced outside, consumed inside

**Lemma 1 (determination).** Let `α = α_x`, `α' = α_{x'}` be trace
assignments. If `x, x'` agree on `past(L)` and `α, α'` agree on `B(L)`, then
`α, α'` agree on every edge with an endpoint in `L`. Applied to the complement
of `L`: if `x, x'` agree outside `past(L)` and `α, α'` agree on `F(L)`, then
`α, α'` agree on every edge with an endpoint outside `L`.

*Proof.* All edges of a signal carry the signal's value
(`eq_firstOut_of_satisfies`), so it suffices to show `α, α'` agree on the
value of every signal `w` that has an edge touching `L`. Induct on the wire
index of `w`. If some edge of `w` lies in `B(L)`, done by hypothesis. If no
edge of `w` crosses the cut, then, the edges of `w` forming a connected tree
through its signal vertex, all of them lie inside `L`, so the signal vertex is
in `L`: for an input, its variable is in `past(L)`; for a gate, its two slot
edges have their consumer in `L`, so the slot signals have edges touching `L`
and smaller index, and the gate's value is its operation on theirs. If some
edge of `w` is forward-crossing and none is backward-crossing, walk the copy
chain from the signal vertex to the forward edge's tail: every chain edge is
non-crossing (else backward), so the signal vertex is in `L` and the previous
case applies. ∎

**Lemma 2 (rectangles of one circuit).** For `σ ∈ Σ := {α_x|C(L) : x accepted}`
let `R_σ := {x accepted : α_x|C(L) = σ}`. Then

  (a) the `R_σ` partition the accepted set;
  (b) `R_σ = pastSet(L, σ) × futureSet(L, σ)` via `glue` (gluing plus
      uniqueness of the satisfying assignment);
  (c) for every future assignment `q`, at most `2^{|F(L)|}` elements `σ ∈ Σ`
      have `q ∈ futureSet(L, σ)`;
  (d) for every past assignment `p`, at most `2^{|B(L)|}` elements `σ ∈ Σ`
      have `p ∈ pastSet(L, σ)`.

*Proof of (c).* If `q ∈ futureSet(L, σ) ∩ futureSet(L, σ')` and
`σ|F = σ'|F`, pick `p ∈ pastSet(L, σ)`, `p' ∈ pastSet(L, σ')` (nonempty since
`σ, σ'` are realized). By (b), `glue p q ∈ R_σ` and `glue p' q ∈ R_σ'`; the
two inputs agree outside `past(L)` and their traces agree on `F(L)`, so by
Lemma 1 for the complement they agree on `C(L)`: `σ = σ'`. Hence
`σ ↦ σ|F` is injective on `{σ ∈ Σ : q ∈ futureSet(L, σ)}`. (d) is symmetric. ∎

**Lemma 3 (one-sided count).** Let `A` be the accepted set of the circuit and
`f` be `(K, ν)`-balanced. Then

    |A ∩ f⁻¹(1)| ≤ (1/2 + ν)|A| + (K − 1)(2^{n − |past(L)| + |F(L)|} + 2^{|past(L)| + |B(L)|}).

*Proof.* Sum over the partition (a). A rectangle with both sides at least
`K` contributes at most `(1/2 + ν)|R_σ|` by balance, taking `U = past(L)`.
A rectangle with `|pastSet| < K` has size at most `(K − 1)|futureSet(L, σ)|`,
and summing `|futureSet(L, σ)|` over such `σ` counts pairs `(σ, q)`, at most
`2^{n − |past(L)|}` choices of `q` times `2^{|F(L)|}` by (c). Symmetrically
for `|futureSet| < K` using (d). ∎

**Lemma 4 (a good layer).** Write `a(L) = |past(L)| − |F(L)|` and
`c(L) = (n − |past(L)|) − |B(L)|`, so `a(L) + c(L) = n − |C(L)|`. Along the
prefixes `L_i` of the order, `a` starts at `0`, ends at `n' ≥ n − k` (the
inputs read), and changes by at most `4` per step, since a vertex reads at
most one variable and has at most three edges. Let `L` be the first prefix
with `a(L) ≥ δ n`; then `a(L) < δ n + 4` and

    c(L) = n − |C(L)| − a(L) ≥ n − w − δ n − 4,

where `w` bounds every cut. With `s ≤ (4 − ε) n`, `n' > n − k`, and the
ordering bound `w ≤ (1/3 + η)(s − n') + 3 log₂|V| + C`, one has
`n − w ≥ (ε/3 − 3η) n − O(log n)`, so `δ = ε/12` and `η ≤ ε/36` give
`c(L) ≥ δ n` for large `n`. ∎

**Assembly.** Lemma 3 at the layer of Lemma 4 gives

    |A ∩ f⁻¹(1)| ≤ (1/2 + ν)|A| + 2(K − 1) 2^{n − δ n + 4}.

Agreement is `|A ∩ f⁻¹(1)| + |Aᶜ ∩ f⁻¹(0)| = 2ⁿ − |A| − |f⁻¹(1)| + 2|A ∩ f⁻¹(1)|`,
and `|f⁻¹(1)| ≥ (1/2 − ν) 2ⁿ` by balance on the whole cube (split at
`⌈log₂ K⌉` coordinates), so

    agreement ≤ (1/2 + 3ν) 2ⁿ + 4(K − 1) 2^{n − δ n + 4} ≤ (1/2 + 3ν) 2ⁿ + 2^{(1 − δ/2) n}

for large `n`, using `K ≤ n^c`. The output-is-an-input case has `g` a
literal, which agrees with `f` on at most `(1/2 + ν) 2ⁿ + 2K 2^{n−1}/2^{...}`;
more simply, a literal is a large rectangle pair and balance applies directly.

## What the Lean development needs

1. `Balanced f K ν` (`Rectangle.lean`), and `card_accepting_ge` from balance
   on the whole cube.
2. `Wiring.trace_agree_of_agree_backward`: Lemma 1, by strong induction on
   the wire index, reusing `eq_firstOut_of_satisfies` and `eq_trace_of_satisfies`.
3. `Network.card_accepting_inter_le` (Lemma 3) for a network with unique
   satisfying assignments and the two determination properties as
   hypotheses, so that the counting is independent of the circuit model.
4. `exists_good_prefix` (Lemma 4) on a linearly ordered vertex type with the
   per-step bounds `|past(upto v)| ≤ |past(below v)| + 1` and
   `|F(upto v)| ≤ |F(below v)| + 3`.
5. The assembly, reusing `eventually_mul_logb_add_lt` and
   `Nat.eventually_mul_pow_le_pow`.

## Formal statement

The Lean theorem is slightly sharper than the sketch above and fixes the
constants:

    theorem eventually_card_agree_le_of_pathwidthBound
        (pathwidth : ∀ ξ > 0, ∃ N₀, PathwidthBound ξ N₀)
        (f : ∀ n, BooleanFunction n) (K : ℕ → ℕ) (c : ℕ) (hν : 0 ≤ ν)
        (hK : ∀ᶠ n, K n ≤ n ^ c) (hbal : ∀ᶠ n, Balanced (f n) (K n) ν) (hε : 0 < ε) :
        ∀ᶠ n, ∀ circuit : Circuit Binary.signature n 1, circuit.size ≤ (4 - ε) n →
          |{x : circuit.eval x 0 = f n x}| ≤ (1/2 + 3ν) 2ⁿ + 2 ^ ((1 - ε/24) n)

Parameters used in the proof: the ordering slack is `η = ε/36`, the
good-prefix threshold is `t = ⌈ε n / 12⌉`, and the numeric condition on `n` is
`(2c + 3) log₂ n + (C + 24) < ε n / 24`, which
`eventually_mul_logb_add_lt` discharges for large `n`. For `ε > 4` no circuit
has size at most `(4 - ε) n`, so the statement holds vacuously; the fixed-`n`
theorem `card_agree_le_of_bounds` assumes `ε ≤ 4`.

How the sketch maps to the modules:

| Sketch | Lean |
|---|---|
| Lemma 1 (determination) | `Wiring.trace_eq_of_agree_backward` in `Direction`; the wiring instances `network_forwardDetermined`, `network_backwardDetermined`, `network_unambiguous` in `AverageCase` |
| Lemma 2 and 3 (one-sided count) | `Network.card_accepting_inter_le` in `Balanced`, for any network with the three properties |
| Lemma 4 (good layer) | `exists_good_prefix` (generic, over `P = |past|` and `F = |forward cut|`), with the step bounds `Network.card_past_upto_le`, `Network.card_fwdCut_below_le`, `Wiring.card_past_upto_le` |
| few inputs read | `card_agree_le_of_dependsOnlyOn` (subcube refinement by `⌈log₂ K⌉` free coordinates) |
| whole-cube balance | `card_accepting_bounds_of_balanced` |
| numeric core | `thin_mass_le` |
| assembly | `card_agree_eq`, `card_agree_le_of_bounds`, `eventually_card_agree_le`, `eventually_card_agree_le_of_pathwidthBound` |

The one-sided count is stated for an arbitrary constraint network with
unique satisfying assignments and the two determination properties, so a
different compiler target can reuse it by supplying those three facts.
