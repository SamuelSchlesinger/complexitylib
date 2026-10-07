# Reduction ledger

[Return to the argument](index.md).

The class equalities need one uniformly enumerable family of short environments,
mostly accurate at the specified start, with a total logspace evaluator on every
environment. The following reductions preserve that contract. They simplify
OpenAI's proposed proof; they do not independently verify its central estimates
or implementation certificates. Section and theorem numbers refer to the pinned
manuscript [oai26][oai26].

1. **Fix `H=4, h₀=2`.** A rank channel becomes the affine line
   `a(y)=a₀+by` in `F_P⁴`, with `a₀` uniform and the vector `b≠0` uniform.
   General frame notation disappears. Retention rates become `16⁻ᵏ`; entries
   shrink by `16` per stage, against active-count growth at most `2`.
   Lemma 3.1 still supplies marginal, conditional-pair, count, and suffix
   invariance bounds. Conditioning on `b≠0` does **not** preserve unrestricted
   pairwise independence; retain the lemma's conditional bounds. The prime must
   still exceed all identifiers and cover every requested retention scale.

2. **Carry vectors instead of cumulative matrix products.** Maintain
   `h=W+Ch`, with `0≤h≤1`. Replacing `C` by `D=C−E+EC` and `W` by
   `W+EW` preserves the identity. Under the weighted projection `Pʳ`, set
   `h⁺=Pʳh` and `W⁺=Pʳ(W+EW)`; the intertwining
   `C⁺Pʳ=PʳD` gives the next invariant. Primary copies preserve `h`.
   Nonnegativity then gives `0≤W≤h≤1`. This replaces the cumulative
   matrices of Proposition 4.7, preserving the error `|V₀|8⁻ˡ`.
   A further safe simplification defines the initial `h` by backward induction
   on time, eliminating inverse-matrix notation entirely. These are semantic
   targets, not algorithms for evaluating their coordinates.

3. **Keep active support distinct from the domain.** Proposition 4.5 doubles
   only the vertices incident to positive transition entries. The full domain
   still grows as `|V₀|D₀ˡ`, with `D₀>16`. Using that full count in the
   residual bound would give `|V₀|(D₀/16)ˡ`, destroying decay. Conversely, deleting
   inactive addresses is no free algorithmic simplification: the estimator and
   its integrated norms use the prescribed domain and uniform address scheme.

4. **Vote instead of computing a median.** With error below `1/8`, thresholds
   `1/4` for RL and `1/2` for BPL work directly. Constant output precision
   suffices: eight fractional places of digits in `{-6,…,6}` leave tail
   `6·2⁻⁸<1/32`. Statistical precision remains different. Lemma 12.2 loses a
   factor `N=2^O(B)` when extracting the specified start from Theorem 9.8's
   averaged eighth moment. Its bound requires choosing
   `p≥(log₂N)/8+O(1)`, hence an `O(B)` budget even for constant final accuracy.
   Enumerate raw salt strings with their multiplicities; deduplicating equal
   fingerprints changes the probability law.

5. **Use one final potential, after proving local bounds.** Once every physical
   segment satisfies `ℓ≤A(w−w′)+D(t−j)`, including neighbor-state copies,
   `Φ(w,t)=Aw+Dt` telescopes. Because `ℓ≥0` and `D>0`, it also bounds every
   descendant clock. The final presentation can omit the separate `Ψ`
   invariant. It cannot omit the overshoot bound: §10 and Lemmas 11.4 and 11.10
   use it to choose common coefficients, including when `j>t`. Saving a full
   cursor or tuple at each nested call would invalidate this accounting.
   The single environment, cursor, catalyst, and scratch area remain charged.

6. **Keep the conditional sampler's implementation contract.** An unconditional
   expander does not supply averaging on a retained slice. Lemmas 6.1–6.3
   provide a uniform conditional gap and identifier-independent variants that
   preserve the full environment law before endpoint tests. Exactly one wrap
   variant survives per walk word; its weight is the word's original weight.
   Averaging uniformly over guessed wraps would change the estimator. The
   finite-action gap remains an external mathematical dependency through §6's
   stated group-theoretic inputs.

7. **Keep structural ports and the actual estimator.** Zero-weight exposed
   ports still affect candidates, fingerprints, and incoming enumeration.
   Lemma 5.6's witnesses equal one there, and its incoming cap includes them;
   §9.3 charges escaped candidates even when their increments vanish. Deleting
   these ports needs a new proof. Likewise, Theorem 11.1 must evaluate the
   **same** estimator bounded by Theorem 9.8. Requested numerical precision
   cannot alter structural domains, salt visibility, port order, or tie rules.
   Exact-stream arithmetic and concrete recipe certificates remain essential.

8. **Drop downstream consequences, retain uniform totality.** Variable-precision
   approximation, accepting-path extraction, and the effective compiler
   (§§12.4–12.5 and 13) are unnecessary for these class equalities. The fixed
   machine's uniform evaluator is still necessary. Its well-founded allowance
   construction must terminate on inaccurate environments and synthetic
   predecessor probes: one looping evaluation defeats exhaustive voting.
   Direct RL and BPL decisions give the two inclusions; ignoring randomness
   gives the reverse inclusions. Complementing a total deterministic decider
   then gives `coRL=L`. Language equality `RL=L` alone supplies no derivation
   here of `BPL=L`.

The unresolved verification burden is therefore concentrated in §§5–11:
conditional normalization, compression and adaptive fingerprint bounds, and a
total evaluator whose complete live storage obeys the certificates. This ledger
removes surrounding generality without replacing those obligations.

[oai26]: sources.md#oai26
