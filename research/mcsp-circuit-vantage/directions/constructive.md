# Constructive uses of the circuit proofs

[Back to the transfer investigations](index.md).

Status labels distinguish checked library theorems, paper deductions, and open
algorithmic targets. Primary sources were checked on 2026-10-06.

**1. Separate randomized and deterministic refutation.** Let `E_m` be the
**unpadded** `Algebraic.Cutwidth.Extractor.sourceReductionFamily m`, and put
`L=1+π/(3 arccos((1+2√2)/4))≈4.5625`.

**Checked.** `Complexity.Frontier.sourceReductionFamily_agreement_le` states:
for every `ε>0` there is `γ>0` such that, for all sufficiently large `m`, every
fan-in-two Boolean circuit `C` with at most `(L−ε)m` positive-arity gates satisfies

`Pr_x[C(x)=E_m(x)] ≤ 71/72 + 2^(−γm)`.

The theorem is in [Frontier/Explicit.lean](../../../Complexitylib/Circuits/Frontier/Explicit.lean#L191).
The checked `sourceReductionFamilyEval_mem_FP`, together with
`sourceReductionFamilyEval_ofFn`, supplies a polynomial-time evaluator for this
same raw family in [Construction/Uniform.lean](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Extractor/SourceReduction/Construction/Uniform.lean#L49).
These declarations concern `E_m`; the balanced `sourceReductionHardFamily`
is a different family [complexitylib26][complexitylib26].

**Paper deduction: a randomized refuter.** Fix `ε>0`. Eventually
`2^(−γm)≤1/144`, so every circuit in the stated size regime has error at least
`1/144` against `E_m`. Given an explicitly encoded fan-in-two circuit, sample
`t` independent uniform `m`-bit strings, evaluate `C` and the raw-family evaluator,
and return the first disagreement. Every returned witness is checked directly.
The probability of returning no witness is at most `(143/144)^t`; for
`0<δ<1`, taking `t=ceil(log(1/δ)/log(144/143))` makes this at most `δ`.
The runtime is polynomial in `m+|encode(C)|+t`, hence polynomial in
`m+|encode(C)|+log(1/δ)`. This is a paper algorithm for the raw family in its
eventual size regime, rather than an extracted implementation.

**Open deterministic target.** Find a deterministic algorithm returning such a
disagreement in polynomial time. Exhaustive evaluation uses `2^m` trials.
The Gaussian proof uses graph layouts and frontier demand/supply. Extracting a
deterministic refuter from it requires efficient construction of the structural
witness and the subsequent search, with a resource contract for each step.

Carmosino–Dang–Jackman illustrate a different mechanism: gate elimination gives
a polynomial-time affine refuter finding a dimension-`d(m)` subspace on which a
B2 circuit of size less than `3m−4d(m)` is constant (Theorem 5). Their conversion
to a refuter for an explicit affine disperser of dimension `o(m)` uses an NP
oracle to find an opposite-color point (Corollary 6). This illustrates the gap
between constructing a region and searching inside it; it does not identify
the witness structure of the Gaussian frontier proof [cdj26-refute][cdj26-refute].

Refuting the **inner** family and refuting an **outer** MCSP algorithm are
separate tasks. The latter must produce a misclassified truth table.
MCSP-specific constructive separations have substantial additional consequences;
their resource and uniformity conditions matter [cjsw24][cjsw24] (§4).

**2. Exact cost does not characterize optimal circuits.** The repeated
positive-cost anchor's unique completion is an extensional statement about a
restricted truth table. It does not classify every optimal circuit computing
that table. Carmosino–Dang–Jackman's checker for incorrect DeMorgan XOR circuits
of exactly `3(m−1)` binary gates depends on such a classification, beyond the
lower bound (Theorem 8) [cdj26-refute][cdj26-refute]. Their STACS paper also proves
XOR-Simple Extension is polynomial-time solvable, under both counting and
ignoring negations [cdj26-xor][cdj26-xor]. Rigidity can therefore produce an easy
extension problem.

A useful missing obligation is a normal-form/recognition theorem for the anchor's
optimal witnesses, with the exact gate-cost convention. Even success would
concern structured circuit recognition or synthesis; it does not supply a lower
bound for unrestricted outer MCSP. The unique-completion restriction itself
asks only whether the free bits equal one fixed string.

**3. Formalize the local-generator transfer before proposing a generator.**
Let `β=Pr_T[M[n,s](T)=1]`. If every `G(z)` has inner circuit complexity at most
`s`, while `G` fools an outer class `C[S]` to error `η<1−β`, then
`M[n,s]∉C[S]`: its acceptance probability is one on generated tables and `β`
on uniform tables. This finite fixed-slice deduction is the core of the local-PRG
framework [cklm20][cklm20]. A suitable hitting-set generator for dense rejection
sets also suffices.

The two outstanding premises are a circuit-size bound for the index function
`j↦G(z)_j`, with seed fixed, and fooling of the claimed outer model. Fast
whole-output generation or short seed length alone does not establish the first.
The checked average-case theorem above does not directly establish the second.

For a concrete comparison, the NW hybrid argument turns a constant-advantage
distinguisher on `N` output bits into a predictor for its `m`-bit hard function,
guaranteeing only an `Ω(1/N)` advantage over agreement `1/2`. This guarantee is
compatible with the library's upper bound `71/72+2^(−γm)`.
There is also a size gap: CKLM Theorems 39–40 require
hardness against the reconstruction class `C∘DNF_a` at size `S+N·2^a`, where
`a` bounds design intersections. This includes the outer distinguisher size `S`.
In the short-input regime `m=o(N)` and `S≥N`, the available linear bound does
not cover that required reconstruction size. Both prediction advantage and
reconstruction size must match before the theorem can yield a contradiction
[cklm20][cklm20].
Hardness amplification or a different generator could alter this comparison;
its quantitative loss and the inner index-function cost would need new proofs.

[cdj26-refute]: ../sources.md#cdj26-refute
[cdj26-xor]: ../sources.md#cdj26-xor
[cjsw24]: ../sources.md#cjsw24
[cklm20]: ../sources.md#cklm20
[complexitylib26]: ../sources.md#complexitylib26
