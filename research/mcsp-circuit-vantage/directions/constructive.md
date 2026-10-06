# Constructive uses of the circuit proofs

[Back to the transfer investigations](index.md).

These are proposed algorithmic obligations, not established efficient algorithms
extracted from the Lean library. Primary sources were checked on 2026-10-06.

**1. Extract a refuter with a resource contract.** For the Gaussian hard family `H_m`, a concrete target is an algorithm `R(m,C)` returning `x` with `C(x) ≠ H_m(x)` whenever `size(C) < L(m)`, with runtime polynomial in `m + |encode(C)|`. A checked existential counterexample lemma supplies correctness of existence, not this algorithm or bound. Exhaustive evaluation takes `2^m` evaluations: polynomial in the truth-table length, but exponential in the represented arity.

The missing step can be sharply localized: construct the region forced by gate elimination, then find a point of the opposite color. Carmosino–Dang–Jackman give a polynomial-time affine refuter producing a constant dimension-`d` subspace for B2 circuits smaller than `3m−4d(m)`; converting this into a refuter for an arbitrary explicit affine disperser uses an NP oracle (Theorem 5, Corollary 6). Thus even strong extractor geometry need not solve witness search [cdj26-refute][cdj26-refute]. Ask whether this library's particular hard family admits efficient opposite-color search on the regions its proof produces.

This remains a refuter for the **inner** family. A refuter for an **outer** MCSP algorithm receives or targets an algorithm on truth tables and must produce a misclassified table. MCSP-specific constructive separations have substantial additional consequences; their resource and uniformity conditions matter [cjsw24][cjsw24] (§4).

**2. Exact cost does not characterize optimal circuits.** The repeated positive-cost anchor's unique completion is an extensional statement about a restricted truth table. It does not classify every optimal circuit computing that table. Carmosino–Dang–Jackman's checker for incorrect DeMorgan XOR circuits of exactly `3(m−1)` binary gates depends on such a classification, beyond the lower bound (Theorem 8) [cdj26-refute][cdj26-refute]. Their STACS paper also proves XOR-Simple Extension is polynomial-time solvable, under both counting and ignoring negations [cdj26-xor][cdj26-xor]. Rigidity can therefore produce an easy extension problem.

A useful missing obligation is a normal-form/recognition theorem for the anchor's optimal witnesses, with the exact gate-cost convention. Even success would concern structured circuit recognition or synthesis; it does not supply a lower bound for unrestricted outer MCSP. The unique-completion restriction itself asks only whether the free bits equal one fixed string.

**3. Formalize the local-generator transfer before proposing a generator.** Let `β = Pr_T[M[n,s](T)=1]`. If every `G(z)` has inner circuit complexity at most `s`, while `G` fools an outer class `C[S]` to error `ε < 1−β`, then `M[n,s] ∉ C[S]`: its acceptance probability is one on generated tables and `β` on uniform tables. This finite fixed-slice deduction is the core of the local-PRG framework [cklm20][cklm20]. A suitable hitting-set generator for dense rejection sets also suffices.

The two outstanding premises are concrete: a circuit-size bound for the index function `j ↦ G(z)_j`, with seed fixed, and fooling of the claimed outer model. Fast whole-output generation or short seed length alone does not establish the first. The existing worst-case linear B2 lower bound and extractor geometry establish neither premise automatically; an NW route additionally needs the appropriate average-case hardness. This transfer theorem would expose the exact gap without suggesting an MCSP improvement already follows.

[cdj26-refute]: ../sources.md#cdj26-refute
[cdj26-xor]: ../sources.md#cdj26-xor
[cjsw24]: ../sources.md#cjsw24
[cklm20]: ../sources.md#cklm20
