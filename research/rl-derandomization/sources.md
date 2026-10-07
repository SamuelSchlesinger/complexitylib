# Sources

[Return to the argument](index.md).

The manuscript is the source of the proposed derandomization construction.
The other papers supply the external mathematics or explain explicitly named
antecedents. This exposition's reductions are identified where they are used;
neither the exposition nor its finite checks certify the full manuscript.

<a id="oai26"></a>
## oai26

OpenAI. *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
Preprint, September 23, 2026, 108 pages.
[Pinned manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Derandomization-of-Logarithmic-Space-L-equals-RL-equals-BPL-September-23-2026/paper.pdf)
and [LaTeX sections](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Derandomization-of-Logarithmic-Space-L-equals-RL-equals-BPL-September-23-2026/build/sections),
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, inspected October 7, 2026.
The [source manifest](data/source-manifest.json) records byte counts, Git blob
identities, and SHA-256 hashes of the PDF and all 13 section files.

The configuration reduction is Lemma 2.1; the sampler is Lemma 3.1 and
Lemmas 6.1–6.3; the exact hierarchy is Section 4; the estimator and its
adaptive error bounds occupy Sections 5 and 7–9, culminating in Theorem 9.8.
Sections 10–11 implement that estimator, culminating in Theorem 11.1.
Section 12 extracts the specified start and the complexity-class consequences.
Our decision-only reductions omit the subsequent approximation, path recovery,
and compiler consequences.

<a id="shalom99"></a>
## shalom99

Yehuda Shalom. “Bounded generation and Kazhdan's property (T).”
*Publications Mathématiques de l'IHÉS* **90** (1999), 145–168.
[DOI: 10.1007/BF02698832](https://doi.org/10.1007/BF02698832).
[Publisher-hosted record and paper](https://numdam.org/item/PMIHES_1999__90__145_0/).

Theorem 2.1 (p. 152) supplies relative property (T), and Theorem 2.6
(p. 156) supplies property (T) for the relevant special linear group.
The manuscript's Lemma 6.1 combines these to obtain the uniform gap for
its specific affine generators. Shalom's paper does not itself state the
derandomization construction.

<a id="cook87"></a>
## cook87

Stephen A. Cook and Pierre McKenzie. “Problems Complete for Deterministic
Logarithmic Space.” *Journal of Algorithms* **8** (3), 385–394, 1987.
[DOI: 10.1016/0196-6774(87)90018-6](https://doi.org/10.1016/0196-6774(87)90018-6).
[Author-hosted paper](https://www.cs.toronto.edu/~sacook/homepage/cook_mckenzie.pdf).

Proposition 1 (p. 387) supplies the forest permutation used for contour
traversal. The manuscript's incoming-access construction additionally needs
its own program-state, guard, and storage certificates.

<a id="buhrman14"></a>
## buhrman14

Harry Buhrman, Richard Cleve, Michal Koucký, Bruno Loff, and Florian Speelman.
“Computing with a Full Memory: Catalytic Space.” *Proceedings of STOC 2014*,
857–866. [DOI: 10.1145/2591796.2591874](https://doi.org/10.1145/2591796.2591874).
[CWI publication record](https://ir.cwi.nl/pub/22659).

This is the antecedent for computation that restores arbitrary initial
workspace contents. The manuscript's four-visit fingerprint comparison and
its recursive contracts are attributed to the manuscript itself; its
entire shared vector is charged to the claimed space bound.
