# Complexitylib blueprint

The blueprint is the library's map: what is formalized, what is planned, and
how the pieces depend on each other. It is written in LaTeX with
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) and published
at <https://samuelschlesinger.github.io/complexitylib/blueprint/>.

## Building

```bash
pip install leanblueprint            # needs graphviz for the dependency graph
cd blueprint && leanblueprint web    # HTML in blueprint/web/
leanblueprint pdf                    # PDF in blueprint/print/ (needs xelatex)
lake env lean scripts/BlueprintCheck.lean   # every \lean{...} name exists
```

## Conventions

Each chapter in `src/chapters/` covers one area. A node is a `definition`,
`lemma`, `proposition`, `theorem`, or `corollary` environment.

- **Formalized nodes** carry `\lean{Complexity.Name}` (comma-separated when
  several declarations realize the node) and `\leanok`. A formalized theorem's
  proof environment also carries `\leanok`. `scripts/BlueprintCheck.lean`
  fails if any `\lean` name is missing from the library.
- **Planned nodes** carry neither `\lean` nor `\leanok`. Add `\notready` when a
  prerequisite is not yet stated.
- **Dependencies** use `\uses{label, ...}`: in a statement for the definitions
  it mentions, in a proof for the results it applies.
- **Labels** are `def:`, `lem:`, `prop:`, `thm:`, or `cor:` followed by a slug.
  Shared definitions such as `def:P` or `def:NP` are owned by one chapter;
  every other label is prefixed by its chapter, for example `thm:space-savitch`.
- **Honesty.** A result proved under a hypothesis is stated as the
  implication, with the hypothesis explicit, and its unconditional form is a
  separate planned node. Nothing is marked `\leanok` unless the Lean
  declaration states exactly what the node says.
- **Granularity.** Nodes are headline results, the definitions they need, and
  the intermediate results a contributor would reuse. Proof internals stay out.
