#!/usr/bin/env python3
"""Mirror the frontier-method development into `Complexitylib/Circuits/Frontier/`.

Usage (from the repository root):

    python3 scripts/sync_frontier.py /path/to/the-frontier-method [REV]

The source is exported with `git archive` at `REV` (default `HEAD`), so uncommitted work in
the source checkout is never copied. The export is rewritten mechanically:

* modules `Frontier.X` become `Complexitylib.Circuits.Frontier.X`, and the namespace
  `Frontier` becomes `Complexity.Frontier`;
* the upstreaming candidates move to their home directories:
  `Frontier/ForCslib/Program.lean` to `Complexitylib/Cslib/Circuit/Upstream.lean` and
  `Frontier/ForMathlib/X.lean` to `Complexitylib/Mathlib/Frontier/X.lean`;
* names that would collide with existing library declarations are renamed
  (`RENAMES`), and the anchored `PATCHES` fix the library's environment lints;
* the aggregate `Complexitylib/Circuits/Frontier.lean` also imports the library's own
  bridge modules (`OWNED`), which this script never overwrites.

Every previously mirrored file is deleted first, so files removed upstream disappear. A
patch whose anchor is missing aborts the sync: update or drop it after reviewing upstream.
"""

import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET = ROOT / "Complexitylib/Circuits/Frontier"
AGGREGATE = ROOT / "Complexitylib/Circuits/Frontier.lean"
CSLIB = ROOT / "Complexitylib/Cslib/Circuit/Upstream.lean"
MATHLIB = ROOT / "Complexitylib/Mathlib/Frontier"

# Library modules under `TARGET` that are not mirrored from upstream.
OWNED = ["Cutwidth", "Explicit"]

# Declarations renamed to avoid collisions with the rest of the library.
RENAMES = [
    # `Cslib.Circuits.Program.trace_congr` already exists, with a support hypothesis.
    (r"\btrace_congr\b", "trace_congr_of_upstream"),
    # `SimpleGraph.cutFinset` already exists in the cutwidth development.
    (r"cutFinset", "crossingFinset"),
]

# Anchored local edits, as (mirrored path, old text, new text), applied after `RENAMES`.
PATCHES = [
    # Lines lengthened past 100 columns by `RENAMES`.
    ("Complexitylib/Cslib/Circuit/Upstream.lean",
     "`Program.trace_congr_of_upstream`: the value of a wire depends only on the inputs\n"
     "  upstream of it.",
     "`Program.trace_congr_of_upstream`: the value of a wire depends only\n"
     "  on the inputs upstream of it."),
    ("Complexitylib/Mathlib/Frontier/SimpleGraph.lean",
     "`SimpleGraph.crossingFinset S` is the set of edges of a finite simple graph with exactly one "
     "endpoint\nin `S`.",
     "`SimpleGraph.crossingFinset S` is the set of edges of a finite simple graph with exactly\n"
     "one endpoint in `S`."),
    # Unused instance arguments (environment `unusedArguments` linter).
    ('Complexitylib/Circuits/Frontier/AverageCase/Bias.lean',
     '/-- Uniform prediction agreement, normalized by the full input domain. -/\nnoncomputable def agreement [Finite α] (f g : α → Bool) : ℝ :=',
     '/-- Uniform prediction agreement, normalized by the full input domain. -/\nnoncomputable def agreement (f g : α → Bool) : ℝ :='),
    ('Complexitylib/Circuits/Frontier/AverageCase/Bias.lean',
     '/-- If many inputs are unused, an output class is either a thick rectangle or has only\n`q K²` inputs. This is the weighted replacement for the support lemma. -/\ntheorem RectangleBias.abs_sumOn_le_of_dependsOn [Finite ι] [Finite U] [Nonempty U]',
     '/-- If many inputs are unused, an output class is either a thick rectangle or has only\n`q K²` inputs. This is the weighted replacement for the support lemma. -/\ntheorem RectangleBias.abs_sumOn_le_of_dependsOn [Finite ι] [Finite U]'),
    ('Complexitylib/Circuits/Frontier/AverageCase/Pruning.lean',
     'theorem transitionCount_prune_le [Finite ι] [Finite U]',
     'theorem transitionCount_prune_le'),
    ('Complexitylib/Circuits/Frontier/Compiler.lean',
     '/-- No junction feeds itself. -/',
     'omit [Finite O] in\n/-- No junction feeds itself. -/'),
    ('Complexitylib/Circuits/Frontier/Compiler.lean',
     "/-- An edge leaving a junction carries the junction's signal. -/",
     "omit [Finite O] in\n/-- An edge leaving a junction carries the junction's signal. -/"),
    ('Complexitylib/Circuits/Frontier/Compiler.lean',
     'theorem site_eq_some {i : Fin n} {v : Vertex p out} (h : site i = some v) :',
     'omit [Finite O] in\ntheorem site_eq_some {i : Fin n} {v : Vertex p out} (h : site i = some v) :'),
    ('Complexitylib/Circuits/Frontier/Compiler.lean',
     'theorem site_of_reach {i : Fin n} (hi : Reach p out (.input i)) :',
     'omit [Finite O] in\ntheorem site_of_reach {i : Fin n} (hi : Reach p out (.input i)) :'),
    ('Complexitylib/Circuits/Frontier/Compiler.lean',
     '/-- A gate has at most `r` slots when the fan-in is at most `r`. -/',
     'omit [Finite O] in\n/-- A gate has at most `r` slots when the fan-in is at most `r`. -/'),
    ('Complexitylib/Circuits/Frontier/Compiler.lean',
     '/-- Two junctions fed by the same junction are equal. -/',
     'omit [Finite O] in\n/-- Two junctions fed by the same junction are equal. -/'),
    ('Complexitylib/Circuits/Frontier/Compiler.lean',
     '/-- A wire upstream of an output is reachable. -/',
     'omit [Finite O] in\n/-- A wire upstream of an output is reachable. -/'),
    ('Complexitylib/Circuits/Frontier/Compiler.lean',
     '/-- Every reachable wire is upstream of some output. -/',
     'omit [Finite O] in\n/-- Every reachable wire is upstream of some output. -/'),
    ('Complexitylib/Circuits/Frontier/Compiler.lean',
     'theorem card_innerGate_le : Nat.card (InnerGate p out) ≤ p.innerGates.card := by',
     'omit [Finite O] in\ntheorem card_innerGate_le : Nat.card (InnerGate p out) ≤ p.innerGates.card := by'),
    ('Complexitylib/Circuits/Frontier/Compiler.lean',
     '/-- There are at most `r` slots per reachable inner gate; constant gates have none. -/',
     'omit [Finite O] in\n/-- There are at most `r` slots per reachable inner gate; constant gates have none. -/'),
    ('Complexitylib/Circuits/Frontier/Compiler.lean',
     '/-- There are at least as many reachable gates as reachable inner gates. -/',
     'omit [Finite O] in\n/-- There are at least as many reachable gates as reachable inner gates. -/'),
    ('Complexitylib/Circuits/Frontier/Components.lean',
     '/-- A list of all the vertices without repetitions is a layout. -/\nprivate theorem exists_layout_of_list {V : Type*} [Finite V] {L : List V} (hnd : L.Nodup)',
     '/-- A list of all the vertices without repetitions is a layout. -/\nprivate theorem exists_layout_of_list {V : Type*} {L : List V} (hnd : L.Nodup)'),
    ('Complexitylib/Circuits/Frontier/Layouts/Compression.lean',
     '/-- In a final compression of a connected multigraph with at least two blocks, exactly three\nedges leave every block. -/\ntheorem ncard_cut_eq_three (c : Compression G) [Finite E] (hc : c.Final) (hG : G.Connected)',
     '/-- In a final compression of a connected multigraph with at least two blocks, exactly three\nedges leave every block. -/\ntheorem ncard_cut_eq_three (c : Compression G) (hc : c.Final) (hG : G.Connected)'),
    ('Complexitylib/Circuits/Frontier/Layouts/Compression.lean',
     '/-- At most `d log₂ N + d` edges leave the first `r` vertices of a block. -/\ntheorem ncard_cut_take_le [Finite V] [DecidableEq V] [Finite E] (B : c.blocks) (r : ℕ) :',
     '/-- At most `d log₂ N + d` edges leave the first `r` vertices of a block. -/\ntheorem ncard_cut_take_le [Finite V] [DecidableEq V] (B : c.blocks) (r : ℕ) :'),
    ('Complexitylib/Circuits/Frontier/Layouts/MultiCompression.lean',
     'theorem ncard_cut_multiQuotient [Finite E] (T : Set c.blocks) :',
     'theorem ncard_cut_multiQuotient (T : Set c.blocks) :'),
    ('Complexitylib/Circuits/Frontier/Layouts/MultiGraph.lean',
     '/-- The incident-edge union pays once per edge, at most the degree budget per vertex. -/\ntheorem ncard_touching_le [Finite E] {d : ℕ} (hd : G.MaxDegreeLE d) (S : Finset V) :',
     '/-- The incident-edge union pays once per edge, at most the degree budget per vertex. -/\ntheorem ncard_touching_le {d : ℕ} (hd : G.MaxDegreeLE d) (S : Finset V) :'),
    ('Complexitylib/Circuits/Frontier/Reduction.lean',
     '/-- **Frontier demand for any network.** Rectangle-freeness pays for unread inputs;\nno uniqueness of satisfying assignments is needed. -/\ntheorem Network.logb_ncard_accepted_le {V E : Type*} [Finite V] [Finite E]',
     '/-- **Frontier demand for any network.** Rectangle-freeness pays for unread inputs;\nno uniqueness of satisfying assignments is needed. -/\ntheorem Network.logb_ncard_accepted_le {V E : Type*} [Finite E]'),
    ('Complexitylib/Circuits/Frontier/Sweep.lean',
     '/-- At the end everything is revealed and every input of `S` is a peer, so the revealed parts\nare as numerous as `S`. -/\ntheorem ncard_pastSide_length [Finite ι] [Finite U] {x : ι → U} (hx : x ∈ S) :',
     '/-- At the end everything is revealed and every input of `S` is a peer, so the revealed parts\nare as numerous as `S`. -/\ntheorem ncard_pastSide_length {x : ι → U} (hx : x ∈ S) :'),
    ('Complexitylib/Circuits/Frontier/Tree.lean',
     'theorem ncard_inside_root [Finite ι] [Finite U] {x : ι → U} (hx : x ∈ S) :',
     'theorem ncard_inside_root {x : ι → U} (hx : x ∈ S) :'),
    ('Complexitylib/Circuits/Frontier/Tree.lean',
     'theorem exists_critical [Finite ι] [Finite U] {K : ℕ} (hK : 1 < K) (hS : K ≤ S.ncard)',
     'theorem exists_critical {K : ℕ} (hK : 1 < K) (hS : K ≤ S.ncard)'),
    ("Complexitylib/Circuits/Frontier/Layouts/MultiGraph.lean",
     "theorem card_edges_le [Fintype V] [Finite E] {d : ℕ}",
     "theorem card_edges_le [Fintype V] {d : ℕ}"),
    ('Complexitylib/Circuits/Frontier/AdditiveSweep.lean',
     "theorem ncard_pastSide_length [Finite G] {x : G} (hx : x ∈ S) :",
     "theorem ncard_pastSide_length {x : G} (hx : x ∈ S) :"),
    # Missing docstrings (environment `docBlame` linter).
    ('Complexitylib/Circuits/Frontier/AdditiveSweep.lean',
     "  length : ℕ\n  past : ℕ → G → G\n  future : ℕ → G → G\n  emit : ℕ → G → G\n"
     "  message : ℕ → G → M\n",
     "  /-- The number of steps. -/\n  length : ℕ\n"
     "  /-- The contribution of the steps before `t`. -/\n  past : ℕ → G → G\n"
     "  /-- The contribution of the steps from `t` on. -/\n  future : ℕ → G → G\n"
     "  /-- The label emitted at step `t`. -/\n  emit : ℕ → G → G\n"
     "  /-- The message at time `t`, possibly depending on the whole input. -/\n"
     "  message : ℕ → G → M\n"),
    ('Complexitylib/Circuits/Frontier/AdditiveSweep.lean',
     "def peers (t : ℕ) (x : G) : Set G :=",
     "/-- The inputs of `S` sending the same message at time `t` as `x`. -/\n"
     "def peers (t : ℕ) (x : G) : Set G :="),
    ('Complexitylib/Circuits/Frontier/AdditiveSweep.lean',
     "def pastSide (t : ℕ) (x : G) : Set G :=",
     "/-- The past contributions of the peers of `x` at time `t`. -/\n"
     "def pastSide (t : ℕ) (x : G) : Set G :="),
    ('Complexitylib/Circuits/Frontier/AdditiveSweep.lean',
     "def futureSide (t : ℕ) (x : G) : Set G :=",
     "/-- The future contributions of the peers of `x` at time `t`. -/\n"
     "def futureSide (t : ℕ) (x : G) : Set G :="),
    ('Complexitylib/Circuits/Frontier/AdditiveSweep.lean',
     "def transition (t : ℕ) (x : G) : M × M × G :=",
     "/-- The step from time `t`: the old message, the new message, and the emitted label. -/\n"
     "def transition (t : ℕ) (x : G) : M × M × G :="),
    ('Complexitylib/Circuits/Frontier/AdditiveSweep.lean',
     "noncomputable def transitionCount : ℕ :=",
     "/-- The number of distinct transitions realized by `S`, summed over all steps. -/\n"
     "noncomputable def transitionCount : ℕ :="),
    ('Complexitylib/Circuits/Frontier/AdditiveSweep.lean',
     "noncomputable def chargeTime (K : ℕ) (x : G) : ℕ :=",
     "/-- The first time at which the past contributions of the peers of `x` number at least\n"
     "`K`. -/\nnoncomputable def chargeTime (K : ℕ) (x : G) : ℕ :="),
    ("Complexitylib/Circuits/Frontier/Decomposable.lean",
     "structure Decomposable (ι U N : Type*) where\n  scope : N → Set ι\n  root : N\n",
     "structure Decomposable (ι U N : Type*) where\n"
     "  /-- The coordinates each node is about. -/\n  scope : N → Set ι\n"
     "  /-- The root node, whose scope is everything. -/\n  root : N\n"),
    ("Complexitylib/Circuits/Frontier/Decomposable.lean",
     "  gate : N → DecomposableGate N\n  rank : N → ℕ\n  values : (v : N) → Set (scope v → U)\n",
     "  /-- The gate at each node: a leaf, a union of children, or a product of two. -/\n"
     "  gate : N → DecomposableGate N\n"
     "  /-- A rank that decreases from each node to its children. -/\n  rank : N → ℕ\n"
     "  /-- The partial inputs each node accepts, on its scope. -/\n"
     "  values : (v : N) → Set (scope v → U)\n"),
    ("Complexitylib/Circuits/Frontier/Layouts/Local.lean",
     "def disagreements3 (c : Bool)",
     "/-- The number of the three neighbour colours that differ from `c`. -/\n"
     "def disagreements3 (c : Bool)"),
    ("Complexitylib/Circuits/Frontier/Layouts/VertexGaussian.lean",
     "def vertexEvent (q : ℝ) (R : ℕ)",
     "/-- The event that a vertex's score satisfies `p`. -/\ndef vertexEvent (q : ℝ) (R : ℕ)"),
    ("Complexitylib/Circuits/Frontier/Layouts/VertexGaussian.lean",
     "def crossingEvent (q : ℝ) (R : ℕ)",
     "/-- The event that the threshold `t` separates the scores of an edge's endpoints. -/\n"
     "def crossingEvent (q : ℝ) (R : ℕ)"),
    ("Complexitylib/Circuits/Frontier/Layouts/VertexParameters.lean",
     "noncomputable def vertexCorrelation (d : ℕ)",
     "/-- The kernel correlation `2√(d - 1)/d` of adjacent vertices in degree `d`. -/\n"
     "noncomputable def vertexCorrelation (d : ℕ)"),
    ("Complexitylib/Circuits/Frontier/Layouts/VertexParameters.lean",
     "noncomputable def vertexCoefficient (d : ℕ)",
     "/-- The edge-crossing probability `arccos(ρ_d)/π` of Gaussian vertex scores. -/\n"
     "noncomputable def vertexCoefficient (d : ℕ)"),
    ("Complexitylib/Circuits/Frontier/Tree.lean",
     "structure RegionTree (ι N : Type*) where\n  region : N → Set ι\n  root : N\n",
     "structure RegionTree (ι N : Type*) where\n  /-- The inputs of each node's region. -/\n"
     "  region : N → Set ι\n  /-- The root node, whose region is everything. -/\n  root : N\n"),
    ("Complexitylib/Circuits/Frontier/Tree.lean",
     "  left : N → N\n  right : N → N\n  rank : N → ℕ\n",
     "  /-- The left child of a node. -/\n  left : N → N\n"
     "  /-- The right child of a node. -/\n  right : N → N\n"
     "  /-- A rank that decreases at every nonempty child. -/\n  rank : N → ℕ\n"),
    ("Complexitylib/Circuits/Frontier/Tree.lean",
     "extends RegionTree ι N where\n  message : N → (ι → U) → M\n",
     "extends RegionTree ι N where\n"
     "  /-- The message of each node, a function of the whole input. -/\n"
     "  message : N → (ι → U) → M\n"),
    ("Complexitylib/Circuits/Frontier/Tree.lean",
     "def peers (v : N) (x : ι → U)",
     "/-- The inputs of `S` sending the same message at `v` as `x`. -/\n"
     "def peers (v : N) (x : ι → U)"),
    ("Complexitylib/Circuits/Frontier/Tree.lean",
     "def inside (v : N) (x : ι → U)",
     "/-- The restrictions of the peers of `x` at `v` to the region of `v`. -/\n"
     "def inside (v : N) (x : ι → U)"),
    ("Complexitylib/Circuits/Frontier/Tree.lean",
     "def outside (v : N) (x : ι → U)",
     "/-- The restrictions of the peers of `x` at `v` to the complement of its region. -/\n"
     "def outside (v : N) (x : ι → U)"),
    ("Complexitylib/Circuits/Frontier/Tree.lean",
     "def localInputs (v : N) : Set ι",
     "/-- The inputs of the region of `v` in neither child region: those read at `v`. -/\n"
     "def localInputs (v : N) : Set ι"),
    ("Complexitylib/Circuits/Frontier/Tree.lean",
     "noncomputable def transitionCount [Fintype N]",
     "/-- The number of distinct merge transitions realized by `S`, summed over all nodes. -/\n"
     "noncomputable def transitionCount [Fintype N]"),
    ("Complexitylib/Circuits/Frontier/Tree.lean",
     "def erase (hP : P.Coherent) (v : N) (x : ι → U) :\n    TreeFrontier",
     "/-- Delete the peers of `x` at `v` from a coherent tree frontier. -/\n"
     "def erase (hP : P.Coherent) (v : N) (x : ι → U) :\n    TreeFrontier"),
]


def module_path(name):
    """The library path of an upstream module path relative to `Frontier/`."""
    if name == "ForCslib/Program.lean":
        return CSLIB
    if name.startswith("ForMathlib/"):
        return MATHLIB / name.removeprefix("ForMathlib/")
    return TARGET / name


def module_name(path):
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def rewrite(text, modules):
    def imports(match):
        module = match.group(2)
        if module in modules:
            return f"{match.group(1)}import {modules[module]}"
        return match.group(0)

    text = re.sub(r"^((?:public )?)import (\S+)", imports, text, flags=re.M)
    text = re.sub(r"^namespace Frontier\b", "namespace Complexity.Frontier", text, flags=re.M)
    text = re.sub(r"^end Frontier\b", "end Complexity.Frontier", text, flags=re.M)
    text = re.sub(r"^open Frontier\b", "open Complexity.Frontier", text, flags=re.M)
    for pattern, replacement in RENAMES:
        text = re.sub(pattern, replacement, text)
    return text


def main():
    if len(sys.argv) not in (2, 3):
        raise SystemExit(__doc__)
    source = Path(sys.argv[1])
    rev = sys.argv[2] if len(sys.argv) == 3 else "HEAD"
    commit = subprocess.run(["git", "-C", source, "rev-parse", "--short", rev], check=True,
                            capture_output=True, text=True).stdout.strip()
    with tempfile.TemporaryDirectory() as tmp:
        archive = Path(tmp) / "frontier.tar"
        subprocess.run(["git", "-C", source, "archive", "-o", archive, rev, "Frontier",
                        "Frontier.lean"], check=True)
        with tarfile.open(archive) as tar:
            tar.extractall(tmp, filter="data")
        upstream = Path(tmp) / "Frontier"
        names = sorted(p.relative_to(upstream).as_posix() for p in upstream.rglob("*.lean"))
        modules = {"Frontier." + n.removesuffix(".lean").replace("/", "."):
                   module_name(module_path(n)) for n in names}
        for path in TARGET.rglob("*.lean"):
            if path.relative_to(TARGET).with_suffix("").as_posix() not in OWNED:
                path.unlink()
        if MATHLIB.exists():
            shutil.rmtree(MATHLIB)
        for name in names:
            destination = module_path(name)
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(rewrite((upstream / name).read_text(), modules))
        aggregate = rewrite((Path(tmp) / "Frontier.lean").read_text(), modules)
    owned = "".join(f"public import Complexitylib.Circuits.Frontier.{m}\n" for m in OWNED)
    aggregate = re.sub(r"(\n(?:public import .*\n)+)", lambda m: m.group(1) + owned, aggregate,
                       count=1)
    AGGREGATE.write_text(aggregate)
    for relative, old, new in PATCHES:
        path = ROOT / relative
        text = path.read_text()
        if text.count(old) != 1:
            raise SystemExit(f"patch anchor not found exactly once in {relative}:\n{old}")
        path.write_text(text.replace(old, new))
    for path in TARGET.rglob("*"):
        if path.is_dir() and not any(path.iterdir()):
            path.rmdir()
    print(f"mirrored {len(names)} modules from the-frontier-method {commit}")


if __name__ == "__main__":
    main()
