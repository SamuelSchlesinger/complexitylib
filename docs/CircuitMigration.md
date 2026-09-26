# Moving the circuit developments to CSLib's circuit model

Status (2026-09-26): phase 1 and the start of phase 2 are done:

- step 0: the build moves to the CSLib integration branch (commit `00f41e9`),
  and typed circuits translate to CSLib straight-line programs with the same
  function and size (`Circuit.toStraightLine`, `eda4781`);
- step 2.1: the basis and typed-circuit definitions are split
  (`Circuits/Basis/Defs`, `Circuits/Typed/Defs`, `d2bc6fe`);
- step 2.2: `Complexitylib/Cslib/Circuit` extends CSLib circuits with gated
  outputs (`Circuit.GatedOutputs`, `Wire.IsGate`) and the program helpers
  moved from the depth bridge, and the duplicated wire translations give way
  to `Wire.index` and `StraightLine.wireOfIndex` (`2c937a3`).

Steps 2.3 onward are open unless a commit on `circuit-migration` says
otherwise. `ROADMAP.md` item 7 gives the phases; this note is the detailed
plan for phases 2 and 3.

CSLib is pinned to commit `2a4389b` of the `complexitylib-integration` branch
of `SamuelSchlesinger/cslib` (tagged `complexitylib-2a4389b` so it stays
reachable), which integrates the pending CSLib circuit PRs until they land
upstream.

The design redefines Complexitylib's measures and `CircuitFamily` over CSLib
circuits on `Basis.signature`. The invariant `GatedOutputs` (every output is
an internal gate) reproduces the typed size charge exactly, so every public
statement keeps its text and meaning, and `emptyOutput` stays.

## 0. Decisions at a glance

1. **Complexitylib's names become definitions over CSLib circuits, not aliases.**
   - Redefined: `Realizable`, `realizationSizes`, `sizeComplexityWithTop`, `sizeComplexity` and `CircuitFamily` (with `function`, `size`, `depth`).
   - Text unchanged, meaning carried by the new family: every class (`SIZEWithBasis`, `SIZE`, `PPoly`, `DEPTHWithBasis`, `DEPTH`, `NC`/`AC`/`TC`, `NC0`/`NC1`/`AC0`/`TC0`, `UniformPPoly`, `PromiseSIZEWithBasis`).
   - CSLib's `ecomplexity`, `complexity`, `Boolean.SIZE`, `Boolean.PPoly`, `CircuitFamily` and `DecidableInSize` stay reference notions, connected by theorems.
2. **Counted output gates → `Cslib.Circuits.Circuit.GatedOutputs`.** "Every output is an internal gate" is exactly the typed charge, for every basis, with no copy-gate hypothesis. `max 1 ∘ ecomplexity` is a theorem, not the definition.
3. **Free negations** are carried by the signature: an operation symbol is a whole `Basis.GateKind`. Nothing needs converting.
4. **`emptyOutput` and `[NeZero N]` stay.** ROADMAP item 7's claim that zero-input circuits remove them is wrong and gets corrected (§1, F1).
5. **The converse `Circuit.ofStraightLine` is Σ-valued and exact for single-output gated circuits** (size, depth, eval, and the round trip), so the family flip needs no copy gates and no `≤` repairs.
6. **Every commit passes all gates and is pushed straight to `origin/circuit-migration`.** A draft PR against `dev` makes CI run on every push.

## 1. Facts I checked that constrain the design

Paths are relative to the repository root.

| # | Fact | Where |
|---|---|---|
| F1 | `Basis.andOr2` has `arity _ := .exactly 2` and no nullary kind. The first line of any program on 0 inputs needs `Fin 2 → Wire 0 0`, which is empty. So `Cslib.Circuits.Circuit Basis.andOr2.signature 0 1` is empty. So is `Cslib.Circuits.CircuitFamily Basis.andOr2.signature`, and `Interpretation.IsComplete` fails, so `Cslib.Circuits.complexity` cannot be applied. | `Circuits/AndOrNot/Defs.lean`; CSLib `Complexity.lean:52` |
| F2 | `boundedAndOr k`, `unboundedAndOr` and `threshold` allow fan-in 0 (constants), but a zero-input circuit still costs 1 gate and has depth 1, while the typed family charges 0 at n = 0. | `Circuits/AndOrNot/Defs.lean`, `Circuits/Threshold/Defs.lean` |
| F3 | Typed output gates are sinks: wires are `Fin (N+G)`, and outputs are separate gates. `toStraightLine` puts the outputs on the last M lines (`outputs o := .gate (Fin.natAdd G o)`, `size := G + M`). | `Circuits/Basic.lean:109`, `Circuits/StraightLine/Defs.lean` |
| F4 | CSLib `Line.depth = succ (foldl max wireDepths)` with input depth 0. This is the same shape as typed `outputDepth = 1 + foldl max wireDepth`. | CSLib `Program.lean:160`; `Basic.lean:192` |
| F5 | `Circuit.comp` maps outer outputs through `appendWire`, which sends `.gate j` to `.gate (natAdd _ j)`. `Circuit.append` maps gates to gates. So both preserve gating when the outer circuit (for `comp`) or both circuits (for `append`) are gated. | CSLib `Composition.lean:119,131` |
| F6 | Only two `CompleteBasis` instances exist: `andOr2` (`Internal/Simulation.lean:1026`, derived from `unboundedAndOr`) and `unboundedAndOr` (`Internal/AndOrNot.lean:457`). `CompleteBasis` is multi-output. | `Basic.lean:218` |
| F7 | Duplicates to remove:<br>• `Complexity.StraightLine.ofLines` equals `Complexity.Program.ofLines` (`Interop/Cslib/CircuitDepth.lean:121`).<br>• `Complexity.Circuit.ofCslibWire` equals CSLib `Wire.index` (same two cases).<br>• `Complexity.Program.lines_wires_lt` (`Interop/Cslib/Circuit/Defs.lean:109`) restates CSLib `Program.lines_wires_lt` in `index` form. | as cited |
| F9 | The CSLib pin `SamuelSchlesinger/cslib@2a4389ba` is the head of the remote branch `complexitylib-integration` (checked with `git ls-remote`). The docbuild manifest already pins the same rev and CLAUDE.md documents the fork, so CI can fetch it. | `lakefile.toml`, `docbuild/lake-manifest.json` |
| F10 | Nothing outside `Basic.lean` unfolds `realizationSizes` or `sizeComplexity`. Consumers use only the API lemmas. `PPoly_eq_iUnion_SIZE` is `rfl`, and `mem_PPoly_iff` has 7 uses. | `grep` |
| F11 | `CircuitFamily` is built by structure literal in 9 files: BasisHom/Defs, PPoly/{Advice,Unrolling,Uniform/Unrolling}/Defs, Uniform/Unrolling/Padded, Randomized/PPoly/Defs, and Interop/Cslib/{Circuit, CircuitClasses, CircuitDepth}. `internalGateCount` is used in BasisHom/Defs and PPoly/Oracle/Inlining/Defs. | `grep` |
| F12 | Pinned names:<br>• **AxiomGuard:** `shannon_lower_bound_circuit`, `shannon_sizeComplexity`, `shannon_upper_bound`, `Circuit.card_essentialInputs_le_mul_size`, `sizeComplexity_xorBool_ge`, `P_subset_UniformPPoly`, `UniformPPoly_eq_P`.<br>• **Blueprint, in addition:** `SIZE`, `SIZEWithBasis`, `PPoly`, `mem_PPoly_iff`, `P_subset_PPoly`, `BPP_subset_PPoly`, `PPoly_subset_PAdvice`, `NC1_subset_Width5BP`, `NC1_subset_FormulaNC1`, `schnorr_lower_bound_circuit`, `Schnorr.xorBool`, `essentialInputs`, `MCSP.Instance`, `CircuitCode.{encodeCircuit, evalCode, evalCode_encodeCircuit, encodeCircuit_length_le_size}`, `Circuit.outputAC0Formula{,_spec}`. | `scripts/AxiomGuard.lean`, `blueprint/src/chapters/*.tex` |
| F13 | `parity_size_lowerBound_of_deMorgan_realization` bounds by `(realization.operation op).size`, which counts NOT gates: `AND(¬a,¬b)` has size 3, so K = 3 and the bound is only `N-1`. The right lemma is `parity_size_lowerBound_of_deMorgan_minimumCost` with K = 1 (binaryCost charges NOT 0). | `Algebraic/LowerBound/GateElimination/Translation.lean:60,79` |
| F14 | CSLib `Synthesis` is a Prop (∀ p₁ ∃ p₂). Builders consumed in Defs files need concrete circuits. Those files: MCSP `AntiChecker/GoodString/Circuit/Defs`, `Magnification/.../Selection/Defs`, `Encoding/FixedWidth/{Lookup,Validity}/Defs`, `KeyedMinimumTournament/Family/Defs`, `Randomized/ApproximateCounting/Relative/Circuit/Defs`. | `grep` |
| F15 | CSLib counting needs `[Fintype σ.Op]`. `Basis.signature` is a `def`, so the instance must be stated on `Basis.andOr2.signature.Op`, not on `GateKind`. | CSLib `Counting.lean:44,225` |

## 2. Lean definitions

### 2.1 Basis layer (commit 2.1: pure move)

- **`Circuits/Basis/Defs.lean`** (new; imports `Cslib.Computability.Circuit.Basic`): `BitString`, `BoolFunFamily`, `Arity`, `Arity.satisfiedBy`, `Basis`, and `Basis.GateKind`, `Basis.signature`, `Basis.interpretation`, moved unchanged from `StraightLine/Defs.lean`.
- **`Circuits/Typed/Defs.lean`** (new): `Gate`, `Gate.eval`, typed `Circuit`, `wireValue` and its lemmas, `wireDepth`, `outputDepth`, `depth`, `eval`, `size`, `CompleteBasis`, `CompleteBasis.of_simulation`.
- **`Circuits/Basic.lean`** becomes a surface: it imports the above plus (after 2.5) `Circuits/Size`, so every `import Complexitylib.Circuits.Basic` still sees everything.
- `StraightLine/Defs.lean` imports `Basis/Defs` and `Typed/Defs` and keeps `Gate.kind` and `toStraightLine`.

### 2.2 CSLib extensions (commit 2.2; namespace `Cslib.Circuits`)

These go in a new tree `Complexitylib/Cslib/Circuit/`, as ROADMAP phase 5 anticipates. `lint_style.py` checks `_root_.` escapes, not namespaces, so the only prerequisite is a one-line CLAUDE.md exception naming `Complexitylib/Cslib/` next to `Complexitylib/Mathlib/`.

```lean
-- Complexitylib/Cslib/Circuit/Gated.lean
namespace Cslib.Circuits
variable {σ : Signature} {n m p g : ℕ}

/-- Whether a wire is the output of an internal gate. -/
def Wire.IsGate : Wire n g → Prop
  | .input _ => False
  | .gate _ => True
instance (w : Wire n g) : Decidable w.IsGate := by cases w <;> unfold Wire.IsGate <;> infer_instance

/-- The gate carrying a gate wire (computable; the input case is absurd). -/
def Wire.gateOf : (w : Wire n g) → w.IsGate → Fin g
  | .gate j, _ => j
  | .input _, h => h.elim

/-- Every designated output is an internal gate. -/
def Circuit.GatedOutputs (c : Circuit σ n m) : Prop := ∀ o, (c.outputs o).IsGate
instance (c : Circuit σ n m) : Decidable c.GatedOutputs := Fintype.decidableForallFintype

theorem Circuit.GatedOutputs.size_pos [NeZero m] {c : Circuit σ n m} (h : c.GatedOutputs) :
    0 < c.size
theorem Circuit.GatedOutputs.comp {d : Circuit σ m p} (hd : d.GatedOutputs) (c : Circuit σ n m) :
    (d.comp c).GatedOutputs
theorem Circuit.GatedOutputs.append {c : Circuit σ n m} {d : Circuit σ n p}
    (hc : c.GatedOutputs) (hd : d.GatedOutputs) : (c.append d).GatedOutputs

/-- Outputs that forward an input wire. -/
def Circuit.inputOutputCount (c : Circuit σ n m) : ℕ :=
  (Finset.univ.filter fun o => ¬ (c.outputs o).IsGate).card
theorem Circuit.inputOutputCount_eq_zero_iff {c : Circuit σ n m} :
    c.inputOutputCount = 0 ↔ c.GatedOutputs
```

```lean
-- Complexitylib/Cslib/Circuit/Program.lean
-- Moved here from Interop/Cslib/CircuitDepth.lean (namespace Complexity.Program → Cslib.Circuits.Program):
--   Program.ofLines, Program.wireCastLE, Program.lines_ofLines, Program.depths_eq_lines_depth,
--   Program.wireDepths_gate_castSucc, Line.depth_mono, Program.wireDepths_le.
def Program.totalFanIn : Program σ n g → ℕ
  | .empty => 0
  | .gate p line => p.totalFanIn + σ.Arity line.op
def Circuit.totalFanIn (c : Circuit σ n m) : ℕ := c.program.totalFanIn
```

Dedupes (F7):
- delete `Complexity.StraightLine.ofLines` (use `Program.ofLines`);
- delete `Complexity.Circuit.ofCslibWire` and `toCslibWire` (use `Wire.index`, with `ofCslibWire w = w.index` by `cases w <;> rfl` as the migration lemma);
- delete `Complexity.Program.lines_wires_lt` (use CSLib's).

### 2.3 Converse translation, copy gates, finiteness (commits 2.3 and 2.4; namespace `Complexity`)

```lean
-- Circuits/StraightLine/Defs.lean
/-- The gate of `B` performing line `l`, renumbered in the typed layout and bounded by `W`. -/
def Gate.ofLine {B : Basis} {N g W : ℕ} (l : Line B.signature N g)
    (hW : ∀ a, (l.wires a).index.val < W) : Gate B W where
  op := l.op.op
  fanIn := l.op.fanIn
  arityOk := l.op.arityOk
  inputs a := ⟨(l.wires a).index, hW a⟩
  negated := l.op.negated
@[simp] theorem Gate.kind_ofLine : (Gate.ofLine l hW).kind = l.op := rfl

namespace Circuit
variable {B : Basis} {N M : ℕ} [NeZero N] [NeZero M]
/-- Converse of `toStraightLine` on gated circuits: internal gate `i` is line `i`
(`i < c.size - 1`) and output `o` copies the line driving `c.outputs o`. -/
def ofStraightLine (c : Cslib.Circuits.Circuit B.signature N M) (hc : c.GatedOutputs) :
    Σ G, Circuit B N M G :=
  ⟨c.size - 1,
   { gates := fun i => Gate.ofLine (c.program.lines ⟨i, by omega⟩) fun a =>
       lt_of_lt_of_le (c.program.lines_wires_lt _ a) (by simp; omega)
     outputs := fun o => Gate.ofLine (c.program.lines ((c.outputs o).gateOf (hc o))) fun a =>
       lt_of_lt_of_le (c.program.lines_wires_lt _ a) (by have := ((c.outputs o).gateOf (hc o)).isLt; omega)
     acyclic := fun i a => c.program.lines_wires_lt ⟨i, by omega⟩ a }⟩
end Circuit

/-- A gate kind returning its argument when every argument carries the same bit. -/
class Basis.HasCopyGate (B : Basis) where
  copy : B.GateKind
  fanIn_pos : 0 < copy.fanIn
  interpretation_copy : ∀ b : Bool, B.interpretation copy (fun _ => b) = b
-- instances: andOr2 (AND, fan-in 2, no flags); boundedAndOr k with [NeZero k] (AND, fan-in 1);
-- unboundedAndOr (AND, fan-in 1); threshold (cutoff 1, fan-in 1). None for boundedAndOr 0.

namespace StraightLine
/-- Make a single output a gate: an input-forwarding output becomes one copy gate. -/
def gated [B.HasCopyGate] (c : Cslib.Circuits.Circuit B.signature N 1) :
    Cslib.Circuits.Circuit B.signature N 1 :=
  match c.outputs 0 with
  | .gate _ => c
  | .input i => ⟨.gate .empty ⟨Basis.HasCopyGate.copy, fun _ => .input i⟩, fun _ => .gate 0⟩
end StraightLine

-- Circuits/StraightLine/Finite.lean
instance : Fintype Basis.andOr2.signature.Op      -- via ≃ AndOrOp × (Fin 2 → Bool); card 8
instance : DecidableEq Basis.andOr2.signature.Op
```

Lemmas, all in `StraightLine.lean`:
- `gatedOutputs_toStraightLine`
- `eval_ofStraightLine : (ofStraightLine c hc).2.eval x = c.eval B.interpretation x`
- `fst_ofStraightLine : (ofStraightLine c hc).1 = c.size - 1` (rfl)
- `size_ofStraightLine : (ofStraightLine c hc).2.size = c.size - 1 + M` (rfl)
- `size_ofStraightLine_one : … = c.size` (M = 1, using `size_pos`)
- `depth_toStraightLine : c.toStraightLine.depth = c.depth`
- `depth_ofStraightLine : (ofStraightLine c hc).2.depth = c.depth`
- `ofStraightLine_toStraightLine (c : Circuit B N 1 G) : ofStraightLine c.toStraightLine c.gatedOutputs_toStraightLine = ⟨G, c⟩` (needs `@[ext]` on typed `Circuit` and `Gate`; `G + 1 - 1` reduces to `G` by `rfl`)
- `totalFanIn_toStraightLine`
- For `gated`: `gatedOutputs_gated`, `eval_gated`, `size_gated_le : (gated c).size ≤ max 1 c.size`, `gated_eq_self (hc) : gated c = c`, `depth_gated : (gated c).depth = max 1 c.depth`

Optional (only if a 3.2 step needs it): `ofStraightLineMulti [B.HasCopyGate] : Cslib.Circuits.Circuit B.signature N M → Circuit B N M c.size`, which keeps all lines and adds one copy gate per output.

### 2.4 Measures (commit 2.5; `Circuits/Size/Defs.lean`)

```lean
namespace Complexity.Circuit
variable {B : Basis} {N : ℕ}      -- no [NeZero N] in this section (it would be unused)

def Realizable (B : Basis) (f : BitString N → Bool) : Prop :=
  ∃ c : Cslib.Circuits.Circuit B.signature N 1,
    c.GatedOutputs ∧ c.Computes B.interpretation fun x _ => f x

def realizationSizes (B : Basis) (f : BitString N → Bool) : Set ℕ :=
  {s | ∃ c : Cslib.Circuits.Circuit B.signature N 1,
    c.GatedOutputs ∧ c.size = s ∧ c.Computes B.interpretation fun x _ => f x}

noncomputable def sizeComplexityWithTop (B : Basis) (f : BitString N → Bool) : WithTop ℕ :=
  sInf ((fun s : ℕ => (s : WithTop ℕ)) '' realizationSizes B f)          -- body text unchanged

-- Existing documented nolint, comment extended: `CompleteBasis B` and `NeZero N` are the
-- preconditions under which the infimum is attained.
@[nolint unusedArguments]
noncomputable def sizeComplexity (B : Basis) [CompleteBasis B] [NeZero N]
    (f : BitString N → Bool) : ℕ :=
  sInf (realizationSizes B f)                                             -- body text unchanged
```

`Realizable`, `realizationSizes` and `sizeComplexityWithTop` lose their unused `[NeZero N]`. This makes them more general, and no theorem statement changes text. If some call site passes the instance explicitly, fall back to the same documented `@[nolint]`.

Characterizations:
- **`Size/Internal.lean`:** `realizationSizes_eq_typed [NeZero N]`, which rewrites `realizationSizes B f` as `{s | ∃ G, ∃ c : Circuit B N 1 G, c.size = s ∧ (fun x => c.eval x 0) = f}`; and `realizable_iff_typed`.
- **`Circuits/Size.lean`, CSLib-native:**
  - `sizeComplexityWithTop_eq_ecomplexity_of_forall_ne_proj (hf : ∀ i, f ≠ fun x => x i) : (sizeComplexityWithTop B f : ℕ∞) = ecomplexity B.interpretation fun x (_ : Fin 1) => f x`. This holds for every B: a circuit computing a non-projection has a gate as its output.
  - `sizeComplexityWithTop_eq_max_one_ecomplexity [B.HasCopyGate] : (sizeComplexityWithTop B f : ℕ∞) = max 1 (ecomplexity B.interpretation fun x (_ : Fin 1) => f x)`.
  - `sizeComplexity_le_of_gated (c) (hg : c.GatedOutputs) (hc) : sizeComplexity B f ≤ c.size`.
  - `sizeComplexity_le_of_computes [B.HasCopyGate] (c) (hc) : sizeComplexity B f ≤ max 1 c.size`. This is the "charged size" bound for ungated sources such as Synthesis or Lupanov.
  - `exists_gated_size_eq_sizeComplexity`.
  - `mem_SIZEWithBasis_iff_sizeComplexityWithTop : L ∈ SIZEWithBasis B s ↔ ∀ n [NeZero n], sizeComplexityWithTop B (L.slice n) ≤ s n`, together with its `[B.HasCopyGate]` `max 1 ∘ ecomplexity` form (commit 2.9).

Defining `sizeComplexityWithTop := max 1 ∘ ecomplexity` was considered and rejected. For a basis with no copy gate, such as `boundedAndOr 0` or a future user basis, the typed value on a projection is `⊤` but `max 1 0 = 1`, so the meaning would change. It remains a theorem.

`CompleteBasis` keeps its typed, multi-output text through phase 2. It is used only to show that `realizationSizes` is nonempty, via `toStraightLine`. It is flipped in 3.7.

### 2.5 Family and shims (commits 2.6 to 2.8)

After the flip, `Circuits/Family/Defs.lean`:

```lean
structure CircuitFamily (B : Basis) where
  emptyOutput : Bool
  circuit : ∀ (n : ℕ) [NeZero n], Cslib.Circuits.Circuit B.signature n 1
  circuit_gated : ∀ (n : ℕ) [NeZero n], (circuit n).GatedOutputs

namespace CircuitFamily
def function (F : CircuitFamily B) : BoolFunFamily
  | 0, _ => F.emptyOutput
  | n + 1, x => (F.circuit (n + 1)).eval B.interpretation x 0
def size (F : CircuitFamily B) : ℕ → ℕ | 0 => 0 | n + 1 => (F.circuit (n + 1)).size
def depth (F : CircuitFamily B) : ℕ → ℕ | 0 => 0 | n + 1 => (F.circuit (n + 1)).depth
-- evalList, SizeBoundedBy, DepthBoundedBy, PolynomialSize, Computes, language, Decides: text unchanged.
-- internalGateCount and the Σ-valued `circuits` field are deleted.
```

`Circuits/Family/Typed.lean` holds the shims. It is added in 2.6 on the old structure, reimplemented in 2.8, and deleted in phase 4.

```lean
@[irreducible] def CircuitFamily.ofTyped (emptyOutput : Bool)
    (C : ∀ (n : ℕ) [NeZero n], Σ G, Circuit B n 1 G) : CircuitFamily B
  -- 2.6: ⟨emptyOutput, C⟩;  2.8: ⟨emptyOutput, fun n => (C n).2.toStraightLine,
  --                               fun n => (C n).2.gatedOutputs_toStraightLine⟩
@[irreducible] def CircuitFamily.typedCircuit (F : CircuitFamily B) (n : ℕ) [NeZero n] :
    Σ G, Circuit B n 1 G
  -- 2.6: F.circuits n;  2.8: Circuit.ofStraightLine (F.circuit n) (F.circuit_gated n)
```

`@[irreducible]` from the start makes any consumer that leans on definitional equality fail at the pre-shim commit instead of at the flip. Shim API (rfl in 2.6, theorems in 2.8):
- `emptyOutput_ofTyped`
- `typedCircuit_ofTyped : (ofTyped e C).typedCircuit n = C n`
- `function_succ_typed : F.function (n+1) x = (F.typedCircuit (n+1)).2.eval x 0`
- `size_succ_typed : F.size (n+1) = (F.typedCircuit (n+1)).2.size` (an equality, not ≤)
- `depth_succ_typed : F.depth (n+1) = (F.typedCircuit (n+1)).2.depth`
- `exists_ofTyped (F) : (ofTyped F.emptyOutput F.typedCircuit).function = F.function ∧ … .size = F.size ∧ … .depth = F.depth`

In 2.6/2.7, `encodeAt` becomes `true :: CircuitCode.encodeCircuit (F.typedCircuit (n + 1)).2`. By `typedCircuit_ofTyped` it produces exactly the old bits for every family built by `ofTyped`. After 3.3 it is redefined as `true :: (RawCircuit.ofCslib (F.circuit (n+1))).encode`, which gives the same bits by `ofCslib_eq_ofCircuit` (§4).

Certificate theorems (added in 2.8, deleted in phase 4). They state each class in the old typed-family formula, with no duplicate `TypedCircuitFamily` structure:

```lean
theorem mem_SIZEWithBasis_iff_typed : L ∈ SIZEWithBasis B s ↔
    ∃ (e : Bool) (C : ∀ (n : ℕ) [NeZero n], Σ G, Circuit B n 1 G),
      (CircuitFamily.ofTyped e C).Decides L ∧ ∀ (n : ℕ) [NeZero n], (C n).2.size ≤ s n
theorem mem_DEPTHWithBasis_iff_typed : f ∈ DEPTHWithBasis B d ↔
    ∃ e C, (CircuitFamily.ofTyped e C).Computes f ∧ ∀ (n : ℕ) [NeZero n], (C n).2.depth ≤ d n
theorem mem_NC_iff_typed (i : ℕ) : f ∈ NC i ↔ ∃ e (C : ∀ (n : ℕ) [NeZero n], Σ G, Circuit Basis.andOr2 n 1 G)
    (p : Polynomial ℕ) (c : ℕ), (CircuitFamily.ofTyped e C).Computes f ∧
      (∀ (n : ℕ) [NeZero n], (C n).2.size ≤ p.eval n) ∧
      ∀ (n : ℕ) [NeZero n], (C n).2.depth ≤ polylogDepth i c n
-- mem_AC_iff_typed, mem_TC_iff_typed: same shape over unboundedAndOr / threshold
```

The SIZE certificate goes in `Classes/PPoly.lean` and the depth-class certificates in `Circuits/DepthClasses.lean`.

`CircuitFamily.mapBasis` goes through the shim (`ofTyped F.emptyOutput fun n => ⟨_, (F.typedCircuit n).2.mapBasis hom⟩`). `ofStraightLine` needs only the family's own gating field, so the generic-B statements `PromiseSIZEWithBasis_mapBasis_subset`, `AC_subset_TC` and `function/size/depth_mapBasis` gain no hypotheses. The native `Program.mapOps` form comes in 3.5.

### 2.6 What becomes what

| Name | Phases 2 and 3 | Phase 4 |
|---|---|---|
| `Basis`, `Basis.signature`, `Basis.interpretation`, `Basis.GateKind` | definitions, moved to `Basis/Defs` | unchanged |
| `Circuit.Realizable`, `realizationSizes`, `sizeComplexityWithTop`, `sizeComplexity` | definitions over gated CSLib circuits (2.5) | unchanged |
| `CircuitFamily` with `function`, `size`, `depth` | definitions over gated CSLib circuits; `emptyOutput` kept (2.8) | unchanged |
| `SIZEWithBasis`, `SIZE`, `PPoly`, `DEPTHWithBasis`, `DEPTH`, `polylogDepth`, `NC`/`AC`/`TC`/`NC0`/`NC1`/`AC0`/`TC0`, `UniformPPoly`, `CircuitFamily.Uniform`, `PromiseSIZEWithBasis`, `language`, `Decides` | text unchanged | unchanged. `PPoly := Cslib.Circuits.Boolean.PPoly` is an optional phase-5 alias: exact by `PPoly_eq_cslib_PPoly`, but it needs the bridge moved below `Classes/PPoly.lean`, and `PPoly_eq_iUnion_SIZE` stops being `rfl`. |
| `CompleteBasis`, `of_simulation` | typed until 3.7, then over gated CSLib circuits, keeping the multi-output shape `∀ {N M} [NeZero N] [NeZero M] f, ∃ c, c.GatedOutputs ∧ c.Computes B.interpretation f` | unchanged |
| `MCSP.Instance.HasCircuitAtMost` | typed until 3.6, then over gated CSLib circuits | unchanged |
| CSLib `ecomplexity`, `complexity`, `Boolean.SIZE`, `Boolean.PPoly`, `CircuitFamily`, `DecidableInSize` | reference notions, connected by theorems | same |
| Typed `Circuit`, `Gate`, shims, `*_typed` corollaries | coexist | deleted |

No aliases, for these reasons:
- `SIZE := Boolean.SIZE` would count NOTs and free the output. It would falsify `mem_SIZE_iff_sliceSizeComplexity_le`, because De Morgan needs 1 gate at n = 0.
- `sizeComplexity := complexity` fails for two reasons: `IsComplete` is false for `andOr2` (F1), and projections would cost 0.
- `CircuitFamily := Cslib.Circuits.CircuitFamily` would be empty for `andOr2` (F1).

## 3. Conventions and statement preservation

### 3.1 Counted output gates vs free output wires: `GatedOutputs`

These exact equalities carry every statement:

| Id | Equality | Source |
|---|---|---|
| E1 | `c.toStraightLine.size = c.size` (= G + M) | `size_toStraightLine` (exists) |
| E2 | `c.toStraightLine.GatedOutputs` | F3 |
| E3 | `(ofStraightLine c hc).2.size = c.size - 1 + M`; for M = 1, `= c.size` | rfl, plus `size_pos` |
| E4 | `depth_toStraightLine`, `depth_ofStraightLine`: equal | F4; generalizes `Program.depths_eq_lines_depth` and `wireDepth_ofCslib` |
| E5 | `eval_toStraightLine` (exists), `eval_ofStraightLine` | generalizes `wireValue_ofCslib` |
| E6 | `ofStraightLine c.toStraightLine _ = ⟨G, c⟩` (M = 1) | `Gate.ext`, `Circuit.ext` |
| E7 | `totalFanIn_toStraightLine` | lines are the typed gates |

Consequences:
- `realizationSizes_eq_typed` and `realizable_iff_typed` follow from E1 to E3 and E5, so every measure lemma keeps its text.
- `size_succ_typed`, `depth_succ_typed` and `function_succ_typed` are exact (E3 to E5).
- So every class is set-equal to its typed version for every basis and every bound, including `s 0 = 0`, `s n = 0` and `d n = 0`.

Without gating, meanings would change in these places:
- `SIZE (fun _ => 0)`, which is empty today, would contain projection languages.
- `DEPTH (fun _ => 0)` would change the same way.
- `sizeComplexity_pos` would be false.
- An MCSP instance with threshold 0 would accept projections.
- Schnorr would fail at N = 1: the zero-gate wiring computes `xor₁ = x₀`.
- The essential-input bound would fail on the identity wiring.

Classes with an existential constant (`NC i`, `AC i`, `TC i`, `PPoly`) would not change, which corrects the in-place claim about `NC 0`.

Multi-output circuits:
- CSLib size ≤ typed size ≤ CSLib size + M − 1 via `ofStraightLine`. There is no exact formula, because typed outputs are distinct sinks.
- No public class is multi-output.
- The multi-output headline (essential inputs) is proved directly over CSLib (§3.4).

### 3.2 Free per-edge negations vs De Morgan (NOT counted)

This is carried by the signature itself: `Basis.interpretation` is `Gate.eval`. De Morgan appears only in the reference theorems. All of them keep their constants, and in phase 2 their proofs go through the unchanged API lemmas and shims:

| Statement (file) | Bound kept |
|---|---|
| `sizeComplexity_le_of_cslib` (Interop/Cslib/Circuit.lean) | `≤ c.size + 1` |
| `exists_cslib_of_sizeComplexity` | `≤ N + 2 · sizeComplexity` |
| `SIZE_subset_cslib_SIZE`, `exists_cslib_of_mem_SIZE` | `n + 2 s n + 1` |
| `cslib_SIZE_subset_SIZE`, `mem_SIZE_of_cslib` | `s n + 1` |
| `PPoly_eq_cslib_PPoly`, `exists_not_mem_PPoly` | equality |
| `exists_cslib_of_mem_DEPTH`, `mem_DEPTH_of_cslib` | `d + 1` |
| `lupanov_sizeComplexity`, `exists_sizeComplexity_gt_cslib` | unchanged |

In 3.8 the typed `ofCslib` and `toCslib` are replaced by CSLib-level translations:
- `ofDeMorgan : Circuit Boolean.signature N M → Circuit Basis.andOr2.signature N M` (needs `[NeZero N]`) works gate for gate:
  - `NOT w ↦ AND(¬w,¬w)`
  - `const b ↦ OR/AND(x₀,¬x₀)`
  - AND and OR are unchanged.
  - Size and depth are exact, and the outputs are unchanged.
- The dual rail `toDeMorgan` has size `N + 2·c.size` and depth ≤ `c.depth + 1`.

These give the sharper siblings `sizeComplexity Basis.andOr2 f ≤ max 1 (Boolean complexity of f)` and `Boolean complexity ≤ N + 2·sizeComplexity`.

Lower bounds do not transfer through De Morgan: Red'kin's `4(n−1)` through the per-gate map gives only `2N−2`. So `andOr2` lower bounds use the Algebraic `binaryCost` transport (F13).

### 3.3 N ≥ 1 / `emptyOutput` vs zero-input circuits

Both stay: `sizeComplexity` keeps `[NeZero N]`, `CompleteBasis` stays positive-arity, the family keeps `[NeZero n]` and `emptyOutput`, and `size 0 = depth 0 = 0`. The reasons:
- For `andOr2` there are no zero-input circuits at all (F1).
- For the other bases, dropping `emptyOutput` would charge 1 gate and depth 1 at n = 0 (F2). That would change `SIZE s` whenever `s 0 = 0` and `DEPTH d` whenever `d 0 = 0`.
- Only the existential classes would be unaffected, and only for bases with constants.

CSLib's `n^k + k` against our zero cost at length 0 stays absorbed inside `PPoly_eq_cslib_PPoly`, as the `+1` in `n + 2 s n + 1`. Commit 2.10 corrects ROADMAP item 7.

### 3.4 Named public statements

| Statement | Phase 2 | Phase 3 | What preserves it |
|---|---|---|---|
| `sizeComplexityWithTop_le`, `_eq_top_iff`, `_ne_top_iff`, `_witness`, `_eq_coe`, `sizeComplexity_pos`, `sizeComplexity_le`, `sizeComplexity_witness`, `Circuit.Computes.sizeComplexity{,WithTop}_le` | text unchanged, typed binders, no new hypotheses | kept until phase 4, when they are restated over CSLib | `realizationSizes_eq_typed` (E1, E3, E5, E6) |
| `SIZEWithBasis`, `SIZE`, `PPoly`, `SIZE_mono`, `mem_PPoly_iff` (typed-free text: `∃ F : CircuitFamily Basis.andOr2, …, F.size =O …`), `PPoly_eq_iUnion_SIZE` (still `rfl`), `P_subset_PPoly`, `BPP_subset_PPoly`, `PPoly_subset_PAdvice`, `UniformPPoly_subset_PPoly` | unchanged | unchanged | `mem_SIZEWithBasis_iff_typed` (E3 exact for M = 1) |
| `mem_SIZE_iff_sliceSizeComplexity_le`, `mem_SIZE_sliceSizeComplexity` | unchanged | unchanged | n = 0 via `emptyOutput`; `sizeComplexity_witness` |
| `UniformPPoly`, `P_subset_UniformPPoly`, `UniformPPoly_eq_P`, `UniformPPoly_subset_P` | unchanged | unchanged | bit-exact `encodeAt` (E6, then `ofCslib_eq_ofCircuit`) |
| `DEPTH`, `DEPTHWithBasis`, `NC`/`AC`/`TC`, `NC_mono`, `AC_subset_TC`, `mem_NC1_iff`, `mem_AC0_iff`, `mem_TC0_iff`, `NC1_subset_Width5BP`, `NC1_subset_FormulaNC1`, `depth_outputFormulaFamily_le` (≤ 2·`F.depth`) | unchanged | unchanged | E4 exact both ways; `mapBasis` needs no hypotheses |
| `shannon_lower_bound_circuit` (N ≥ 6, `c.size ≤ 2^N/(5N)`) | unchanged | 3.1: `∀ c : Cslib.Circuits.Circuit Basis.andOr2.signature N 1, c.size ≤ 2^N/(5N) → ¬ c.Computes _ fun x _ => f x`, with no gating hypothesis (a strengthening); old text kept as `shannon_lower_bound_circuit_typed` | gated c: `ofStraightLine` gives a typed circuit of equal size. Ungated c: f = xᵢ, and the typed copy gate `xᵢ∧xᵢ` has size 1 ≤ 2^N/(5N), since 5N ≤ 2^N for N ≥ 6 (2^6/30 = 2). Contradiction either way. |
| `shannon_sizeComplexity`, `shannon_upper_bound` (N ≥ 16, ≤ 18·2^N/N), `lupanov_sizeComplexity`, `sizeComplexity_xorBool_ge` (≥ 2N−1), `sizeComplexity_restrictFirst_le`, `sizeComplexity_or_le` (+1), `sizeComplexity_existsQuantify_le` (2^k(s+1)), `_shannon`, `minimumSize_eq_sizeComplexity`, `hasCircuitAtMost_iff_sizeComplexity_le` | unchanged | unchanged, re-proved natively | they mention only `sizeComplexity` |
| `schnorr_lower_bound_circuit` | unchanged | 3.1: `(c : Cslib.Circuits.Circuit Basis.andOr2.signature N 1) (hc : c.GatedOutputs) (comp) (heval : ∀ x, c.eval _ x 0 = comp.xor (Schnorr.xorBool N x)) : 2 * N - 1 ≤ c.size`; `_typed` corollary | Gating is necessary (the N = 1 wiring). Proof: `3(N−1) ≤ c.size` (below), `3(N−1) ≥ 2N−1` for N ≥ 2, and N = 1 from `size_pos`. New siblings: `three_mul_pred_le_size_of_xorBool` (ungated) and `three_mul_pred_le_sizeComplexity_xorBool : 3 * (N - 1) ≤ sizeComplexity Basis.andOr2 (xorBool N)`. |
| `card_essentialInputs_le_totalFanIn`, `card_essentialInputs_le_mul_size` (boundedAndOr k, M outputs, `≤ k * c.size`), `le_mul_size_of_forall_isEssentialInput` | unchanged | 3.1, gated: `(c : Cslib.Circuits.Circuit (Basis.boundedAndOr k).signature N M) (hc : c.GatedOutputs) … : (essentialInputs f).card ≤ k * c.size`. Ungated companions: `… ≤ c.totalFanIn + c.inputOutputCount` and `… ≤ k * c.size + c.inputOutputCount`. `_typed` corollaries. | Every essential input is read by some line or forwarded to an output. `inputOutputCount = 0` under gating. The typed statement follows from E1, E2 and E7 for every k. k = 0 is trivial only for gated or typed circuits (constant functions); the identity wiring breaks it for ungated ones, hence the companion. |
| `CircuitCode.encodeCircuit`, `evalCode_encodeCircuit`, `encodeCircuit_length_le_size` | unchanged | 3.3: CSLib binder; bound `1 + max 1 c.size * (2 * (N + max 1 c.size) + 6)`, which is the old bound when gated | `length_ofCslib = max 1 c.size` |
| `MCSP.Instance.HasCircuitAtMost`, set `MCSP` | unchanged | 3.6: `∃ c : Cslib.Circuits.Circuit Basis.andOr2.signature inst.arity 1, c.GatedOutputs ∧ c.size ≤ inst.threshold ∧ c.Computes _ fun x _ => inst.function x`, with `hasCircuitAtMost_iff_typed` | E1, E3 |
| `Circuit.outputAC0Formula{,_spec}` | unchanged | 3.5: CSLib binder, `_typed` corollary | recursion on `Program` |

The Schnorr proof uses `Realization Basis.andOr2.signature Algebraic.DeMorgan.signature Basis.andOr2.interpretation DeMorgan.interpretation`:
- Each kind `op(¬^a x, ¬^b y)` has `minimumCost binaryCost ≤ 1`.
- `parity_size_lowerBound_of_deMorgan_minimumCost` with K = 1 gives `3(N−1) ≤ c.size` for any CSLib `andOr2` circuit computing `parityTarget`.
- The complement case uses a five-line lemma `DeMorgan.not_xor_lowerBound`: append a NOT, which costs 0.
- Bridge lemmas needed: `xorBool_eq_parityTarget`, and `ComputesWith ↔ Computes`.

## 4. Converse translation and its exact size behaviour

| Translation | Domain | Result | Size | Depth | Eval |
|---|---|---|---|---|---|
| `Circuit.ofStraightLine c hc` | gated `Cslib.Circuits.Circuit B.signature N M`, `[NeZero N] [NeZero M]`, any basis | `Σ G, Circuit B N M G` with `G = c.size − 1` | `c.size − 1 + M`; exactly `c.size` for M = 1 | `= c.depth` | equal |
| `StraightLine.gated` then `ofStraightLine` | any single-output circuit, `[B.HasCopyGate]` | typed | `≤ max 1 c.size`; equal if gated or `c.size = 0` | `= max 1 c.depth` | equal |
| `ofStraightLineMulti` (optional) | any, `[B.HasCopyGate]` | `Circuit B N M c.size` | `c.size + M` | `c.depth + 1` | equal |
| existing `Circuit.ofCslib` (Interop) | De Morgan | `Circuit Basis.andOr2 N M c.size` | `c.size + M` | `c.depth + 1` | equal; kept until 3.8 |

Round trips:
- `ofStraightLine_toStraightLine = ⟨G, c⟩` for M = 1. This is the lemma that keeps `encodeAt` bit-exact.
- `(ofStraightLine c hc).2.toStraightLine` computes the same function with the same size (M = 1). It is structurally equal to c exactly when the output is the last line.

Serialization (3.3):
- `RawCircuit.toCslib (N) (r : RawCircuit) (h : r.WellFormed N) : Cslib.Circuits.Circuit Basis.andOr2.signature N 1` has `size = r.length`, output = last line, and is gated. `WellFormed` already includes `r ≠ []`.
- `RawCircuit.ofCslib c` emits lines `0..size−2` followed by the output line, or a copy gate `xᵢ∧xᵢ` if the output is input i. Its length is `max 1 c.size`.
- Lemmas:
  - `ofCslib_eq_ofCircuit (hc) : RawCircuit.ofCslib c = RawCircuit.ofCircuit (ofStraightLine c hc).2`
  - `ofCslib_toCslib : RawCircuit.ofCslib (r.toCslib N h) = r`
  - `eval?_ofCslib`

## 5. Commit-by-commit order

**Rule for every commit.** Run the ROADMAP gate list:
- `python3 scripts/lint_style.py`
- `lake build --wfail` and the five validation roots (Cobham, SingleTape, Repetition, Circuits.Encoding, SAT.Tseitin)
- `lake exe runLinter Complexitylib` (plus the validation roots)
- `lake env lean scripts/AxiomGuard.lean`
- `lake env lean scripts/BlueprintCheck.lean`

Update blueprint `\lean{}`/`\leanok` in the same commit, then `git push origin circuit-migration`. A typed declaration is deleted only when `grep` shows it has no users.

### Step 0 (done)

- `00f41e9` `chore(deps): build on the CSLib circuit integration branch`
- `eda4781` `feat(Circuits): translate typed circuits to CSLib straight-line programs`

The branch `circuit-migration` carries the work; `dev` fast-forwards to it at
phase boundaries, after the gates pass in CI.

### Phase 2 (definitions; consumers change only mechanically)

| # | Commit | Content | Why it builds |
|---|---|---|---|
| 2.1 | `refactor(Circuits): split the basis and typed-circuit definitions` | §2.1 pure move | names unchanged; `Basic.lean` re-exports |
| 2.2 | `refactor(Cslib): gated outputs, program helpers, and dedupes` | §2.2; CLAUDE.md exception; F7 dedupes (Interop files re-pointed) | additive, plus renames confined to 3 Interop files and StraightLine |
| 2.3 | `feat(StraightLine): converse translation with exact size and depth` | `Gate.ofLine`, `ofStraightLine`, E2 to E7, `@[ext]` on `Gate`/`Circuit` | additive |
| 2.4 | `feat(StraightLine): copy gates, output gating, finite andOr2 kinds` | `HasCopyGate` with 4 instances, `StraightLine.gated`, `Fintype`/`DecidableEq` (F15) | additive |
| 2.5 | `refactor(Circuits): define circuit size complexity over CSLib circuits` | §2.4 `Size/{Defs,Internal}.lean` and `Size.lean`; Basic.lean API lemmas re-proved by rewriting with `realizationSizes_eq_typed` | statements unchanged; no consumer unfolds the measures (F10). Rebuilds about 696 modules, so it stays alone. |
| 2.6 | `refactor(Family): route family construction through ofTyped` | `Family/Typed.lean` shims on the old structure (irreducible, rfl lemmas); the 9 constructor files (F11) switch to `ofTyped` | old structure untouched; shims are identities |
| 2.7a–c | `refactor(…): read family circuits through typedCircuit` | accessor sites switch from `F.circuit`/`F.circuits`/`internalGateCount`/typed uses of `size_succ`/`depth_succ`/`function_succ` to `typedCircuit` and the `_typed` lemmas. **(a)** Circuits: Encoding/Family `encodeAt`, CircuitFormula/Family/*, DepthClasses/Internal, BasisHom/*. **(b)** Classes/PPoly: Advice, Unrolling, Uniform/Unrolling (+Padded, Containment), Oracle, Oracle/Inlining. **(c)** Randomized/PPoly, Promise/CircuitSize, Interop/Cslib/*. The last commit adds a grep gate (no `.circuits`, `internalGateCount` or typed-consumed `F.circuit` outside `Family/`). | still the old structure; equalities, not `≤` |
| 2.8 | `refactor(Family): circuit families over CSLib circuits` | definitions only: the new `Family/Defs.lean`, shims reimplemented and proved, the `Family.lean` lemmas (`size_succ`/`depth_succ` text unchanged; `function_succ` gains `B.interpretation`), `exists_ofTyped`, certificates; a `#guard` in `Circuits/Encoding/Validation.lean` pinning `encodeAt` bits of a small `ofTyped` family, recorded before the flip | consumers touch only the shim API; near-full rebuild, alone |
| 2.9 | `feat(Circuits): relate size complexity to CSLib complexity` | `max 1 ∘ ecomplexity`, the non-projection equality, `mem_SIZEWithBasis_iff_*`, `sizeComplexity_le_of_{gated,computes}` | additive |
| 2.10 | `docs: correct ROADMAP item 7 and document the CSLib measures` | ROADMAP (emptyOutput stays; converse done), blueprint nodes, `Circuits.lean` module doc | docs only |

### Phase 3 (consumers by area)

Each area follows the same pattern:
1. Add the CSLib-native construction or theorem next to the typed one.
2. Switch the consumers.
3. Restate the public statement under its own name, keeping the old one as `_typed`.
4. Delete the typed internals once they have no importers.

The shims keep every other area green. Order and dependencies:
- 3.1 and 3.5 are independent after 2.8.
- 3.2 comes before 3.4 and 3.6.
- 3.3 comes before 3.4 and 3.6.
- Critical path: 2.3 → 2.8 → 3.3 → 3.4.

| Area | Commits |
|---|---|
| **3.1 Counting and gate elimination** | **(a)** Schnorr restated from the typed theorem via `ofStraightLine`. **(b)** Algebraic realization, `not_xor_lowerBound`, the `3(N−1)` siblings; `sizeComplexity_xorBool_ge` re-proved; delete `Internal/Schnorr.lean` (≈1475 lines) and `SchnorrBridge`. **(c)** Essential inputs: gated plus companions, `_typed`. **(d)** Shannon restated over all CSLib circuits (proof via `ofStraightLine`). **(e)** Replace CircDesc with `card_computableFunctions_mul_factorial_le_of_arity_le` at `Basis.andOr2.signature` (8 kinds, r = 2). This needs an explicit inequality `(s+1)·max(s, 8(N+s+1)²)^s·(N+s) < 2^(2^N)·s!` for `s = 2^N/(5N)`, N ≥ 6 (at N = 6 the left side is about 10⁷). Then delete CircuitDescriptor, CircuitToDescriptor and ShannonBridge. If the arithmetic stalls, keep CircDesc. **(f)** Nondeterminism natively: `append` plus one OR gate; line-level constant restriction. ShannonUpper is deferred: its statement is `sizeComplexity`-only and preserved. |
| **3.2 Builders** | One commit per builder under `Complexity.StraightLine.*` names, each with a lemma relating it to the typed builder through `toStraightLine`:<br>• compose → `Circuit.comp`; parallel → `Circuit.append` (both preserve gating, F5)<br>• projections and reindexing → `Circuit.wiring` plus `comp`<br>• hardwiring → line-level substitution on `andOr2` lines, size-exact like typed `restrictPrefix` (G unchanged), needs `[NeZero m]`<br>• Multiplexer, Majority, BinaryComparison, BinaryMinimum, KeyedMinimum(+Tournament), InputPairing/Sources/Projection, Dependency, OracleInlining, NormalForm → concrete computable `Program.ofLines` or `RawCircuit.toCslib` constructions. `Synthesis` is used only for existence and size (F14).<br>Typed builders stay until their last importer moves; Composition has 23. |
| **3.3 Serialization** | `RawCircuit.toCslib`/`ofCslib` and their round trips (§4); `encodeCircuit`, `evalCode_encodeCircuit` and `encodeCircuit_length_le_size` restated; `encodeAt` redefined through `ofCslib`, with the same bits by `ofCslib_eq_ofCircuit` (the Validation guard checks this). |
| **3.4 P/poly family consumers** | Unrolling/Acceptance, PPoly/{Unrolling, Advice(+Reverse), Uniform, Oracle}, Randomized/PPoly and amplification, Promise: `RawCircuit.toCircuit` plus typed `restrictPrefix` become `toCslib` plus CSLib restriction, and `ofTyped` becomes direct constructors. The roughly 60k machine lines are untouched. |
| **3.5 Depth consumers** | CircuitFormula (`outputFormulaFamily` unfolds `Program`); DepthClasses internals; BasisHom natively via `Program.mapOps (φ) (hφ : ∀ op, τ.Arity (φ op) = σ.Arity op)` (size, depth and gating equal); AC0 Normalization (circuit to `AC0Formula` by recursion on `Program`, `outputAC0Formula_spec` restated). Optional: parity ∉ AC0 from Algebraic's Håstad development, then retire the switching internals. |
| **3.6 MCSP** (36 files) | `HasCircuitAtMost` redefined with `hasCircuitAtMost_iff_typed`; witnesses through `RawCircuit.ofCslib`; generator and anti-checkers use the 3.2 builders. |
| **3.7 Completeness** | `CompleteBasis Basis.andOr2` from CSLib De Morgan completeness via `ofDeMorgan` and `gated`; `unboundedAndOr` from `andOr2` via `mapBasis` (fan-in 2 is allowed there). Then flip `CompleteBasis` and restate `of_simulation` over CSLib (multi-output shape kept). Retire `Internal/Simulation.lean` (1032 lines) and, if unused, the DNF parts of `Internal/AndOrNot.lean`. |
| **3.8 Interop and remaining** | CSLib-level `ofDeMorgan` and `toDeMorgan` replace typed `ofCslib`/`toCslib`, with the sharper siblings; BarringtonTyped; ensure nothing outside the `_typed` corollaries names typed `Circuit`, so phase 4 is pure deletion. |

## 6. Risks and mitigations

| Risk | Level | Mitigation |
|---|---|---|
| ROADMAP item 7's zero-input claim is wrong for `andOr2` (F1, F2) | high, design-level | keep `emptyOutput` and `NeZero`; correct the ROADMAP in 2.10 |
| Rebuild cost: `Basic.lean`'s reverse closure is about 696 modules | medium | 2.5 and 2.8 are separate small commits; the pre-shim keeps 2.8 definitions-only |
| Pre-shim leakage (consumers relying on definitional equality of the old structure) | medium | `@[irreducible]` shims from 2.6; grep gate in 2.7c |
| `encodeAt` bit-exactness (`UniformPPoly_eq_P` proves `gen 1^n = F.encodeAt n`) | medium | E6, then `ofCslib_eq_ofCircuit`; a `#guard` recorded before 2.8 |
| Dependent-type friction: `c.size − 1`, `B.signature.Arity k = k.fanIn` not definitionally 2, `Fin.cast` in `andOr2` lines | medium | Σ-valued converse; an `andOr2Line` smart constructor and simp lemmas; `≃ AndOrOp × (Fin 2 → Bool)`; the index-free `Program.lines` view |
| Gating friction for CSLib-built circuits | medium | closure lemmas (`comp`, `append`); `StraightLine.gated`; `sizeComplexity_le_of_computes` (`max 1`) |
| Explicit constants: Shannon (N ≥ 6, 5N) and ShannonUpper (N ≥ 16, 18·2^N/N); CSLib's results are eventual | medium | keep the CircDesc and ShannonUpper proofs until the explicit CSLib count exists. Porting via an explicit `Lupanov.synthesis` instance is plausible; adopt-cslib's claimed check at N = 16 (46017 ≤ 73727) needs re-verifying. |
| `Synthesis` is a Prop (F14) | medium | computable builders for Defs-level consumers |
| CSLib integration-branch churn (#949, #952, #955, #957, #954, #950 may rename `size`, `comp`, `ecomplexityOn`) | medium | use the CSLib API directly only in `Complexitylib/Cslib`, StraightLine, Size and Family; budget one re-sync |
| Name ambiguity under `open Cslib.Circuits` inside `namespace Complexity` (`Circuit`, `Circuit.Computes`, which also exists typed in `Family/Defs.lean`, `CircuitFamily`, `BitString`) | low-medium | fully qualify `Cslib.Circuits.Circuit` until phase 4 |
| `WithTop ℕ` vs `ℕ∞` in the `ecomplexity` lemmas | low | state them with an `ℕ∞` ascription and bridge by `show` |
| Env linter `unusedArguments` | low | drop `NeZero` from the three measures; keep the documented nolint on `sizeComplexity` |
| Pinned names (F12) | low | names are kept; restatements reuse the pinned names; `_typed` names are unpinned |
| Three parallel APIs (CSLib, Algebraic `ComputesWith`/`gateComplexity`, Complexitylib) | low | bridge lemmas in 3.1 (`ComputesWith ↔ Computes`, `gateComplexity = ecomplexity`) |

## 7. Effort (focused engineer-days)

| Area | Days | Notes |
|---|---|---|
| Step 0 | 0.5 | two commits |
| 2.1 to 2.4 | 4–6 | about 900 new lines; the converse and depth lemmas generalize `wireValue_ofCslib` and `wireDepth_ofCslib` |
| 2.5 measures | 1–2 | about 300 lines |
| 2.6 and 2.7 pre-shim | 1.5–2.5 | 9 constructor files and about 20 accessor files |
| 2.8 flip and certificates | 2–3 | about 500 lines |
| 2.9 and 2.10 | 1.5 | |
| **Phase 2 total** | **11–15** | about 13 pushed commits |
| 3.1 counting | 6.5–10.5 (+4–6 ShannonUpper) | deletes about 2.0k lines |
| 3.2 builders | 10–15 | about 5.5k lines touched; net −2k to −3k |
| 3.3 serialization | 3–5 | about 15 files, 2.8k lines |
| 3.4 P/poly consumers | 5–8 | about 25 files |
| 3.5 depth consumers | 7–12 (+4–8 parity ∉ AC0) | |
| 3.6 MCSP | 6–10 | 36 files, 4.9k lines |
| 3.7 completeness | 4–7 | retires about 1.0k to 1.5k lines |
| 3.8 remaining | 2–3 | |
| **Phase 3 total** | **43–70** (+8–14 optional) | about 35–45 commits |
| Phase 4 (deletion, `ℕ∞` cleanup) | 3–5 | |
| **Overall** | **about 57–90** | 45–60 green, pushed commits |

