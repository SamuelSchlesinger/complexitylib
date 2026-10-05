/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Network
public import Complexitylib.Cslib.Circuit.Upstream
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Compiling a circuit into a constraint network

Fix a straight-line program `p` over any signature, *output* wires `out o` indexed by a finite
type `O`, an interpretation `I` of the signature in an alphabet `U`, and for each output a set
`Acc o ⊆ U` of *accepting* values. We build a constraint network whose accepted inputs are
exactly those on which every output `o` lies in `Acc o`. A circuit deciding a set has one output;
a circuit computing a function accepts every value at each of its outputs.

Only the *reachable* wires matter: the outputs and, recursively, the arguments of reachable
gates. We call them *signals*. A signal is *consumed* by each argument slot of a reachable gate
that reads it, and each output is also consumed by its own *output vertex*. A circuit has
unbounded fan-out, but a bounded-degree network cannot give a signal one edge per consumer. So
each signal `w` with consumers `c₀, c₁, ...` is routed through a chain of *junctions*
`j₀, j₁, ...`, one per consumer:

```
  w --- j0 --- j1 --- j2 --- ...
        |      |      |
        c0     c1     c2
```

Each junction has one *feed* edge from its predecessor in the chain (the signal itself for
`j₀`) and one *deliver* edge to its consumer. The constraints are:

* a signal vertex for the input `x_i` reads `x_i` and puts it on its outgoing edge;
* a signal vertex for a gate `g` puts `g` applied to its incoming argument edges on its
  outgoing edge;
* a junction puts its incoming value on both of its outgoing edges;
* the output vertex of `o` requires its incoming value to lie in `Acc o`.

Every vertex has degree at most `r + 1` when the gates have fan-in at most `r ≥ 2`; for fan-in
two the graph is subcubic. The network records gates as *relations*: it never evaluates
anything, and the constraint of a gate does not care which of its edges a sweep reaches first.

**Exactness** (`accepted_network`). The values of a run of the program satisfy the network.
Conversely, in a satisfying assignment the junction constraints force all edges of a signal to
carry one value, and the gate constraints, read in program order, force that value to be the
signal's value in the run (`eq_trace`). So the satisfying assignment, if any, is unique.

**Counting.** With `C` consumers, `W` signals, and `|O|` outputs, the network has `2C` edges and
`W + C + |O|` vertices, so its cycle rank is `C - W - |O| + 1`, the number of slots minus the
number of signals plus one. A gate of arity `k` has `k` slots, so it contributes `k - 1` to the
cycle rank, and a reachable input contributes `-1`. Hence the cycle rank is at most
`(r - 1) s + 1 - m` for `s` gates of fan-in at most `r` and `m` reachable inputs. If all gates
are binary and reachable and there are no constants, the rank is exactly `s + 1 - m`, compared
with zero for a read-once binary formula on `m` distinct inputs. Sharing creates cycles;
gates create local constraints. Gates of arity zero,
the constants, only lower the cycle rank: the count charges only the *inner* gates, those of
positive arity.

## Main definitions

* `Frontier.Compiler.network p out I Acc`: the constraint network of a program.

## Main results

* `Frontier.Compiler.accepted_network`, `Frontier.Compiler.eq_trace`: exactness.
* `Frontier.Compiler.connected_of_upstream`, `loopless`: the graph is loopless, and connected
  when some wire is upstream of every output, in particular when there is one output.
* `Frontier.Compiler.maxDegreeLE`: for fan-in at most `r ≥ 2`, the degrees are at most `r + 1`.
* `Frontier.Compiler.cycleRank_add_ncard_read_le`: the cycle rank is at most
  `(r - 1) s + 1 - |read|`, where `s` counts the inner gates.
* `Frontier.Compiler.card_vertex_le`: there are at most `2 r s + 3 |O|` vertices.
-/

@[expose] public section

namespace Complexity.Frontier

namespace Compiler

open Cslib.Circuits Set

variable {σ : Signature} {n s : ℕ} {O : Type*} [Finite O] (p : Program σ n s) (out : O → Wire n s)

-- Every network in this file has finitely many outputs, though a few lemmas do not need it.
set_option linter.unusedSectionVars false

/-! ### Signals, consumers, and junctions -/

/-- A wire is *reachable* when it is an output or an argument of a reachable gate. -/
inductive Reach : Wire n s → Prop
  /-- The outputs are reachable. -/
  | out (o : O) : Reach (out o)
  /-- The arguments of a reachable gate are reachable. -/
  | arg {g : Fin s} (a : Fin (σ.Arity (p.lines g).op)) :
      Reach (.gate g) → Reach ((p.lines g).wires a)

/-- The *signals*: the reachable wires. -/
abbrev Signal : Type :=
  {w : Wire n s // Reach p out w}

/-- An argument slot of a reachable gate. -/
abbrev Slot : Type :=
  {t : Σ g : Fin s, Fin (σ.Arity (p.lines g).op) // Reach p out (.gate t.1)}

/-- A *consumer*: an argument slot of a reachable gate, or an output. -/
abbrev Consumer :=
  Slot p out ⊕ O

variable {p out}

/-- The signal read by a consumer. -/
def consumed : Consumer p out → Signal p out
  | .inl t => ⟨(p.lines t.1.1).wires t.1.2, .arg t.1.2 t.2⟩
  | .inr o => ⟨out o, .out o⟩

variable (p out)

/-- The number of consumers of a signal. -/
noncomputable def fanout (w : Signal p out) : ℕ :=
  Nat.card {c : Consumer p out // consumed c = w}

/-- A *junction*: a copy of a signal for one of its consumers. The junctions of a signal `w`
are numbered `0, ..., fanout w - 1`. -/
abbrev Junction : Type :=
  Σ w : Signal p out, Fin (fanout p out w)

/-- Junctions correspond to consumers. -/
noncomputable def junctionEquiv : Junction p out ≃ Consumer p out :=
  (Equiv.sigmaCongrRight fun w =>
      (Finite.equivFin {c : Consumer p out // consumed c = w}).symm).trans
    (Equiv.sigmaFiberEquiv consumed)

variable {p out}

/-- The consumer of a junction reads the junction's signal. -/
@[simp] theorem consumed_junctionEquiv (j : Junction p out) :
    consumed (junctionEquiv p out j) = j.1 :=
  ((Finite.equivFin {c : Consumer p out // consumed c = j.1}).symm j.2).2

/-- The junction of a consumer belongs to the consumed signal. -/
@[simp] theorem fst_junctionEquiv_symm (c : Consumer p out) :
    ((junctionEquiv p out).symm c).1 = consumed c := by
  rw [← consumed_junctionEquiv, Equiv.apply_symm_apply]

/-- Every signal has a consumer. -/
theorem fanout_pos (w : Signal p out) : 0 < fanout p out w := by
  obtain ⟨w, hw⟩ := w
  refine Nat.card_pos_iff.mpr ⟨?_, inferInstance⟩
  cases hw with
  | out o => exact ⟨⟨.inr o, rfl⟩⟩
  | arg a hg => exact ⟨⟨.inl ⟨⟨_, a⟩, hg⟩, rfl⟩⟩

/-! ### The graph -/

variable (p out)

/-- The vertices: one per signal, one per junction, and one per output. -/
inductive Vertex
  /-- The vertex of a signal: an input vertex or a gate vertex. -/
  | signal (w : Signal p out)
  /-- A junction. -/
  | junction (j : Junction p out)
  /-- The vertex of an output, which consumes it. -/
  | output (o : O)

/-- The edges: two per junction. -/
inductive Edge : Type
  /-- The edge into a junction from its predecessor in the chain. -/
  | feed (j : Junction p out)
  /-- The edge from a junction to its consumer. -/
  | deliver (j : Junction p out)

variable {p out}

/-- Vertices are signals, junctions, and outputs. -/
def Vertex.equiv : Vertex p out ≃ Signal p out ⊕ Junction p out ⊕ O where
  toFun
    | .signal w => .inl w
    | .junction j => .inr (.inl j)
    | .output o => .inr (.inr o)
  invFun
    | .inl w => .signal w
    | .inr (.inl j) => .junction j
    | .inr (.inr o) => .output o
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with w | j | o <;> rfl

/-- Edges are two copies of the junctions. -/
def Edge.equiv : Edge p out ≃ Junction p out ⊕ Junction p out where
  toFun
    | .feed j => .inl j
    | .deliver j => .inr j
  invFun
    | .inl j => .feed j
    | .inr j => .deliver j
  left_inv e := by cases e <;> rfl
  right_inv e := by rcases e with j | j <;> rfl

instance : Finite (Vertex p out) := Finite.of_equiv _ Vertex.equiv.symm

instance : Finite (Edge p out) := Finite.of_equiv _ Edge.equiv.symm

/-- The vertex that consumes through a consumer: a gate vertex or an output vertex. -/
def owner : Consumer p out → Vertex p out
  | .inl t => .signal ⟨.gate t.1.1, t.2⟩
  | .inr o => .output o

/-- The vertex feeding a junction: the signal itself for its first junction, and the previous
junction otherwise. -/
def feeder (j : Junction p out) : Vertex p out :=
  if j.2.val = 0 then .signal j.1
  else .junction ⟨j.1, ⟨j.2.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.2.isLt⟩⟩

omit [Finite O] in
/-- No junction feeds itself. -/
theorem feeder_ne_junction_self (j : Junction p out) : feeder j ≠ .junction j := by
  obtain ⟨w, k⟩ := j
  unfold feeder
  dsimp only
  split_ifs with hk
  · exact fun h => by cases h
  · intro h
    injection h with h
    have := congrArg (fun j : Junction p out => (j.2 : ℕ)) h
    dsimp only at this
    omega

/-- The source of an edge. -/
def src : Edge p out → Vertex p out
  | .feed j => feeder j
  | .deliver j => .junction j

/-- The target of an edge. -/
noncomputable def tgt : Edge p out → Vertex p out
  | .feed j => .junction j
  | .deliver j => owner (junctionEquiv p out j)

/-- The signal carried by an edge. -/
def Edge.signal : Edge p out → Signal p out
  | .feed j => j.1
  | .deliver j => j.1

/-- The edge delivering argument `a` to the reachable gate `g`. -/
noncomputable def argEdge {g : Fin s} (hg : Reach p out (.gate g))
    (a : Fin (σ.Arity (p.lines g).op)) : Edge p out :=
  .deliver ((junctionEquiv p out).symm (.inl ⟨⟨g, a⟩, hg⟩))

/-- The edge delivering an output to its output vertex. -/
noncomputable def outEdge (o : O) : Edge p out :=
  .deliver ((junctionEquiv p out).symm (.inr o))

/-- The first edge of a signal: the feed edge of its first junction. -/
def head (w : Signal p out) : Edge p out :=
  .feed ⟨w, ⟨0, fanout_pos w⟩⟩

@[simp] theorem signal_argEdge {g : Fin s} (hg : Reach p out (.gate g))
    (a : Fin (σ.Arity (p.lines g).op)) :
    (argEdge hg a).signal = ⟨(p.lines g).wires a, .arg a hg⟩ := by
  simp [argEdge, Edge.signal, consumed]

@[simp] theorem signal_outEdge (o : O) : (outEdge o : Edge p out).signal = ⟨out o, .out o⟩ := by
  simp [outEdge, Edge.signal, consumed]

@[simp] theorem tgt_argEdge {g : Fin s} (hg : Reach p out (.gate g))
    (a : Fin (σ.Arity (p.lines g).op)) : tgt (argEdge hg a) = .signal ⟨.gate g, hg⟩ := by
  simp [argEdge, tgt, owner]

@[simp] theorem tgt_outEdge (o : O) : tgt (outEdge o : Edge p out) = .output o := by
  simp [outEdge, tgt, owner]

/-- An edge leaving a signal vertex is the first edge of that signal. -/
theorem eq_head_of_src_eq_signal {e : Edge p out} {w : Signal p out}
    (h : src e = .signal w) : e = head w := by
  rcases e with ⟨w', k⟩ | j
  · simp only [src, feeder] at h
    split_ifs at h with hk
    cases h
    simp only [head, Edge.feed.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    exact Fin.ext hk
  · cases h

omit [Finite O] in
/-- An edge leaving a junction carries the junction's signal. -/
theorem signal_of_src_eq_junction {e : Edge p out} {j : Junction p out}
    (h : src e = .junction j) : e.signal = j.1 := by
  rcases e with ⟨w', k⟩ | j'
  · simp only [src, feeder] at h
    split_ifs at h with hk
    cases h
    rfl
  · cases h
    rfl

/-! ### The network -/

variable {U : Type*} (I : Interpretation σ U) (Acc : O → Set U)

/-- The value a signal vertex puts on its outgoing edge: the input itself for an input wire,
and the gate's operation applied to its incoming argument edges for a gate wire. -/
noncomputable def emit : (w : Wire n s) → Reach p out w → (Fin n → U) → (Edge p out → U) → U
  | .input i, _, x, _ => x i
  | .gate g, hg, _, α => I (p.lines g).op fun a => α (argEdge hg a)

/-- The constraint at each vertex. -/
noncomputable def check : Vertex p out → (Fin n → U) → (Edge p out → U) → Prop
  | .signal w, x, α => ∀ e, src e = .signal w → α e = emit I w.1 w.2 x α
  | .junction j, _, α => ∀ e, src e = .junction j → α e = α (.feed j)
  | .output o, _, α => α (outEdge o) ∈ Acc o

open Classical in
/-- Each reachable input is read at its signal vertex. -/
noncomputable def site (i : Fin n) : Option (Vertex p out) :=
  if h : Reach p out (.input i) then some (.signal ⟨.input i, h⟩) else none

omit [Finite O] in
theorem site_eq_some {i : Fin n} {v : Vertex p out} (h : site i = some v) :
    ∃ hi : Reach p out (.input i), v = .signal ⟨.input i, hi⟩ := by
  unfold site at h
  split_ifs at h with hi
  exact ⟨hi, (Option.some_injective _ h).symm⟩

omit [Finite O] in
theorem site_of_reach {i : Fin n} (hi : Reach p out (.input i)) :
    site i = some (.signal ⟨.input i, hi⟩ : Vertex p out) := by
  simp [site, hi]

variable (p out)

/-- **The constraint network of a program** with outputs `out`, accepting at the output `o` the
values in `Acc o`. -/
noncomputable def network : Network U (Fin n) (Vertex p out) (Edge p out) where
  src := src
  tgt := tgt
  site := site
  Check := check I Acc
  check_local v x x' α α' hx hα hc := by
    cases v with
    | signal w =>
      obtain ⟨w, hw⟩ := w
      intro e he
      rw [← hα e (Or.inl he), hc e he]
      cases w with
      | input i => exact hx i (site_of_reach hw)
      | gate g =>
        simp only [emit]
        congr 1
        funext a
        exact hα _ (Or.inr (tgt_argEdge hw a))
    | junction j =>
      intro e he
      rw [← hα e (Or.inl he), hc e he]
      exact hα _ (Or.inr rfl)
    | output o =>
      change α' (outEdge o) ∈ Acc o
      rw [← hα _ (Or.inr (tgt_outEdge o))]
      exact hc

variable {p out}

/-! ### Exactness -/

/-- The run of the program puts the value of each signal on each of its edges. -/
theorem trace_satisfies {x : Fin n → U} (hx : ∀ o, p.trace I x (out o) ∈ Acc o) :
    (network p out I Acc).Satisfies x fun e => p.trace I x e.signal.1 := by
  intro v
  cases v with
  | signal w =>
    obtain ⟨w, hw⟩ := w
    intro e he
    rw [eq_head_of_src_eq_signal he]
    cases w with
    | input i => rfl
    | gate g =>
      simp only [head, Edge.signal, emit]
      exact p.trace_gate I x g
  | junction j =>
    intro e he
    change p.trace I x e.signal.1 = p.trace I x j.1.1
    rw [signal_of_src_eq_junction he]
  | output o =>
    change p.trace I x (outEdge o).signal.1 ∈ Acc o
    simpa using hx o

section Satisfying

variable {I Acc} {x : Fin n → U} {α : Edge p out → U}
  (hα : (network p out I Acc).Satisfies x α)
include hα

/-- In a satisfying assignment, the feed edges along the junction chain of a signal all carry
the value of its first edge. -/
theorem feed_eq_head (w : Signal p out) :
    ∀ (k : ℕ) (hk : k < fanout p out w), α (.feed ⟨w, ⟨k, hk⟩⟩) = α (head w)
  | 0, _ => rfl
  | k + 1, hk => by
    have hprev : src (.feed ⟨w, ⟨k + 1, hk⟩⟩ : Edge p out) = .junction ⟨w, ⟨k, by omega⟩⟩ := by
      simp [src, feeder]
    rw [hα (.junction _) _ hprev]
    exact feed_eq_head w k _

/-- In a satisfying assignment, every edge carries the value of the first edge of its
signal. -/
theorem eq_head (e : Edge p out) : α e = α (head e.signal) := by
  rcases e with ⟨w, k⟩ | ⟨w, k⟩
  · exact feed_eq_head hα w k k.isLt
  · rw [hα (.junction ⟨w, k⟩) (.deliver ⟨w, k⟩) rfl]
    exact feed_eq_head hα w k k.isLt

/-- In a satisfying assignment, every signal carries its value in the run of the program. -/
theorem head_eq_trace : ∀ (w : Wire n s) (hw : Reach p out w), α (head ⟨w, hw⟩) = p.trace I x w
  | .input i, hw => hα (.signal ⟨.input i, hw⟩) _ rfl
  | .gate g, hw => by
    rw [hα (.signal ⟨.gate g, hw⟩) _ rfl, p.trace_gate I x g]
    simp only [emit]
    congr 1
    funext a
    rw [eq_head hα, signal_argEdge]
    exact head_eq_trace _ _
termination_by w => match w with | .input _ => 0 | .gate g => g.val + 1
decreasing_by
  generalize hw' : (p.lines g).wires a = w' at *
  cases w' with
  | input => simp
  | gate g' => simpa using p.lines_wires_eq_gate_lt g a hw'

/-- **Uniqueness.** A satisfying assignment puts on every edge the value of its signal in the
run of the program. -/
theorem eq_trace (e : Edge p out) : α e = p.trace I x e.signal.1 := by
  rw [eq_head hα, head_eq_trace hα]

end Satisfying

/-- **Exactness.** The network accepts exactly the inputs on which every output `o` lies in
`Acc o`. -/
theorem accepted_network :
    (network p out I Acc).accepted = {x | ∀ o, p.trace I x (out o) ∈ Acc o} := by
  ext x
  constructor
  · rintro ⟨α, hα⟩ o
    have hacc : α (outEdge o) ∈ Acc o := hα (.output o)
    rwa [eq_trace hα, signal_outEdge] at hacc
  · exact fun hx => ⟨_, trace_satisfies I Acc hx⟩

/-! ### Outputs across a cut -/

/-- **Outputs across a cut.** In the network of a program computing a function (every value
accepted at every output), let the runs on two inputs `x` and `y` agree on the cut of a set of
vertices `P`, and let `z` read like `x` at `P` and like `y` elsewhere. Then the outputs of `z`
are those of `x` at the output vertices in `P` and those of `y` at the others. -/
theorem trace_out_of_cut {P : Set (Vertex p out)} {x y z : Fin n → U}
    (hcut : ∀ e ∈ (network p out I fun _ => univ).cut P,
      p.trace I x e.signal.1 = p.trace I y e.signal.1)
    (hzx : EqOn z x ((network p out I fun _ => univ).readIn P))
    (hzy : EqOn z y ((network p out I fun _ => univ).readIn P)ᶜ) (o : O) :
    (Vertex.output o ∈ P → p.trace I z (out o) = p.trace I x (out o)) ∧
      (Vertex.output o ∉ P → p.trace I z (out o) = p.trace I y (out o)) := by
  have hx := trace_satisfies (p := p) (out := out) (x := x) I (fun _ => univ) fun _ => trivial
  have hy := trace_satisfies (p := p) (out := out) (x := y) I (fun _ => univ) fun _ => trivial
  obtain ⟨γ, hγ, hγx, hγy⟩ := hx.splice hy (fun e he => hcut e he) hzx hzy
  have hz : p.trace I z (out o) = γ (outEdge o) := by
    rw [eq_trace hγ, signal_outEdge]
  rw [hz]
  refine ⟨fun ho => ?_, fun ho => ?_⟩
  · rw [hγx (Or.inr (by simpa [network] using ho))]
    simp only [signal_outEdge]
  · by_cases ht : outEdge o ∈ (network p out I fun _ => univ).touching P
    · -- The edge reaches into `P` from outside, so it lies on the cut.
      have hc : outEdge o ∈ (network p out I fun _ => univ).cut P := by
        rcases ht with ht | ht
        · simp only [Multigraph.mem_cut, ht, true_iff]
          simpa [network] using ho
        · exact absurd (by simpa [network] using ht) ho
      rw [hγx ht]
      simpa only [signal_outEdge] using hcut _ hc
    · rw [hγy ht]
      simp only [signal_outEdge]

/-! ### The shape of the graph -/

/-- The graph has no loops. -/
theorem loopless : (network p out I Acc).Loopless := by
  rintro (⟨w, k⟩ | j) h
  · exact feeder_ne_junction_self _ h
  · simp only [network, src, tgt] at h
    rcases hj : junctionEquiv p out j with t | o <;> rw [hj] at h <;> cases h

/-! ### Degrees -/

/-- The edge delivering a slot's signal to its gate. -/
noncomputable def slotEdge (t : Slot p out) : Edge p out :=
  .deliver ((junctionEquiv p out).symm (.inl t))

omit [Finite O] in
/-- A gate has at most `r` slots when the fan-in is at most `r`. -/
theorem ncard_slots_le {r : ℕ} (hfan : p.FanInAtMost r) (w : Wire n s) :
    {t : Slot p out | Wire.gate t.1.1 = w}.ncard ≤ r := by
  calc {t : Slot p out | Wire.gate t.1.1 = w}.ncard
      ≤ ((Finset.range r : Finset ℕ) : Set ℕ).ncard := by
        refine ncard_le_ncard_of_injOn (fun t => t.1.2.val) ?_ ?_ (toFinite _)
        · intro t _
          simpa using t.1.2.isLt.trans_le (hfan.arity_le t.1.1)
        · rintro ⟨⟨g, a⟩, hg⟩ hw ⟨⟨g', a'⟩, hg'⟩ hw' haa'
          simp only [mem_ofPred_eq] at hw hw'
          obtain rfl : g = g' := Wire.gate.inj (hw.trans hw'.symm)
          obtain rfl : a = a' := Fin.ext haa'
          rfl
    _ = r := by rw [ncard_coe_finset, Finset.card_range]

/-- An edge entering a signal vertex delivers one of the slots of its gate. -/
theorem exists_slot_of_tgt_eq_signal {e : Edge p out} {w : Signal p out}
    (h : tgt e = .signal w) : ∃ t : Slot p out, Wire.gate t.1.1 = w.1 ∧ e = slotEdge t := by
  rcases e with j | j
  · cases h
  · simp only [tgt] at h
    rcases hj : junctionEquiv p out j with t | o <;> rw [hj] at h
    · simp only [owner, Vertex.signal.injEq] at h
      exact ⟨t, congrArg Subtype.val h, by simp [slotEdge, ← hj]⟩
    · cases h

omit [Finite O] in
/-- Two junctions fed by the same junction are equal. -/
theorem eq_of_feeder_eq_junction {j₁ j₂ j : Junction p out} (h₁ : feeder j₁ = .junction j)
    (h₂ : feeder j₂ = .junction j) : j₁ = j₂ := by
  obtain ⟨w₁, k₁⟩ := j₁
  obtain ⟨w₂, k₂⟩ := j₂
  unfold feeder at h₁ h₂
  dsimp only at h₁ h₂
  split_ifs at h₁ h₂ with hk₁ hk₂
  injection h₁ with h₁
  injection h₂ with h₂
  have hw := (congrArg Sigma.fst h₁).trans (congrArg Sigma.fst h₂).symm
  dsimp only at hw
  subst hw
  have hr := (congrArg (fun j : Junction p out => (j.2 : ℕ)) h₁).trans
    (congrArg (fun j : Junction p out => (j.2 : ℕ)) h₂).symm
  dsimp only at hr
  obtain rfl : k₁ = k₂ := Fin.ext (by omega)
  rfl

/-- **The degrees are bounded.** When the gates have fan-in at most `r ≥ 2`, every vertex has
degree at most `r + 1`: a gate vertex has its argument edges and one outgoing edge, a junction
has three edges, and input vertices and output vertices have one. For fan-in two the graph is
subcubic. -/
theorem maxDegreeLE {r : ℕ} (hr : 2 ≤ r) (hfan : p.FanInAtMost r) :
    (network p out I Acc).MaxDegreeLE (r + 1) := by
  intro v
  cases v with
  | signal w =>
    -- The first edge of the signal, and the edges delivering the slots of its gate.
    calc ((network p out I Acc).edgesAt (.signal w)).ncard
        ≤ (insert (head w) (slotEdge '' {t : Slot p out | Wire.gate t.1.1 = w.1})).ncard := by
          refine ncard_le_ncard (fun e he => ?_) (toFinite _)
          rcases he with he | he
          · exact Or.inl (eq_head_of_src_eq_signal he)
          · obtain ⟨t, ht, rfl⟩ := exists_slot_of_tgt_eq_signal he
            exact Or.inr ⟨t, ht, rfl⟩
      _ ≤ (slotEdge '' {t : Slot p out | Wire.gate t.1.1 = w.1}).ncard + 1 := ncard_insert_le _ _
      _ ≤ {t : Slot p out | Wire.gate t.1.1 = w.1}.ncard + 1 := by
          gcongr; exact ncard_image_le (toFinite _)
      _ ≤ r + 1 := by have := ncard_slots_le (out := out) hfan w.1; omega
  | junction j =>
    -- Its feed and deliver edges, and the feed edge of the next junction.
    calc ((network p out I Acc).edgesAt (.junction j)).ncard
        ≤ (insert (Edge.feed j) (insert (Edge.deliver j)
            {e | ∃ j', feeder j' = .junction j ∧ e = Edge.feed j'})).ncard := by
          refine ncard_le_ncard (fun e he => ?_) (toFinite _)
          rcases he with he | he
          · rcases e with j' | j'
            · exact Or.inr (Or.inr ⟨j', he, rfl⟩)
            · cases he; exact Or.inr (Or.inl rfl)
          · rcases e with j' | j'
            · cases he; exact Or.inl rfl
            · simp only [network, tgt] at he
              rcases hj : junctionEquiv p out j' with t | o <;> rw [hj] at he <;> cases he
      _ ≤ {e | ∃ j', feeder j' = .junction j ∧ e = (.feed j' : Edge p out)}.ncard + 1 + 1 :=
          (ncard_insert_le _ _).trans (by gcongr; exact ncard_insert_le _ _)
      _ ≤ r + 1 := by
          have : {e | ∃ j', feeder j' = .junction j ∧ e = (.feed j' : Edge p out)}.ncard ≤ 1 :=
            (ncard_le_one (toFinite _)).mpr fun _ ⟨j₁, h₁, he₁⟩ _ ⟨j₂, h₂, he₂⟩ =>
              he₁.trans ((eq_of_feeder_eq_junction h₁ h₂) ▸ he₂.symm)
          omega
  | output o =>
    -- Only the edge delivering the output.
    calc ((network p out I Acc).edgesAt (.output o)).ncard
        ≤ ({outEdge o} : Set (Edge p out)).ncard := by
          refine ncard_le_ncard (fun e he => ?_) (toFinite _)
          rcases he with he | he
          · rcases e with j | j
            · simp only [network, src, feeder] at he; split_ifs at he
            · cases he
          · rcases e with j | j
            · cases he
            · simp only [network, tgt] at he
              rcases hj : junctionEquiv p out j with t | o' <;> rw [hj] at he
              · cases he
              · cases he; simp [outEdge, ← hj]
      _ ≤ r + 1 := by simp

/-! ### Connectivity -/

/-- Every junction of a signal is joined to the signal along its chain. -/
theorem reflTransGen_junction_signal (w : Signal p out) :
    ∀ (k : ℕ) (hk : k < fanout p out w),
      Relation.ReflTransGen (network p out I Acc).Adj (.junction ⟨w, ⟨k, hk⟩⟩) (.signal w)
  | 0, _ => .single ⟨.feed ⟨w, ⟨0, _⟩⟩, Or.inr ⟨by simp [network, src, feeder], rfl⟩⟩
  | k + 1, hk => .head ⟨.feed ⟨w, ⟨k + 1, hk⟩⟩, Or.inr ⟨by simp [network, src, feeder], rfl⟩⟩
      (reflTransGen_junction_signal w k (by omega))

/-- Every junction is joined to its signal. -/
theorem reflTransGen_junction (j : Junction p out) :
    Relation.ReflTransGen (network p out I Acc).Adj (.junction j) (.signal j.1) :=
  reflTransGen_junction_signal I Acc j.1 j.2.val j.2.isLt

/-- Each output signal is joined to its output vertex. -/
theorem reflTransGen_out (o : O) :
    Relation.ReflTransGen (network p out I Acc).Adj (.signal ⟨out o, .out o⟩) (.output o) := by
  have hj := reflTransGen_junction I Acc ((junctionEquiv p out).symm (.inr o))
  rw [fst_junctionEquiv_symm] at hj
  exact (Multigraph.reflTransGen_adj_symm hj).tail ⟨outEdge o, Or.inl ⟨rfl, tgt_outEdge o⟩⟩

/-- Each argument of a reachable gate is joined to the gate, along its chain. -/
theorem reflTransGen_arg {g : Fin s} (hg : Reach p out (.gate g))
    (a : Fin (σ.Arity (p.lines g).op)) :
    Relation.ReflTransGen (network p out I Acc).Adj (.signal ⟨_, .arg a hg⟩)
      (.signal ⟨.gate g, hg⟩) := by
  have hj := reflTransGen_junction I Acc ((junctionEquiv p out).symm (.inl ⟨⟨g, a⟩, hg⟩))
  rw [fst_junctionEquiv_symm] at hj
  exact (Multigraph.reflTransGen_adj_symm hj).tail ⟨argEdge hg a, Or.inl ⟨rfl, tgt_argEdge hg a⟩⟩

omit [Finite O] in
/-- A wire upstream of an output is reachable. -/
theorem reach_of_upstream {o : O} {w : Wire n s} (h : p.Upstream (out o) w) : Reach p out w := by
  induction h with
  | refl => exact .out o
  | arg a _ ih => exact .arg a ih

/-- A wire upstream of an output is joined to the output vertex. -/
theorem reflTransGen_of_upstream {o : O} {w : Wire n s} (h : p.Upstream (out o) w)
    (hw : Reach p out w) :
    Relation.ReflTransGen (network p out I Acc).Adj (.signal ⟨w, hw⟩) (.output o) := by
  induction h with
  | refl => exact reflTransGen_out I Acc o
  | @arg g a hg ih =>
    have hg' := reach_of_upstream hg
    exact (reflTransGen_arg I Acc hg' a).trans (ih hg')

omit [Finite O] in
/-- Every reachable wire is upstream of some output. -/
theorem exists_upstream {w : Wire n s} (hw : Reach p out w) : ∃ o, p.Upstream (out o) w := by
  induction hw with
  | out o => exact ⟨o, .refl⟩
  | arg a _ ih => obtain ⟨o, ho⟩ := ih; exact ⟨o, .arg a ho⟩

/-- **The graph is connected** when some wire is upstream of every output. -/
theorem connected_of_upstream {w₀ : Wire n s} (h₀ : ∀ o, p.Upstream (out o) w₀) :
    (network p out I Acc).Connected := by
  -- Every vertex is joined to some output vertex, and every output vertex to `w₀`.
  have hout : ∀ v : Vertex p out, ∃ o, Relation.ReflTransGen (network p out I Acc).Adj v
      (.output o) := by
    intro v
    cases v with
    | signal w =>
      obtain ⟨o, ho⟩ := exists_upstream w.2
      exact ⟨o, reflTransGen_of_upstream I Acc ho w.2⟩
    | junction j =>
      obtain ⟨o, ho⟩ := exists_upstream j.1.2
      exact ⟨o, (reflTransGen_junction I Acc j).trans (reflTransGen_of_upstream I Acc ho _)⟩
    | output o => exact ⟨o, .refl⟩
  have hw₀ : ∀ o, Reach p out w₀ := fun o => reach_of_upstream (h₀ o)
  intro u v
  obtain ⟨o, hu⟩ := hout u
  obtain ⟨o', hv⟩ := hout v
  exact (hu.trans (Multigraph.reflTransGen_adj_symm
    (reflTransGen_of_upstream I Acc (h₀ o) (hw₀ o)))).trans
    ((reflTransGen_of_upstream I Acc (h₀ o') (hw₀ o')).trans (Multigraph.reflTransGen_adj_symm hv))

/-- **The graph of a circuit with one output is connected.** -/
theorem connected [Subsingleton O] : (network p out I Acc).Connected := by
  rcases isEmpty_or_nonempty O with hO | ⟨⟨o₀⟩⟩
  · intro u v
    cases u with
    | signal w =>
      obtain ⟨o, -⟩ := exists_upstream w.2
      exact isEmptyElim o
    | junction j =>
      obtain ⟨o, -⟩ := exists_upstream j.1.2
      exact isEmptyElim o
    | output o => exact isEmptyElim o
  · exact connected_of_upstream I Acc (w₀ := out o₀) fun o => Subsingleton.elim o₀ o ▸ .refl

/-! ### Counting -/

/-- The inputs read by the network are the reachable inputs. -/
theorem read_network : (network p out I Acc).read = {i | Reach p out (.input i)} := by
  ext i
  simp only [Network.read, Network.readIn, mem_univ, true_and, mem_ofPred_eq, network]
  constructor
  · rintro ⟨v, hv⟩; exact (site_eq_some hv).1
  · exact fun hi => ⟨_, site_of_reach hi⟩

/-- Each vertex reads at most one input. -/
theorem ncard_readAt_le (v : Vertex p out) : ((network p out I Acc).readAt v).ncard ≤ 1 := by
  refine (ncard_le_one (toFinite _)).mpr fun i hi i' hi' => ?_
  obtain ⟨_, rfl⟩ := site_eq_some hi
  obtain ⟨_, h⟩ := site_eq_some hi'
  simp only [Vertex.signal.injEq, Subtype.mk.injEq, Wire.input.injEq] at h
  exact h

/-- Signals are reachable inputs and reachable gates. -/
def signalEquiv :
    Signal p out ≃
      {i : Fin n // Reach p out (.input i)} ⊕ {g : Fin s // Reach p out (.gate g)} where
  toFun
    | ⟨.input i, h⟩ => .inl ⟨i, h⟩
    | ⟨.gate g, h⟩ => .inr ⟨g, h⟩
  invFun
    | .inl i => ⟨.input i.1, i.2⟩
    | .inr g => ⟨.gate g.1, g.2⟩
  left_inv w := by rcases w with ⟨w | w, h⟩ <;> rfl
  right_inv w := by rcases w with w | w <;> rfl

variable (p out) in
/-- The reachable inner gates: reachable gates of positive arity. -/
abbrev InnerGate : Type :=
  {g : Fin s // Reach p out (.gate g) ∧ σ.Arity (p.lines g).op ≠ 0}

omit [Finite O] in
theorem card_innerGate_le : Nat.card (InnerGate p out) ≤ p.innerGates.card := by
  calc Nat.card (InnerGate p out)
      ≤ Nat.card p.innerGates :=
        Nat.card_le_card_of_injective (fun g => ⟨g.1, by simpa [Program.innerGates] using g.2.2⟩)
          fun _ _ h => Subtype.ext (by simpa using h)
    _ = p.innerGates.card := Nat.card_eq_finsetCard _

omit [Finite O] in
/-- There are at most `r` slots per reachable inner gate; constant gates have none. -/
theorem card_slot_le {r : ℕ} (hfan : p.FanInAtMost r) :
    Nat.card (Slot p out) ≤ r * Nat.card (InnerGate p out) := by
  calc Nat.card (Slot p out)
      ≤ Nat.card (InnerGate p out × Fin r) := by
        refine Nat.card_le_card_of_injective
          (fun t => (⟨t.1.1, t.2, Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt t.1.2.isLt)⟩,
            ⟨t.1.2.val, t.1.2.isLt.trans_le (hfan.arity_le t.1.1)⟩)) ?_
        rintro ⟨⟨g, a⟩, hg⟩ ⟨⟨g', a'⟩, hg'⟩ h
        simp only [Prod.mk.injEq, Subtype.mk.injEq, Fin.mk.injEq] at h
        obtain ⟨rfl, haa'⟩ := h
        obtain rfl : a = a' := Fin.ext haa'
        rfl
    _ = r * Nat.card (InnerGate p out) := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin, mul_comm]

omit [Finite O] in
/-- There are at least as many reachable gates as reachable inner gates. -/
theorem card_innerGate_le_card_gate :
    Nat.card (InnerGate p out) ≤ Nat.card {g : Fin s // Reach p out (.gate g)} :=
  Nat.card_le_card_of_injective (fun g => ⟨g.1, g.2.1⟩) fun _ _ h =>
    Subtype.ext (by simpa using h)

/-- The cardinalities of the network, in terms of signals and consumers. -/
theorem card_edge : Nat.card (Edge p out) = 2 * Nat.card (Consumer p out) := by
  rw [Nat.card_congr Edge.equiv, Nat.card_sum, Nat.card_congr (junctionEquiv p out), two_mul]

theorem card_vertex :
    Nat.card (Vertex p out) = Nat.card (Signal p out) + Nat.card (Consumer p out) + Nat.card O := by
  rw [Nat.card_congr Vertex.equiv, Nat.card_sum, Nat.card_sum, Nat.card_congr (junctionEquiv p out),
    add_assoc]

theorem card_consumer : Nat.card (Consumer p out) = Nat.card (Slot p out) + Nat.card O :=
  Nat.card_sum

/-- Every signal has a consumer, so there are at least as many consumers as signals. -/
theorem card_signal_le_card_consumer : Nat.card (Signal p out) ≤ Nat.card (Consumer p out) := by
  rw [← Nat.card_congr (junctionEquiv p out)]
  exact Nat.card_le_card_of_injective (fun w => ⟨w, ⟨0, fanout_pos w⟩⟩) fun w w' h =>
    congrArg Sigma.fst h

/-- **The edge count.** For fan-in at most `r`, the edges of the network and the inputs it reads
number at most `(r - 1) s` more than its vertices, where `s` counts the inner gates. -/
theorem card_edge_add_ncard_read_le {r : ℕ} (hfan : p.FanInAtMost r) :
    Nat.card (Edge p out) + (network p out I Acc).read.ncard ≤
      Nat.card (Vertex p out) + (r - 1) * p.innerGates.card := by
  have hread :
      (network p out I Acc).read.ncard = Nat.card {i : Fin n // Reach p out (.input i)} := by
    rw [read_network, ← Nat.card_coe_set_eq]; rfl
  have hsig := Nat.card_congr (signalEquiv (p := p) (out := out))
  rw [Nat.card_sum] at hsig
  have hcons := card_consumer (p := p) (out := out)
  have hslot := card_slot_le (out := out) hfan
  have hinner := card_innerGate_le_card_gate (p := p) (out := out)
  -- `r G ≤ (r - 1) G + G`, for `G` the number of reachable inner gates.
  have hr : r * Nat.card (InnerGate p out) ≤
      (r - 1) * Nat.card (InnerGate p out) + Nat.card (InnerGate p out) := by
    rcases r with _ | r
    · simp
    · simp [add_mul]
  have hrs := Nat.mul_le_mul_left (r - 1) (card_innerGate_le (p := p) (out := out))
  rw [hread, card_edge, card_vertex]
  omega

/-- **The cycle rank.** For fan-in at most `r`, if the network is connected, its cycle rank and
the number of inputs it reads add up to at most `(r - 1) s + 1`, where `s` counts the inner
gates. For fan-in two, the cycle rank is at most `s + 1 - m` for `m` reachable inputs. -/
theorem cycleRank_add_ncard_read_le {r : ℕ} (hfan : p.FanInAtMost r)
    (hconn : (network p out I Acc).Connected) :
    (network p out I Acc).cycleRank + (network p out I Acc).read.ncard ≤
      (r - 1) * p.innerGates.card + 1 := by
  have h := card_edge_add_ncard_read_le (out := out) I Acc hfan
  have hV : Nat.card (Vertex p out) ≤ Nat.card (Edge p out) + 1 := hconn.card_vertex_le
  unfold Multigraph.cycleRank
  omega

/-- **The number of vertices** is at most `2 r s + 3 |O|` for fan-in at most `r`, where `s`
counts the inner gates. -/
theorem card_vertex_le {r : ℕ} (hfan : p.FanInAtMost r) :
    Nat.card (Vertex p out) ≤ 2 * r * p.innerGates.card + 3 * Nat.card O := by
  have hcons := card_consumer (p := p) (out := out)
  have hslot := card_slot_le (out := out) hfan
  have := card_signal_le_card_consumer (p := p) (out := out)
  have hrs : r * Nat.card (InnerGate p out) ≤ r * p.innerGates.card :=
    Nat.mul_le_mul_left r (card_innerGate_le (p := p) (out := out))
  rw [card_vertex, mul_assoc]
  omega

end Compiler

end Complexity.Frontier
