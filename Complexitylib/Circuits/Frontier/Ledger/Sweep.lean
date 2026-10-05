/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Ledger.Basic
public import Complexitylib.Circuits.Frontier.Compiler
import Mathlib.Tactic.Ring

/-!
# Sweeping a circuit with a ledger

Let a circuit with one output decide a set `S`, and let its special gates have a ledger in `M`.
Erase the special gates. A wire is *live* if it is an input or a gate of positive arity of the
erased program; the others are constants, among them the placeholders. Compile the erased
program with outputs the output of the circuit, accepting the same values, and every live wire,
accepting every value. Every live wire is then a signal of the network. For a guess `m ∈ M` the
network of the erased program runs the circuit with the placeholders reading their values from
`m`; its graph and its sites do not depend on `m`.

**The ledger sweep** (`Frontier.Ledger.sweep`) is the sweep along a layout
(`Frontier.Network.frontierSweep`) whose extra message has two parts: the product `m` of the
contributions of the true run (its consistent guess) and the product of the contributions of the
signals whose vertices come first (the *ledger so far*). Two inputs with the same message can be
spliced: the network of the erased program with guess `m` splices their runs (the separator
lemma), the two parts of the ledger multiply back to `m`, because the constant wires contribute
the same for every input, and a consistent guess yields the true run
(`Frontier.Ledger.mem_of_splice`).

**Transitions.** The extra messages take at most `|M|^3` pairs of values at each step
(`Frontier.Ledger.ncard_extra_le`). Inside a closed set of vertices `W`, the values of the run
on the edges at `W` depend only on the guess and the inputs read in `W`
(`Frontier.Ledger.run_eq_of_eqOn_readIn`), so the transitions inside `W` are bounded by the
inputs that `W` reads, however wide the layout is there.
-/

@[expose] public section

namespace Complexity.Frontier

namespace Ledger

open Cslib.Circuits Set

universe v

variable {U : Type*} {σ : Signature.{v}} {n : ℕ} {c : Circuit σ n 1} {I : Interpretation σ U}
  {special : ℕ → Prop} {M : Type*} [CommMonoid M] (L : Ledger c.program I special M)

/-! ### The network of the erased program -/

/-- A wire is *live* when it is an input or a gate of positive arity of the erased program. -/
def Live (c : Circuit σ n 1) (special : ℕ → Prop) (w : Wire n c.size) : Prop :=
  ∀ g, w = .gate g → (guessSignature σ).Arity ((erase special c.program).lines g).op ≠ 0

/-- The outputs of the erased program: the output of the circuit, and every live wire. -/
def outs (c : Circuit σ n 1) (special : ℕ → Prop) :
    Option {w : Wire n c.size // Live c special w} → Wire n c.size
  | none => c.outputs 0
  | some w => w.1

/-- The accepted values at the outputs of the erased program. -/
def accs (Acc : Set U) {α : Type*} : Option α → Set U
  | none => Acc
  | some _ => univ

/-- The vertices of the network of the erased program. -/
abbrev Vtx (c : Circuit σ n 1) (special : ℕ → Prop) :=
  Compiler.Vertex (erase special c.program) (outs c special)

/-- The edges of the network of the erased program. -/
abbrev Edg (c : Circuit σ n 1) (special : ℕ → Prop) :=
  Compiler.Edge (erase special c.program) (outs c special)

/-- The network of the erased program with the guess `m`, accepting the values in `Acc` at the
output of the circuit. -/
noncomputable abbrev net (Acc : Set U) (m : M) :=
  Compiler.network (erase special c.program) (outs c special)
    (guessInterpretation I (L.readout m)) (accs Acc)

/-- The network of the erased program with the guess `m`, accepting every value. -/
noncomputable abbrev fnet (m : M) :=
  Compiler.network (erase special c.program) (outs c special)
    (guessInterpretation I (L.readout m)) fun _ => univ

omit [CommMonoid M] in
/-- Live wires are signals. -/
theorem reach_of_live {w : Wire n c.size} (hw : Live c special w) :
    Compiler.Reach (erase special c.program) (outs c special) w :=
  .out (some (⟨w, hw⟩ : {w // Live c special w}))

/-- A wire that is not a signal is a constant gate of the erased program, so its value in a run
depends only on the guess. -/
theorem run_eq_of_not_reach (m : M) {w : Wire n c.size}
    (hw : ¬ Compiler.Reach (erase special c.program) (outs c special) w) (x y : Fin n → U) :
    L.run m x w = L.run m y w := by
  have hlive : ¬ Live c special w := fun h => hw (reach_of_live h)
  simp only [Live, not_forall] at hlive
  obtain ⟨g, rfl, hg⟩ := hlive
  have h0 : (guessSignature σ).Arity ((erase special c.program).lines g).op = 0 := not_not.mp hg
  rw [run, run, Program.trace_gate, Program.trace_gate]
  congr 1
  funext a
  have ha := a.isLt
  omega

/-- The wires whose vertices lie in `P`. -/
def wiresIn (P : Set (Vtx c special)) : Set (Wire n c.size) :=
  {w | ∃ hw, (.signal ⟨w, hw⟩ : Vtx c special) ∈ P}

open Classical in
/-- The product of the contributions of the wires in `Q`. -/
noncomputable def ledgerOn (Q : Set (Wire n c.size)) (v : Wire n c.size → U) : M :=
  ∏ w ∈ Finset.univ.filter (· ∈ Q), L.contribution w (v w)

theorem total_eq_mul (Q : Set (Wire n c.size)) (v : Wire n c.size → U) :
    L.total v = L.ledgerOn Q v * L.ledgerOn Qᶜ v := by
  classical
  rw [total, ledgerOn, ledgerOn, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ Q)]
  simp

/-! ### Splicing -/

/-- The true run satisfies the network of its consistent guess. -/
theorem satisfies_net {Acc : Set U} {x : Fin n → U}
    (hx : c.program.trace I x (c.outputs 0) ∈ Acc) :
    (L.net Acc (L.total (c.program.trace I x))).Satisfies x
      fun e => c.program.trace I x e.signal.1 := by
  have h := Compiler.trace_satisfies (p := erase special c.program) (out := outs c special)
    (x := x) (guessInterpretation I (L.readout (L.total (c.program.trace I x)))) (accs Acc)
    fun o => by
      rcases o with _ | w
      · change L.run _ x (c.outputs 0) ∈ Acc
        rwa [L.run_total_trace]
      · trivial
  convert h using 2 with e
  change _ = L.run _ x _
  rw [L.run_total_trace]

/-- **Splicing two inputs with the same message.** If the runs of two inputs of `S` have the
same consistent guess, the same ledger on `P`, and the same values on the cut of `P`, then the
input that reads like the first at `P` and like the second elsewhere lies in `S`. -/
theorem mem_of_splice {Acc : Set U} {P : Set (Vtx c special)} {x y z : Fin n → U}
    (hx : c.program.trace I x (c.outputs 0) ∈ Acc)
    (hy : c.program.trace I y (c.outputs 0) ∈ Acc)
    (hm : L.total (c.program.trace I x) = L.total (c.program.trace I y))
    (hpart : L.ledgerOn (wiresIn P) (c.program.trace I x) =
      L.ledgerOn (wiresIn P) (c.program.trace I y))
    (hcut : EqOn (fun e => c.program.trace I x e.signal.1)
      (fun e => c.program.trace I y e.signal.1) ((L.fnet 1).cut P))
    (hzx : EqOn z x ((L.fnet 1).readIn P)) (hzy : EqOn z y ((L.fnet 1).readIn P)ᶜ) :
    c.program.trace I z (c.outputs 0) ∈ Acc := by
  classical
  generalize hmdef : L.total (c.program.trace I y) = m
  have hαx := L.satisfies_net hx
  have hαy := L.satisfies_net hy
  rw [hm, hmdef] at hαx
  rw [hmdef] at hαy
  obtain ⟨γ, hγ, hγx, hγy⟩ := hαx.splice hαy hcut hzx hzy
  -- The spliced assignment is the run of `z` with the guess `m`.
  have hγrun : ∀ e, γ e = L.run m z e.signal.1 := fun e => Compiler.eq_trace hγ e
  -- On each wire, the run of `z` agrees with `x` at `P` and with `y` elsewhere.
  have hwire : ∀ w, L.run m z w =
      if w ∈ wiresIn P then c.program.trace I x w else c.program.trace I y w := by
    intro w
    by_cases hreach : Compiler.Reach (erase special c.program) (outs c special) w
    · have hhead : (Compiler.head ⟨w, hreach⟩ : Edg c special).signal.1 = w := rfl
      rw [← hhead, ← hγrun]
      split_ifs with hw
      · obtain ⟨_, hw⟩ := hw
        exact hγx (Or.inl hw)
      · have hw' : (.signal ⟨w, hreach⟩ : Vtx c special) ∉ P := fun h => hw ⟨hreach, h⟩
        by_cases ht : Compiler.head ⟨w, hreach⟩ ∈ (L.net Acc m).touching P
        · rw [hγx ht]
          refine hcut ?_
          rcases ht with ht | ht
          · exact absurd ht hw'
          · simp only [Multigraph.mem_cut]
            exact fun h => hw' (h.mpr ht)
        · exact hγy ht
    · have hw : w ∉ wiresIn P := fun ⟨h, _⟩ => hreach h
      simp only [hw, ite_false]
      rw [L.run_eq_of_not_reach m hreach z y, ← hmdef, L.run_total_trace]
  -- The ledger of the run of `z` is `m`, so the guess is consistent.
  have htotal : L.total (L.run m z) = m := by
    rw [L.total_eq_mul (wiresIn P)]
    conv_rhs => rw [← hmdef, L.total_eq_mul (wiresIn P) (c.program.trace I y)]
    congr 1
    · rw [← hpart, ledgerOn, ledgerOn]
      refine Finset.prod_congr rfl fun w hw => ?_
      have hw' : w ∈ wiresIn P := by simpa using hw
      rw [hwire]
      simp only [hw', ite_true]
    · rw [ledgerOn, ledgerOn]
      refine Finset.prod_congr rfl fun w hw => ?_
      have hw' : w ∉ wiresIn P := by simpa using hw
      rw [hwire]
      simp only [hw', ite_false]
  have hrun := L.run_eq_trace htotal
  -- The output check of the spliced assignment.
  have hout : γ (Compiler.outEdge none) ∈ Acc := hγ (.output none)
  rw [hγrun, Compiler.signal_outEdge, hrun] at hout
  exact hout

/-- **Locality inside a closed set.** For a fixed guess, the values of the run on the edges at a
closed set of vertices `W` depend only on the inputs read in `W`. -/
theorem run_eq_of_eqOn_readIn (m : M) {W : Set (Vtx c special)}
    (hW : (L.fnet m).cut W = ∅) {x x' : Fin n → U} (hxx' : EqOn x x' ((L.fnet m).readIn W))
    {e : Edg c special} (he : e ∈ (L.fnet m).touching W) :
    L.run m x e.signal.1 = L.run m x' e.signal.1 := by
  have hα := Compiler.trace_satisfies (p := erase special c.program) (out := outs c special)
    (x := x) (guessInterpretation I (L.readout m)) (fun _ => univ) fun _ => trivial
  have hα' := Compiler.trace_satisfies (p := erase special c.program) (out := outs c special)
    (x := x') (guessInterpretation I (L.readout m)) (fun _ => univ) fun _ => trivial
  obtain ⟨γ, hγ, hγx, -⟩ := hα.splice hα' (by rw [hW]; exact eqOn_empty _ _) hxx'.symm
    (eqOn_refl _ _)
  change (erase special c.program).trace _ x _ = (erase special c.program).trace _ x' _
  rw [← Compiler.eq_trace hγ e]
  exact (hγx he).symm

/-! ### The sweep -/

section Sweep

variable (Acc : Set U) (π : Layout (Vtx c special))

/-- Every input is read, at its own vertex. -/
theorem readIn_univ (m : M) : (L.fnet m).readIn univ = univ :=
  eq_univ_of_forall fun i => ⟨_, mem_univ _, Compiler.site_of_reach (reach_of_live (fun _ h =>
    by cases h))⟩

open Classical in
/-- The extra message at time `t`: the consistent guess and the ledger of the first `t`
vertices. After the last vertex it is empty. -/
noncomputable def extra (t : ℕ) (x : Fin n → U) : M × M :=
  if t ≤ Nat.card (Vtx c special) then
    (L.total (c.program.trace I x), L.ledgerOn (wiresIn (π.initial t)) (c.program.trace I x))
  else (1, 1)

/-- **The sweep of a circuit with a ledger**, along a layout of the network of its erased
program: the frontier sweep whose extra message is the guess and the ledger so far. -/
noncomputable def sweep :
    Sweep {x | c.program.trace I x (c.outputs 0) ∈ Acc} ((M × M) × (Edg c special → Option U)) :=
  (L.fnet 1).frontierSweep π (fun x e => c.program.trace I x e.signal.1) (L.extra π)
    (fun _ _ _ _ => by simp [extra])
    fun t ht x hx y hy hxy hval z hzx hzy => by
      simp only [extra, ht, ite_true, Prod.mk.injEq] at hxy
      exact L.mem_of_splice hx hy hxy.1 hxy.2 hval hzx hzy

variable {Acc}

/-- The extra messages take at most `|M|^3` pairs of values at each step. -/
theorem ncard_extra_le [Finite U] [Finite M] (t : ℕ) :
    ((fun x => (L.extra π t x, L.extra π (t + 1) x)) ''
      {x | c.program.trace I x (c.outputs 0) ∈ Acc}).ncard ≤ Nat.card M ^ 3 := by
  calc _ ≤ ((fun x => (L.total (c.program.trace I x),
        L.ledgerOn (wiresIn (π.initial t)) (c.program.trace I x),
        L.ledgerOn (wiresIn (π.initial (t + 1))) (c.program.trace I x))) ''
          {x | c.program.trace I x (c.outputs 0) ∈ Acc}).ncard := by
        refine ncard_image_le_ncard_image_of_determines (toFinite _) _ _
          fun x _ y _ hxy => ?_
        simp only [Prod.mk.injEq] at hxy
        simp only [extra, hxy.1, hxy.2.1, hxy.2.2]
    _ ≤ Nat.card (M × M × M) := ncard_le_card _
    _ = Nat.card M ^ 3 := by simp only [Nat.card_prod]; ring

/-- **Transitions inside a closed set.** If the vertex processed at step `t` lies in a closed
set `W` that contains both frontiers, a transition is determined by the guess, the two ledgers,
and the inputs read in `W`. -/
theorem ncard_transition_le_closed [Finite U] [Finite M] {t : ℕ}
    (ht : t < Nat.card (Vtx c special)) {W : Set (Vtx c special)}
    (hW : (L.fnet 1).cut W = ∅) (hv : π.symm ⟨t, ht⟩ ∈ W)
    (hC : (L.fnet 1).frontier π t ∪ (L.fnet 1).frontier π (t + 1) ⊆ (L.fnet 1).touching W) :
    ((L.sweep Acc π).transition t '' {x | c.program.trace I x (c.outputs 0) ∈ Acc}).ncard ≤
      Nat.card M ^ 3 * Nat.card U ^ ((L.fnet 1).readIn W).ncard := by
  refine ((L.fnet 1).ncard_transition_le_of_touching ht hv hC
    fun x _ y _ hxy _ hR e he => ?_).trans (Nat.mul_le_mul_right _ (L.ncard_extra_le π t))
  simp only [extra, ht.le, ite_true, Prod.mk.injEq] at hxy
  rw [← L.run_total_trace x, ← L.run_total_trace y, ← hxy.1]
  exact L.run_eq_of_eqOn_readIn (L.total (c.program.trace I x)) hW hR he

/-- **Transitions by width.** A transition is determined by the guess, the two ledgers, the
values on the two frontiers, and the input read at the vertex processed. -/
theorem ncard_transition_le_width [Finite U] [Finite M] {t : ℕ}
    (ht : t < Nat.card (Vtx c special)) :
    ((L.sweep Acc π).transition t '' {x | c.program.trace I x (c.outputs 0) ∈ Acc}).ncard ≤
      Nat.card M ^ 3 * Nat.card U ^ (((L.fnet 1).frontier π t ∪
        (L.fnet 1).frontier π (t + 1)).ncard + ((L.fnet 1).readAt (π.symm ⟨t, ht⟩)).ncard) :=
  ((L.fnet 1).ncard_transition_le ht).trans (Nat.mul_le_mul_right _ (L.ncard_extra_le π t))

/-- At the last step the transition is determined by the guess and the two ledgers, since every
input is read. -/
theorem ncard_transition_last_le [Finite U] [Finite M] :
    ((L.sweep Acc π).transition (Nat.card (Vtx c special)) ''
      {x | c.program.trace I x (c.outputs 0) ∈ Acc}).ncard ≤ Nat.card M ^ 3 := by
  have h : ((L.sweep Acc π).transition (Nat.card (Vtx c special)) ''
      {x | c.program.trace I x (c.outputs 0) ∈ Acc}).ncard ≤
      ((fun x => (L.extra π (Nat.card (Vtx c special)) x,
        L.extra π (Nat.card (Vtx c special) + 1) x)) ''
          {x | c.program.trace I x (c.outputs 0) ∈ Acc}).ncard *
        Nat.card U ^ ((L.fnet 1).read)ᶜ.ncard :=
    (L.fnet 1).ncard_transition_last_le
  replace h := h.trans (Nat.mul_le_mul_right _ (L.ncard_extra_le π _))
  have hread : ((L.fnet 1).read)ᶜ = ∅ := by
    rw [Network.read, L.readIn_univ, compl_univ]
  rwa [hread, ncard_empty, pow_zero, mul_one] at h

end Sweep

end Ledger

end Complexity.Frontier
