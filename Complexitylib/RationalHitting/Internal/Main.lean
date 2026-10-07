/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.OutputComputation

/-!
# Rational hitting lists: main

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Main.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.ExecutableGenerator
open StackLanguage

/-- One fixed finite stack program computes the exact canonical list on literal
unary inputs, with a fixed polynomial bound on all actual stack steps. -/
theorem stack_implementation : StackImplementation := by
  obtain ⟨p⟩ := Runtime.raw_feasible
  let f : p.Registers → Fin (Fintype.card p.Registers+1) :=
    fun a => (Fintype.equivFin p.Registers a).castSucc
  have hf : Function.Injective f := by
    intro a b h
    apply (Fintype.equivFin p.Registers).injective
    exact Fin.castSucc_inj.mp h
  obtain ⟨C,k,hC,hk,hbound⟩ := (p.bound.comp (TimeBound.variable+1)).growth
  refine ⟨Fintype.card p.Registers,p.program.rename f,f p.input,f p.output,C,k,hC,hk,?_⟩
  intro n s hn hs
  obtain ⟨t,ht,he⟩ := p.correct (n,s)
  refine ⟨t,?_,?_⟩
  · have hb := hbound (n+s+1) (by omega)
    simp only [TimeBound.eval_comp,TimeBound.eval_add,TimeBound.eval_variable,
      TimeBound.eval_numeral] at hb
    have hlen : (unaryWord n s).length+1=n+s+1+1 := by simp [unaryWord];omega
    have ht' : t≤p.bound.eval ((unaryWord n s).length+1) := ht
    rw [hlen] at ht'
    exact ht'.trans hb
  · have hh := he.rename_single f hf
    simpa only [single,Function.comp_apply,id_eq] using hh

/-- The finite-state compilation of the uniform stack implementation. -/

theorem implementation : Implementation := implementation_of_stack stack_implementation

end RationalHitting.ExecutableGenerator

namespace RationalHitting

/-- A rational hitting list preserving every inverse domain, with invertible
values, canonical rational binary output, and polynomial deterministic
finite-state Turing time. -/
theorem main : MainStatement :=
  ExecutableGenerator.main_of_implementation ExecutableGenerator.implementation

end RationalHitting

end Complexity
