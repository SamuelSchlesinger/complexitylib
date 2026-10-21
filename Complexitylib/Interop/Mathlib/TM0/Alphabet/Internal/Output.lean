/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Alphabet.Internal.Initialization
public import Complexitylib.Interop.Mathlib.TM0.Alphabet.Internal.Emission
public import Complexitylib.Interop.Cslib.FromMultiTape
import Complexitylib.Asymptotics

/-!
# Complete finite-alphabet computations on binary inputs

Parsing, source simulation, and encoded emission preserve complete words with
linear endpoint overhead. Invalid inputs halt before source execution. Source
bounds need only hold when the corresponding binary input satisfies the
chosen validity predicate.
-/

@[expose] public section

namespace Complexity.MathlibTM0.AlphabetMachine

variable {Input Output : Type} (M : AlphabetMachine Input Output)
variable (ci : FiniteAlphabetCode Input) (co : FiniteAlphabetCode Output)

lemma computes_proof {input : List Input} {output : List Output} {time : ℕ}
    (h : M.OutputsWithin input output time) :
    (machine M ci co).ComputesInTimeAndSpace (ci.encode input) (co.encode output)
      (2 * (ci.encode input).length + time + (co.size + 1) * output.length + 4)
      ((machine M ci co).spaceUsed ((machine M ci co).initCfg (ci.encode input))
        (2 * (ci.encode input).length + time + (co.size + 1) * output.length + 4)) := by
  obtain ⟨t, ht, c, hr, hh, ho⟩ := h
  have hm : M.simulatorSource.binary.run t
      (MarkedMachine.sourceCfg M.simulatorSource (Turing.TM0.init (M.inputCells true input))) =
      some (MarkedMachine.sourceCfg M.simulatorSource c) := by
    rw [MarkedMachine.source_run, hr]
    rfl
  have hs := (ready_sim M (ci.encode input) input).run t hm
  have he := hs.halt (by rw [MarkedMachine.source_step, hh]; rfl)
  have hem : Emitting M ci co (MarkedMachine.sourceCfg M.simulatorSource c).Tape []
      (liftCfg M ci co ((MathlibTM0.machine M.simulatorSource.binary).step
        ((MathlibTM0.machine M.simulatorSource.binary).runFrom
          (readyCfg M (ci.encode input) input) t))) := by
    refine ⟨?_, he.output, he.tape⟩
    simp [liftCfg, Turing.Cfg.mapState, he.state]
  have hout := Emitting.run M ci co output hem (fun j => by
    rw [MarkedMachine.source_nth]
    exact ho j)
  have hrun : (machine M ci co).runFrom ((machine M ci co).initCfg (ci.encode input))
      ((2 * (ci.encode input).length + 2) + t + 1) =
      liftCfg M ci co ((MathlibTM0.machine M.simulatorSource.binary).step
        ((MathlibTM0.machine M.simulatorSource.binary).runFrom
          (readyCfg M (ci.encode input) input) t)) := by
    rw [run_succ_last, run_add, init_ready,
      lift_source_run M ci co (ready_sim M (ci.encode input) input) t hm]
    exact lift_step_of_run M ci co _ _ hs.state
  rw [← hrun, ← run_add] at hout
  have heq : ((2 * (ci.encode input).length + 2) + t + 1) +
      ((co.encode output).length + 1) =
      2 * (ci.encode input).length + t + (co.encode output).length + 4 := by omega
  rw [heq] at hout
  have hbound : 2 * (ci.encode input).length + t + (co.encode output).length + 4 ≤
      2 * (ci.encode input).length + time + (co.size + 1) * output.length + 4 := by
    have := FiniteAlphabetCode.encode_length_upper co output
    omega
  have hfreeze := (machine M ci co).runFrom_eq_of_halt
    ((machine M ci co).initCfg (ci.encode input)) hbound hout.1
  exact ⟨by rw [hfreeze]; exact hout.1, by rw [hfreeze]; exact hout.2, rfl⟩

lemma computes_with_bounds {f : List Input → List Output} {p q : Polynomial ℕ}
    {P : List Bool → Prop}
    (h : ∀ xs, P (ci.encode xs) → M.OutputsWithin xs (f xs) (p.eval xs.length))
    (hlen : ∀ xs, P (ci.encode xs) → (f xs).length ≤ q.eval xs.length)
    (w : List Bool) (hw : P w) :
    (machine M ci co).ComputesInTimeAndSpace w (ci.map co f w)
      (2 * w.length + p.eval w.length + (co.size + 1) * q.eval w.length + 4)
      ((machine M ci co).spaceUsed ((machine M ci co).initCfg w)
        (2 * w.length + p.eval w.length + (co.size + 1) * q.eval w.length + 4)) := by
  cases hd : ci.decode w with
  | none =>
      have hc := copy_invalid M ci co w hd
      have he := (machine M ci co).runFrom_eq_of_halt ((machine M ci co).initCfg w)
        (by omega : w.length + 1 ≤
          2 * w.length + p.eval w.length + (co.size + 1) * q.eval w.length + 4) hc.1
      refine ⟨by rw [he]; exact hc.1, ?_, rfl⟩
      rw [he]
      simpa [FiniteAlphabetCode.map, hd] using hc.2
  | some xs =>
      have he := FiniteAlphabetCode.encode_decode_proof ci hd
      have hp : P (ci.encode xs) := by rw [he]; exact hw
      have hc := computes_proof M ci co (h xs hp)
      rw [he] at hc
      have hsize : xs.length ≤ w.length := by
        simpa only [he] using FiniteAlphabetCode.encode_length_lower ci xs
      have hbound : 2 * w.length + p.eval xs.length + (co.size + 1) * (f xs).length + 4 ≤
          2 * w.length + p.eval w.length + (co.size + 1) * q.eval w.length + 4 := by
        have hp' := polynomial_eval_mono_nat p hsize
        have hq' := (hlen xs hp).trans (polynomial_eval_mono_nat q hsize)
        exact Nat.add_le_add_right (Nat.add_le_add
          (Nat.add_le_add_left hp' _) (Nat.mul_le_mul_left _ hq')) 4
      have hf := (machine M ci co).runFrom_eq_of_halt ((machine M ci co).initCfg w) hbound hc.1
      refine ⟨by rw [hf]; exact hc.1, ?_, rfl⟩
      rw [hf]
      simpa [FiniteAlphabetCode.map, hd] using hc.2.1

end Complexity.MathlibTM0.AlphabetMachine
