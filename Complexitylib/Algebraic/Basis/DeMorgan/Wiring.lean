/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Expression

/-!
# Zero-cost De Morgan wiring

A wiring specification selects an existing Boolean input or a hardwired
constant for each output. The type excludes charged logical operations, so
every compiled specification has zero standard De Morgan cost.
-/

@[expose] public section

namespace Algebraic
namespace DeMorgan

/-- One output of a pure wiring layer. -/
inductive Wiring (inputs : Nat)
  | input (index : Fin inputs)
  | constant (value : Bool)

namespace Wiring

/-- Interpret a wiring source against a concrete input assignment. -/
def eval (input : Fin inputs -> Bool) : Wiring inputs -> Bool
  | .input index => input index
  | .constant value => value

@[simp] theorem eval_input
    (input : Fin inputs -> Bool)
    (index : Fin inputs) :
    eval input (.input index) = input index := rfl

@[simp] theorem eval_constant
    (input : Fin inputs -> Bool)
    (value : Bool) :
    eval input (.constant value) = value := rfl

/-- Compile a wiring source to its zero-cost De Morgan expression. -/
def expression : Wiring inputs -> Expression inputs
  | .input index => .input index
  | .constant value => .constant value

@[simp] theorem expression_eval
    (source : Wiring inputs)
    (input : Fin inputs -> Bool) :
    source.expression.eval input = source.eval input := by
  cases source <;> rfl

@[simp] theorem expression_standardCost
    (source : Wiring inputs) :
    source.expression.standardCost = 0 := by
  cases source <;> rfl

theorem eval_finAppend
    (left : Fin leftCount -> Wiring inputs)
    (right : Fin rightCount -> Wiring inputs)
    (input : Fin inputs -> Bool)
    (index : Fin (leftCount + rightCount)) :
    (Fin.append left right index).eval input =
      Fin.append (fun leftIndex => (left leftIndex).eval input)
        (fun rightIndex => (right rightIndex).eval input) index := by
  refine Fin.addCases (fun leftIndex => ?_) (fun rightIndex => ?_) index
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_right, Fin.append_right]

theorem eval_finAppend_apply
    (left : Fin leftCount -> Fin width -> Wiring inputs)
    (right : Fin rightCount -> Fin width -> Wiring inputs)
    (input : Fin inputs -> Bool)
    (index : Fin (leftCount + rightCount))
    (bit : Fin width) :
    (Fin.append left right index bit).eval input =
      Fin.append
        (fun leftIndex bit => (left leftIndex bit).eval input)
        (fun rightIndex bit => (right rightIndex bit).eval input)
        index bit := by
  refine Fin.addCases (fun leftIndex => ?_) (fun rightIndex => ?_) index
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_right, Fin.append_right]

/-- Compile an arbitrary vector of input selections and constants. -/
def circuit
    (specification : Fin outputs -> Wiring inputs) :
    Circuit signature inputs
      (∑ output, (specification output).expression.gateCount) outputs :=
  Circuit.parallelFin outputs
    (fun output => (specification output).expression.gateCount)
    (fun output => (specification output).expression.circuit)

@[simp] theorem circuit_eval
    (specification : Fin outputs -> Wiring inputs)
    (input : Fin inputs -> Bool) :
    (circuit specification).eval interpretation input =
      fun output => (specification output).eval input := by
  funext output
  rw [circuit, Circuit.eval_parallelFin,
    Expression.circuit_eval, expression_eval]

@[simp] theorem circuit_cost
    (specification : Fin outputs -> Wiring inputs) :
    (circuit specification).cost standardCost = 0 := by
  rw [circuit, Circuit.cost_parallelFin]
  simp [Expression.circuit_cost]

end Wiring
end DeMorgan
end Algebraic
