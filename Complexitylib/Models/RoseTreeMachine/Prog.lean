/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Complexitylib.Models.RoseTreeMachine.DataEncode
import Std.Tactic.BVDecide.Normalize.Prop


/-!
# Programs in a rose tree machine (RTM)

This file contains the main definition of the rose tree machine, its programs including
semantics and time and space resource consumption.

## Main definitions and notations

- `Prog` - the program
- `ProgSem` - semantics and resource consumption
- `InPlace` - a fragment of the language that can be easily simulated using multi-tape Turing
    machines.
- `Prog.ComputesInTimeAndSpace` - this defines the complexity notion for the RTM computation model,
    based on `Data` values.
- `Prog.ComputesBoolFunInTimeAndSpace` - the complexity notion transferred to functions on binary
    strings, this making it compatible to all other computation models.
- `ComputableInOTime` - generic time-complexity in the RTM model
- `ComputableInOSpace` - generic space-complexity in the RTM model
-/

@[expose] public section

namespace Complexity

namespace RoseTreeMachine

/--
Prog is the syntax representation of a functional language that has a resource consumption
model which is compatible to that of a Turing machine.
The data structure it operates on is a rose tree (`Data`). The advantage of this data structure
is that the majority of lean data types have a direct encoding.
-/
inductive Prog where
  /-- Variable reference at de Bruijn level `id`. -/
  | var (id : ℕ)
  /-- The empty constructor of `Data`. -/
  | empty
  /-- The `cons` constructor of `Data`: prepend the value of `h` to the list value of `t`. -/
  | cons (h t : Prog)
  /-- Destructor of `Data`: evaluate `v`; if it is `empty`, run `emp`; otherwise destructure into
      `head` and `tail` and apply the function `cs` to `head` and then to `tail`. -/
  | elim (v emp cs : Prog)
  /-- Equality comparison: If `x` evaluates to the same data as `y`, run `then_`, else
  run `else_`.
  This can be simulated using `while_` below, but it is useful to have. -/
  | ifEq (x y then_ else_ : Prog)
  /-- While loop: evaluate `init` to the starting accumulator; `body` must evaluate
      to a one-argument function which is applied to the current accumulator on each
      iteration. Return the accumulator if its head is empty. -/
  | while_ (init body : Prog)
  /-- Abstraction / closure in one variable. -/
  | fn (body : Prog)
  /-- Function application. -/
  | app (fn arg : Prog)
deriving Repr

/-- Runtime values for the semantics predicate `ProgSem`. -/
inductive Value where
  | data (d : Data)
  | closure (body : Prog) (env : List Value)
deriving Repr

/-- The empty `Value`, wrapping the empty `Data` node. -/
abbrev Value.empty : Value := .data (Data.l [])

/-- Whether the program `Prog` refers to the variable at de Bruijn index `i`. -/
def Prog.hasVar (i : ℕ) : Prog → Bool
  | .var j => i = j
  | .empty => false
  | .cons h t => h.hasVar i || t.hasVar i
  | .elim v emp cs => v.hasVar i || emp.hasVar i || cs.hasVar i
  | .ifEq x y then_ else_ =>
      x.hasVar i || y.hasVar i || then_.hasVar i || else_.hasVar i
  | .while_ init body => init.hasVar i || body.hasVar i
  | .fn body => body.hasVar i
  | .app f arg => f.hasVar i || arg.hasVar i


mutual
  /-- The size of a closure's environment, restricted to variables that `body` actually
  references. -/
  def closureSize (body : Prog) (env : List Value) : ℕ :=
    let rec go (depth : ℕ) (env : List Value) : ℕ :=
      match env with
      | [] => 0
      | hd :: tl => go (depth + 1) tl + if body.hasVar depth then hd.size else 0
    go 0 env

  /-- The size of a `Value`. The size of data is the length of its encoding and the size
  of a closure is the sum of the sizes of the referenced variables. -/
  @[simp]
  def Value.size : Value → ℕ
    | .data d => d.size
    | .closure p env => closureSize p env
end

-- `closureSize.go` is an internal helper generated from the `let rec` inside `closureSize`;
-- doc comments cannot be placed directly on `let rec` definitions (doing so breaks
-- elaboration), so the docBlame lint is suppressed here instead.
attribute [nolint docBlame] closureSize.go

@[simp, scoped grind =]
lemma closureSize_of_noVar {body : Prog} {env : List Value} (h : ∀ i, ¬body.hasVar i) :
    closureSize body env = 0 := by
  have (depth : ℕ) : closureSize.go body depth env = 0 := by
    induction env generalizing depth with
    | nil => simp [closureSize.go]
    | cons hd tl ih => simp [closureSize.go, h depth, ih]
  simp [closureSize, this]

@[simp, scoped grind =]
lemma closureSize_of_var {env : List Value} :
    closureSize (.var i) env = (env[i]?.map fun v => v.size).getD 0 := by
  unfold closureSize
  have (d : ℕ) : closureSize.go (.var i) d env =
      if h : d ≤ i ∧ i - d < env.length then (env[i - d]'(by grind)).size else 0 := by
    induction env generalizing d with
    | nil => simp [closureSize.go]
    | cons hd tl ih =>
      grind [closureSize.go, List.length_cons, Prog.hasVar]
  grind


@[scoped grind =]
lemma Value.size_data {d : Data} : (Value.data d).size = d.size := by simp [Value.size]

/-- Splitting the environment of a closure size computation across an append. -/
lemma closureSize.go_append (body : Prog) (depth : ℕ) (l1 l2 : List Value) :
    closureSize.go body depth (l1 ++ l2)
      = closureSize.go body depth l1 + closureSize.go body (depth + l1.length) l2 := by
  induction l1 generalizing depth with
  | nil => simp [closureSize.go]
  | cons hd tl ih =>
      have he : depth + 1 + tl.length = depth + (tl.length + 1) := by omega
      simp only [List.cons_append, closureSize.go, List.length_cons, ih (depth + 1), he]
      omega

/-- The closure size over an appended environment splits into the size over the prefix plus the
contribution of the suffix (counted starting at depth `l1.length`). -/
lemma closureSize_append (body : Prog) (l1 l2 : List Value) :
    closureSize body (l1 ++ l2)
      = closureSize body l1 + closureSize.go body l1.length l2 := by
  simp only [closureSize, closureSize.go_append, Nat.zero_add]

/-- `closureSize.go` is monotone in the set of accessed variables. -/
lemma closureSize.go_mono {body1 body2 : Prog} (env : List Value)
    (h : ∀ i, body1.hasVar i → body2.hasVar i) (depth : ℕ) :
    closureSize.go body1 depth env ≤ closureSize.go body2 depth env := by
  induction env generalizing depth with
  | nil => simp [closureSize.go]
  | cons hd tl ih =>
      simp only [closureSize.go]
      have hb : (if body1.hasVar depth then hd.size else 0)
          ≤ (if body2.hasVar depth then hd.size else 0) := by
        by_cases hv : body1.hasVar depth
        · simp [hv, h depth hv]
        · simp [hv]
      have := ih (depth + 1)
      omega

/-- If every variable accessed by `body1` is also accessed by `body2`, then `body1` has a smaller
closure size over any environment. -/
lemma closureSize_mono {body1 body2 : Prog} (env : List Value)
    (h : ∀ i, body1.hasVar i → body2.hasVar i) :
    closureSize body1 env ≤ closureSize body2 env := by
  have := closureSize.go_mono env h 0
  simpa only [closureSize] using this

/-- The closure size is bounded by the total size of the environment. -/
lemma closureSize.go_le_sum (body : Prog) (depth : ℕ) (env : List Value) :
    closureSize.go body depth env ≤ (env.map Value.size).sum := by
  induction env generalizing depth with
  | nil => simp [closureSize.go]
  | cons hd tl ih =>
      simp only [closureSize.go, List.map_cons, List.sum_cons]
      have h1 := ih (depth + 1)
      have h2 : (if body.hasVar depth then hd.size else 0) ≤ hd.size := by
        by_cases hv : body.hasVar depth <;> simp [hv]
      omega

mutual
/-- Semantics of `Prog` including time and space resource bounds.
`ProgSem σ p x t s` means that on environment `σ`, the program `p` evaluates to the value
`x` and uses `t` time and `s` space. -/
inductive ProgSem : (List Value) → Prog → Value → ℕ → ℕ → Prop
  | var :
      ProgSem σ (.var i) (σ[i]?.getD Value.empty)
        (σ[i]?.getD Value.empty).size (σ[i]?.getD Value.empty).size
  | empty : ProgSem σ .empty Value.empty 2 2
  | cons (h₁ : ProgSem σ head (.data hd) hd_t hd_s) (h₂ : ProgSem σ tail (.data tl) tl_t tl_s) :
      ProgSem σ (.cons head tail) (.data (Data.l (hd :: tl.asList))) (hd_t + tl_t) (hd_s + tl_s)
  /-- `elim`, empty branch: `v` is the empty list, so run `emp` in the current environment. -/
  | elim_nil
      (h₁ : ProgSem σ val (.data (Data.l [])) t_v s_v)
      (h₂ : ProgSem σ emp r t_emp s_emp) :
      ProgSem σ (.elim val emp cs) r (t_v + t_emp) (s_v + s_emp)
  /-- `elim`, cons branch: `v` destructures to `hd :: tl`; evaluate the function `cs` to a
      closure and apply it first to `hd` and then to `tl` (so `cs` is a curried
      two-argument function). -/
  | elim_cons
      (h_v : ProgSem σ val (.data (Data.l (hd :: tl))) t_v s_v)
      (h_cs : ProgSem σ cs cv t_cs s_cs)
      (h_app₁ : AppSem cv (.data hd) cv' t₁ s₁)
      (h_app₂ : AppSem cv' (.data (Data.l tl)) r t₂ s₂) :
      ProgSem σ (.elim val emp cs) r (t_v + t_cs + t₁ + t₂) (s_v + s_cs + s₁ + s₂)
  | ifEq_then
      (h_x : ProgSem σ x (.data vx) t_x s_x)
      (h_y : ProgSem σ y (.data vx) t_y s_y)
      (h_then : ProgSem σ then_ r t_then s_then) :
      ProgSem σ (.ifEq x y then_ else_) r (t_x + t_y + t_then) (s_x + s_y + s_then)
  | ifEq_else
      (h_x : ProgSem σ x (.data vx) t_x s_x)
      (h_y : ProgSem σ y (.data vy) t_y s_y)
      (h_neq : vx ≠ vy)
      (h_else : ProgSem σ else_ r t_else s_else) :
      ProgSem σ (.ifEq x y then_ else_) r (t_x + t_y + t_else) (s_x + s_y + s_else)
  /-- `while_ init body`: evaluate `init` to the starting accumulator and `body` to a
      one-argument closure, then iterate the closure via `WhileSem` until it halts. -/
  | while_
      (h_init : ProgSem σ init (.data acc) t_init s_init)
      (h_body : ProgSem σ body bodyVal t_body s_body)
      (h_while : WhileSem bodyVal acc r t_w s_w) :
      ProgSem σ (.while_ init body) (.data r) (t_init + t_body + t_w) (s_init + s_body + s_w)
  /-- `fn body`: evaluate to a closure capturing the current environment `σ`. The cost is the
      size of the resulting closure (mirroring `var`, which charges the size of the value it
      produces). -/
  | fn : ProgSem σ (.fn body) (.closure body σ)
        (Value.closure body σ).size (Value.closure body σ).size
  /-- `app fn arg`: evaluate `fn` to a closure, evaluate `arg` to a value, then run the
      closure's body in the *captured* environment extended with the argument (static
      scoping). -/
  | app
      (h_fn : ProgSem σ fn fv t_f s_f)
      (h_arg : ProgSem σ arg v t_a s_a)
      (h_app : AppSem fv v r t_b s_b) :
      ProgSem σ (.app fn arg) r (t_f + t_a + t_b) (s_f + s_a + s_b)

/-- Application of a value to an argument value. `AppSem f v r t s` means that applying the
closure `f` to the argument `v` yields `r` using `t` time and `s` space. Only closures can be
applied; applying a first-order value has no derivation (the program is stuck). -/
inductive AppSem : Value → Value → Value → ℕ → ℕ → Prop
  | mk (h_body : ProgSem (σ ++ [v]) body r t s) :
      AppSem (.closure body σ) v r t s

/-- Iterates the closure `bodyVal` of a `while_` loop, threading the accumulator.
`WhileSem bodyVal acc r t s` means that, starting from accumulator `acc`, repeatedly applying
`bodyVal` to the current accumulator eventually yields result `r` using `t` time and `s` space.
Before each iteration the halting condition is checked on the current accumulator: iteration
terminates (with the accumulator as result) when `acc` is empty or its head is empty.
Otherwise `bodyVal` is applied and its result becomes the new accumulator. Non-terminating
loops simply have no derivation. -/
inductive WhileSem : Value → Data → Data → ℕ → ℕ → Prop
  | halt
      (h_stop : acc.asList.head?.getD (Data.l []) = Data.l []) :
      WhileSem bodyVal acc acc acc.size acc.size
  | step
      (h_cont : acc.asList.head?.getD (Data.l []) ≠ Data.l [])
      (h_app : AppSem bodyVal (.data acc) (.data v) t_b s_b)
      (h_rest : WhileSem bodyVal v r t_r s_r) :
      WhileSem bodyVal acc r (t_b + t_r) (max s_b s_r)
end

/-- Producing a value costs at least its size, in both time and space. This holds because every
`ProgSem` derivation either reads/builds the value directly (charging its size) or returns a
value produced by a sub-derivation whose cost it includes. Provable by mutual induction over
`ProgSem`/`AppSem`/`WhileSem`. -/
lemma ProgSem.size_le {σ : List Value} {p : Prog} {v : Value} {t s : ℕ}
    (h : ProgSem σ p v t s) : v.size ≤ t ∧ v.size ≤ s := by
  induction h using ProgSem.rec
    (motive_2 := fun _ _ r t s _ => r.size ≤ t ∧ r.size ≤ s)
    (motive_3 := fun _ _ r t s _ => (Value.data r).size ≤ t ∧ (Value.data r).size ≤ s) with
  | empty => exact ⟨by simp, by simp⟩
  | var | cons | elim_nil | elim_cons | ifEq_then | ifEq_else
  | while_ | fn | app  | mk | halt | step
    => grind [Value.size_data, Data.cons_size, Data.asList_l]

/-- Value-determinism of the relational semantics: a program evaluates to at most one value in a
given environment. The mutually-defined `AppSem`/`WhileSem` relations are value-deterministic too.
The potential branch overlaps (`elim_nil`/`elim_cons`, `ifEq_then`/`ifEq_else`) are ruled out by
value-determinism of the scrutinee / compared values, supplied by the induction hypotheses. -/
theorem ProgSem.value_det {σ : List Value} {p : Prog} {v₁ : Value} {t₁ s₁ : ℕ}
    (h₁ : ProgSem σ p v₁ t₁ s₁) :
    ∀ (v₂ : Value) (t₂ s₂ : ℕ), ProgSem σ p v₂ t₂ s₂ → v₁ = v₂ := by
  induction h₁ using ProgSem.rec
    (motive_2 := fun f a r₁ _ _ _ =>
      ∀ (r₂ : Value) (t₂ s₂ : ℕ), AppSem f a r₂ t₂ s₂ → r₁ = r₂)
    (motive_3 := fun b acc r₁ _ _ _ =>
      ∀ (r₂ : Data) (t₂ s₂ : ℕ), WhileSem b acc r₂ t₂ s₂ → r₁ = r₂) with
  | var | empty | fn => rintro _ _ _ h₂; cases h₂; rfl
  | cons _ _ ih₁ ih₂ =>
    rintro _ _ _ h₂; cases h₂ with
    | cons h₁' h₂' => have := ih₁ _ _ _ h₁'; have := ih₂ _ _ _ h₂'; grind
  | elim_nil _ _ ih_v _ =>
    rintro _ _ _ h₂; cases h₂ with
    | elim_nil h_v' _ => grind
    | elim_cons h_v' _ _ _ => have := ih_v _ _ _ h_v'; grind
  | elim_cons _ _ _ _ ih_v ih_cs ih₁ ih₂ =>
    rintro _ _ _ h₂; cases h₂ with
    | elim_nil h_v' _ => have := ih_v _ _ _ h_v'; grind
    | elim_cons h_v' h_cs' h_a₁' h_a₂' =>
      have := ih_v _ _ _ h_v'; have := ih_cs _ _ _ h_cs'
      grind
  | ifEq_then _ _ _ ih_x ih_y ih_then =>
    rintro _ _ _ h₂; cases h₂ with
    | ifEq_then h_x' _ h_then' => have := ih_then _ _ _ h_then'; grind
    | ifEq_else h_x' h_y' h_neq _ =>
      have := ih_x _ _ _ h_x'; have := ih_y _ _ _ h_y'; grind
  | ifEq_else _ _ _ _ ih_x ih_y ih_else =>
    rintro _ _ _ h₂; cases h₂ with
    | ifEq_then h_x' h_y' _ => have := ih_x _ _ _ h_x'; have := ih_y _ _ _ h_y'; grind
    | ifEq_else _ _ _ h_else' => have := ih_else _ _ _ h_else'; grind
  | while_ _ _ _ ih_init ih_body ih_while =>
    rintro _ _ _ h₂; cases h₂ with
    | while_ h_init' h_body' h_while' =>
      have := ih_init _ _ _ h_init'; have := ih_body _ _ _ h_body'; grind
  | app _ _ _ ih_fn ih_arg ih_app =>
    rintro _ _ _ h₂; cases h₂ with
    | app h_fn' h_arg' h_app' =>
      have := ih_fn _ _ _ h_fn'; have := ih_arg _ _ _ h_arg'; grind
  | mk _ ih_body =>
    rename_i h₂; cases h₂ with
    | mk h_body' => exact ih_body _ _ _ h_body'
  | halt _
  | step _ _ _ ih_app ih_rest =>
    rename_i h₂; cases h₂ with
    | halt h_stop => grind
    | step _ h_app' h_rest' => grind

/-- The program `p` computes the value `y` from the value `x` in time `t` and space `s`. -/
def Prog.ComputesInTimeAndSpace (p : Prog) (x y : Data) (t : ℕ) (s : ℕ) : Prop :=
  ProgSem [.data x] p (.data y) t s


/-- The program `p` computes the function `f` (on binary strings) in time `t` and space `s`.
This is the main definition that defines complexity for this computation model. -/
def Prog.ComputesBoolFunInTimeAndSpace
  (p : Prog) (f : List Bool → List Bool) (t : ℕ → ℕ) (s : ℕ → ℕ) : Prop :=
  ∀ x, ∃ t' ≤ t x.length, ∃ s' ≤ s x.length,
  Prog.ComputesInTimeAndSpace p (DataEncode.encode x) (DataEncode.encode (f x)) t' s'

/-- The function `f` is computable in time `t` in the RTM model, up to constant factors -/
def ComputableInOTime (f : List Bool → List Bool) (t : ℕ → ℕ) : Prop :=
  ∃ p a s, Prog.ComputesBoolFunInTimeAndSpace p f (fun n => a * (t n) + a) s

/-- The function `f` is computable in space `s` in the RTM model, up to constant factors -/
def ComputableInOSpace (f : List Bool → List Bool) (s : ℕ → ℕ) : Prop :=
  ∃ p a t, Prog.ComputesBoolFunInTimeAndSpace p f t (fun n => a * (s n) + a)

/-- The *in-place* (first-order) fragment of the functional language.

`InPlace p` holds when every `fn` in `p` occurs in an immediately-consumed position — as the
operator of an `app`, or as the (curried) branch of an `elim`/`while_`. Consequently no
closure ever escapes: every abstraction is created and used on the spot, so all values that
flow through the environment are first-order `Data`. This is exactly the fragment a
defunctionalising compiler targets, and it is closed under the operational semantics.

A Turing machine can directly implement this fragment without the need for closures:
One tape is used for each "node" in the syntax tree.
-/
inductive InPlace : Prog → Prop
  | var : InPlace (.var i)
  | empty : InPlace .empty
  | cons (hh : InPlace h) (ht : InPlace t) : InPlace (.cons h t)
  /-- `elim` over an in-place value, empty branch, and a curried two-argument function
      branch `fn (fn body)` binding `head` and `tail`. -/
  | elim (hv : InPlace v) (hemp : InPlace emp) (hbody : InPlace body) :
      InPlace (.elim v emp (.fn (.fn body)))
  | ifEq (hx : InPlace x) (hy : InPlace y) (hthen : InPlace then_) (helse : InPlace else_) :
      InPlace (.ifEq x y then_ else_)
  /-- `while_` whose body is a literal one-argument function `fn body` binding the
      accumulator. -/
  | while_ (hinit : InPlace init) (hbody : InPlace body) :
      InPlace (.while_ init (.fn body))
  /-- `app` whose operator is a literal one-argument function `fn body`: this is a `let`,
      binding the value of `arg` and running `body` on the spot. The abstraction is consumed
      immediately, so no closure escapes. Nested applications of this form give multi-argument
      `let`-chains; arbitrary arities follow by repeated use of this constructor. -/
  | app (hbody : InPlace body) (harg : InPlace arg) :
      InPlace (.app (.fn body) arg)


end RoseTreeMachine

end Complexity
