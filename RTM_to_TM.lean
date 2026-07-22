/--

Sketch of how to simulate an RTM with a TM.

First we describe how to simulate the RTM with a multi-tape TM.

From each Prog, we can determine a number of tapes required:

def tape_count (p : Prog) : ℕ :=
  match p with
  | .var _ => 1
  | .letin val rest => 1 + tape_count val + tape_count rest
  | .empty => 1
  | .cons h t => 1 + tape_count h + tape_count t
  | .elim v em cs => 5 + tape_count v + tape_count em + tape_count cs
  | .eq a b => 1 + tape_count a + tape_count b
  | .fold body init list => 5 + tape_count body + tape_count init + tape_count list
  | .while_ init body => 5 + tape_count init + tape_count body

From these tape counts, we can allocate distinct tapes for each Prog. Each prog has a designated
output tape and potentially some helper tapes. We also maintain a mapping from
variable indices to tapes.

This is how we simulate. Whenever we write to a tape, we first clear it, because it might
still contain data from previous loop iterations.

var : copy from the tape of the variable to the output tape of the Prog. This should take linear time in the size of the copied data and also linear space in that.

letin : simulate 'val'. add a new variable to the environment and let it point at the output
  tape of 'val'. Then simulate 'rest'. Copy its output to the output tape.

empty: write '(', ')' to the output tape.

cons: simulate h and t. write '(' to the output tape, then copy the contents of the output tape
of h, then copy the contents of the output tape of t (but ignore the first symbol).

elim: simulate v. check if the output take is exactly "()". If yes, simulate em and copy its
output to the output tape of elim. Otherwise, use three auxiliary tapes: We nede to copy
the head and the tail of the output tape of v to two separate tapes. For that, we need to
analyze the parentheses-nesting structure. Prepare an auxiliary tape to count the current nesting
level in unary (you can put single '(' that do not match a closing one). skip the first '(' on
the output tape of v. Then do the following in a loop: copy the current symbol to the head auxiliary tape
and update the nesting level (add a '(' for '(', remove a '(' for ')'). If the nesting level reaches 0 (the tape head on the nesting level tape reads "empty"), we are at the end of the head, so we switch to copying to the tail auxiliary tape: put a `(` on hte tail auxiliary tape and copy over the rest of the 'v' autput tape. After this, we have the head and tail on separate tapes, so we can simulate cs with these tapes added to the variable mapping. After rest terminates, copy its output tape to the outpuut tape of elim.

eq : simulate a and b. We compare the tape contents by moving over them in parallel. If we find a mismatch, write (()), otherwise write () to the output tape.

fold: simulate init and list. We maintain an auxiliary tape for the accumulator, which we initialize with the output of init. We also maintain an auxiliary tape for the current element of the list. TODO

Then we can simulate each Prog on the TM by using the tapes to store the environment and intermediate results. The TM will have a fixed number of tapes equal to the maximum number of tapes needed for any Prog we want to simulate.

Finally, we can use the fact that multi-tape TMs can be simulated by single-tape TMs with only a polynomial slowdown, to conclude that we can simulate the RTM with a single-tape TM.

-/
inductive Prog where
  | var (id : Var)
  /-- `letin val rest`: evaluate `val`, append the result to `env`, then evaluate `rest`. -/
  | letin (val : Prog) (rest : Prog)
  | empty
  | cons (h t : Prog)
  /-- `elim v em cs`: if `v` evaluates to `empty`, run `em`; otherwise destructure into
      `head` and `tail` (both appended to `env`, in that order) and run `cs`. -/
  | elim (v : Prog) (em : Prog) (cs : Prog)
  | eq (a b : Prog)
  /-- `fold body init list`: `init` and `list` produce starting accumulator and the input
      list; `body` runs once per element with `env` extended by `[acc, x]`. -/
  | fold (body : Prog) (init list : Prog)
  /-- `while_ init body`: `init` produces the starting accumulator; `body` runs with
      `env` extended by the current accumulator. -/
  | while_ (init body : Prog)
deriving Repr

/-- Evaluates `p` on `env` and returns the result, the time and the space consumption. -/
def Prog.meteredEval (env : List Data) (p : Prog) : Part (Data × ℕ × ℕ) :=
  match p with
    -- TODO charge for copy?
  | .var id => .some (env[(show ℕ from id)]?.getD (Data.l []), 1, 1)
  | .letin val rest => do
    let (v, t, s) ← val.meteredEval env
    let (r, t', s') ← rest.meteredEval (env ++ [v])
    -- TODO charge for copy?
    return (r, 1 + t + t', max s s')
  | .empty => .some (Data.empty, 1, 1)
  | .cons h t => do
    let (head, h_t, h_s) ← h.meteredEval env
    let (tail, t_t, t_s) ← t.meteredEval env
    return (Data.l (head :: tail.asList), 1 + h_t + t_t, max h_s t_s)
  | .elim v em cs => do
    let (v', t, s) ← v.meteredEval env
    match v' with
    | Data.l [] =>
      let (r, t', s') ← em.meteredEval env
      return (r, 1 + t + t', max s s')
    | Data.l (head :: tail) =>
      let (r, t', s') ← cs.meteredEval (env ++ [head, Data.l tail])
      return (r, 1 + t + t', max s s')
  | .eq a b => do
    let (a, a_t, a_s) ← a.meteredEval env
    let (b, b_t, b_s) ← b.meteredEval env
    (if a == b then Data.l [ Data.l [] ] else Data.l [], 1 + a_t + b_t, 1 + max a_s b_s)
  | .fold body init list => do
    let (i, i_t, i_s) ← init.meteredEval env
    let (l, l_t, l_s) ← list.meteredEval env
    l.asList.foldlM
      (fun (acc, t, s) el => do
        let (acc', b_t, b_s) ← body.meteredEval (env ++ [acc, el])
        return (acc', 1 + t + b_t, max s b_s))
      (i, 1 + i_t + l_t, max i_s l_s)
  | .while_ init body => do
    let (i, i_t, i_s) ← init.meteredEval env
    -- Real while loop: check the halt condition on the current accumulator first.
    -- If `acc.asList.headD = []` (empty head), halt and return `acc`.
    -- Otherwise run `body` on the accumulator and loop with its result.
    let F : ((Data × ℕ × ℕ) → Part (Data × ℕ × ℕ)) →
            (Data × ℕ × ℕ) → Part (Data × ℕ × ℕ) :=
      fun rec d_ts =>
        let (acc, t, s) := d_ts
        if acc.asList.headD (Data.l []) = Data.l [] then
          .some (acc, t, s)
        else
          (body.meteredEval (env ++ [acc])).bind fun (r, b_t, b_s) =>
            rec (r, t + 1 + b_t, max s b_s)
    Part.fix F (i, 1 + i_t, max 1 i_s)
  termination_by (sizeOf p, 0)
