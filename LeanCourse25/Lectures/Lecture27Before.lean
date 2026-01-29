import Mathlib.Tactic

open Lean Meta Elab Parser Tactic PrettyPrinter
set_option linter.unusedVariables false







/-
# Practical remark

- I will post a mock exam later today.

# Last time: metaprogramming I

- `macro` (and `macro_rules`) is a way to define simple tactics
  in terms of existing tactics.
- You can use quotation `(tactic| ...) to define an object of type `Syntax`
- Inside a quotation you can insert pieces of syntax using `$t` (antiquotation)

- Monads are a way to allow programs to have particular side effect
  when running.
- `do` notation is convenient to write monadic functions.

# Today: metaprogramming II

- we write some simple tactics.
-/


syntax "single_rw_and_simp" term : tactic

macro_rules | `(tactic|single_rw_and_simp $t) => `(tactic| rw [$t:term]; simp)

example {n m : ℕ} (h : n = m) : n + 3 = 0 + m + 3 := by
  single_rw_and_simp h


/-
If you are confused by the difference between `(0 + 0) and 0 + 0,
consider the following.

Below, we define `NatTerm`, a data-type of (some) natural number terms
(with a single variable).
We can evaluate these terms to actual natural numbers
(if we give some value for the variable)
-/

inductive NatTerm where
  | zero : NatTerm
  | var : NatTerm
  | succ : NatTerm → NatTerm
  | add : NatTerm → NatTerm → NatTerm
  | mul : NatTerm → NatTerm → NatTerm

@[simp]
def NatTerm.eval (n : ℕ) : NatTerm → ℕ
  | zero    => 0
  | var     => n
  | succ e  => e.eval n + 1
  | add e f => e.eval n + f.eval n
  | mul e f => e.eval n * f.eval n

variable (n : ℕ)
open NatTerm
#simp (zero.succ.add var).eval n
#simp (zero.succ.succ.mul var).eval n
#simp (var.succ.succ.mul (var.add var)).eval n

#simp only [NatTerm.eval] (zero.add zero).eval n

/-
Note the difference between `zero.add zero` and `0 + 0`.
The former is an element of `NatTerm`, and it is not equal to `zero`.
In contract `0 + 0 = 0` as natural numbers.

The syntax object `(0 + 0) corresponds to an expression like `zero.add zero`.
(except that `Syntax` is more complicated)
-/


/-
`(...) is a syntax object in some monad we will discuss more below.
-/
#check (`(1 + 1) : CoreM (TSyntax `term))
#check (`(tactic|simp) : TacticM (TSyntax `tactic))



/- With macros we can write down some shortcuts combining existing tactics.
For more control, it is useful to use `elab`.

`elab` defines an *elaborator* for a piece of syntax.
A macro states that a piece of syntax should be treated as another piece of syntax,
an elaborator gives code to execute during elaboration.

The syntax is
`elab <syntax> : tactic => <code to execute>`
Let's see some examples. -/

elab "my_tac" : tactic => do
  logInfo "Hello"
  logInfo "world."

example : True := by
  my_tac
  trivial

/- We can throw errors using `throwError`. -/

elab "my_failure" : tactic => do
  logInfo "Hello"
  throwError "Error"

example : True := by
  my_failure


/- `t <|> t'` executes `t`, and only if `t` fails, we execute `t'` instead. -/

elab "try_hard" : tactic => do
  throwError "Oops" <|> logInfo "Ok"

example : True := by
  try_hard
  trivial



/- We can also get information from the context using `let x ← t`.
This executes `t` and stores the result in `x`. -/

elab "print_goal" : tactic => do
  let goal ← getMainGoal
  logInfo m!"Current goal: {goal}"

example : True := by
  print_goal
  trivial

example : ∀ p q : ℕ, p + q = q + p  := by
  print_goal
  exact add_comm


/- We can abbreviate this code by using `← t` anywhere to mean "the result of running `t`" -/

elab "print_info" : tactic => do
  logInfo m!"Current statement to prove: {← getMainTarget}"
  logInfo m!"This is file {← getFileName}"

example : ∀ p q : ℕ, p + q = q + p := by
  print_info
  exact add_comm


/-
Here we've been writing small programs in the *tactic monad* `TacticM`.
This has access to a lot of information, including
- the environment of all Lean declarations imported and in this file.
- functions to find the type of terms
- the current goal, including the "local constants" (hypotheses) and target
  (statement to prove)
- ...

Some of these we can change (e.g. the goal), others we can only read,
but not modify (e.g. the current file name).
-/




/- Now let's implement an actual tactic: the assumption tactic.
We go through each assumption and look whether the type of the assumption is
*definitionally equal* to the target. -/

elab "my_assumption" : tactic => do
  /- `target` is the statement we want to prove -/
  let target ← getMainTarget
  /- Loop through all hypotheses in the local context -/
  for ldecl in ← getLCtx do
    /- Check for *definitional equality* -/
    if ← isDefEq ldecl.type target then
      /- If you find a match, use that hypothesis to close the goal. -/
      closeMainGoal `my_assumption ldecl.toExpr
      logInfo m!"found hypothesis {ldecl.toExpr} with type: {indentExpr (← inferType ldecl.toExpr)}"
      /- `return` stops executing the rest of the function. -/
      return
  /- If none of the local declarations match, throw an error. -/
  throwTacticEx `my_assumption (← getMainGoal)
    m!"unable to find matching hypothesis of type {indentExpr target}"

example (n m : ℕ) (h1 : 0 ≤ m) (h2 : n = 0) (h3 : m ≤ 9) : n = 0 := by
  my_assumption

example (p q : ℕ) (h : q + p = p + q) : p + q = q + p := by
  my_assumption


/- We check for definitional equality, so our tactic can unfold definitions. -/

def double (x : ℕ) : ℕ := x + x

example (n : ℕ) (h1 : double n = 12) : n + n = 12 := by
  my_assumption





/- There is still one problem with our code:
Every tactic updates the goal that we're working on.
Tactics are themselves responsible for updating that they're working
in the context of the current goal.
We can do this using `withMainContext`, which we need to add. -/

example : ∀ (n m : ℕ) (h1 : 0 ≤ m) (h2 : n = 0) (h3 : m ≤ 9), n = 0 := by
  intros
  my_assumption








/- As a second example, we want to write a tactic that creates a new hypothesis
`a₁ + a₂ = b₁ + b₂` from the assumptions `a₁ = b₁` and `a₂ = b₂`. -/

example (a b c d : ℕ) (h : a = b) (h' : c = d) : a + c = b + d := by
  have H := congrArg₂ HAdd.hAdd h h'
  exact H

elab "add_eq" eq₁:ident eq₂:ident " with " new:ident : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let newTerm  ← `(congrArg₂ HAdd.hAdd $eq₁ $eq₂)
    let prf ← elabTerm newTerm none
    let typ ← inferType prf
    let hyp : Hypothesis := {userName := new.getId, type := typ, value := prf}
    let (newFVars, newGoal) ← goal.assertHypotheses #[hyp]
    replaceMainGoal [newGoal]

example (a b c d : ℕ) (h : a = b) (h' : c = d) : a + c = b + d := by
  add_eq h h' with H
  exact H




/- We can make the `with H` optional, by separately declaring the syntax and
elaboration rules for that syntax.
elab = syntax + elab_rules -/

syntax "add_eq'" ident ident ("with" ident)? : tactic

elab_rules : tactic
| `(tactic| add_eq' $eq₁:ident $eq₂:ident $[with $new]?) =>
  withMainContext do
    let goal ← getMainGoal
    let prfStx  ← `(congr (congrArg HAdd.hAdd $eq₁) $eq₂)
    let prf ← elabTerm prfStx none
    let typ ← inferType prf
    -- we use the name `new`, or make a name ourselves
    let newName := match new with
    | some ident => ident.getId
    | none => `newEq
    logInfo m!"Specified name: {new}\nUsing: {newName}" -- we print the variable `new`
    let hyp : Array Hypothesis := #[{userName := newName, type := typ, value := prf}]
    let (newFVars, newGoal) ← goal.assertHypotheses hyp
    replaceMainGoal [newGoal]

example (a b c d : ℕ) (h : a = b) (h' : c = d) : a + c = b + d  := by
  add_eq' h h'
  assumption








/- Here we write another tactics:
we multiply both sides of a hypothesis by a constant -/

example (a b c : ℤ) (hyp : a = b) : c * a = c * b := by
  replace hyp := congr_arg (fun x ↦ c * x) hyp
  exact hyp

elab "mul_left" x:term l:location : tactic =>
  withMainContext do
    match expandLocation l with
    | .targets #[hyp] false => do
      let hypTerm : Term := ⟨hyp⟩
      let prfStx ← `(congr_arg (fun y ↦ $x * y) $hypTerm)
      let prf ← elabTerm prfStx none
      let typ ← inferType prf
      let fvarId ← getFVarId hyp
      let (newFVars, newGoal) ← (← getMainGoal).assertHypotheses
        #[{userName := hyp.getId, type := typ, value := prf}]
      let newGoal ← newGoal.clear fvarId
      replaceMainGoal [newGoal]
    | _ => throwError "You can use this tactic only at a single hypothesis."


example (a b c : ℤ) (hyp : a = b) : c * a = c * b := by
  mul_left c at hyp
  exact hyp

/-
This just scratches the surface. If you want to learn more,
you can find more resources here:
[https://leanprover-community.github.io/learn.html#meta-programming-and-tactic-writing]
-/
