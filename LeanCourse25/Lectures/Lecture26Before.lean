import Mathlib.Tactic

open Lean Meta Elab Parser Tactic PrettyPrinter
set_option linter.unusedVariables false







/-
# Last time

Continuation of differential geometry.
- The tangent space of a point `x` in a manifold `M` is the vector space of
  directions you can take from `x`.
- The tangent bundle is a new manifold that consists of pairs `⟨x, v⟩`
  where `x` is in `M` and `v` is in the tangent space of `x`.
- Smooth vector bundles generalize the tangent bundle:
  it is a manifold `Z` with a projection `π : Z → M`, that
  * admits local trivializations: every `x : M` has an open neighborhood `U`
    such that π⁻¹(U) is homeomorph to `M × F` for some vector space `F`
  * coordinate changes between these trivializations are smooth
- Important maps: smooth sections, diffeomorphisms, immersions, embeddings.

# Today: metaprogramming I

Recall:
* we learned how to declare notation
* Lean *elaborates* **syntax** (the concrete syntax, similar to what you write)
  into **expressions** (the resulting expression, containing all implicit arguments,
  represented as a tree).

Review lectures 10 and 20 if you need a refresher.
-/

#check Syntax
#check Expr
notation "𝔽₂" => ZMod 2



/-
`notation` does three things:
- it makes the syntax you're declaring valid syntax for terms
- it adds a *macro rule* which states how to expand the syntax
- it adds an *unexpander* that unexpands the syntax, used for pretty-printing.
-/
section
local notation "∑ " x " in " l ", " f => List.sum (List.map (fun x => f) l)

#eval ∑ x in [1,2,3], x ^ 3
#check ∑ y in [1,2,3], y ^ 3
end

/-
We can also declare the three parts separately ourselves.
This is useful for e.g. tactic writing, since `notation` only works for terms.
-/
section

/-
We declare the syntax.
Every syntax has a *syntax category*. Examples include:
`ident` (identifiers or names), `term`, `tactic`, `command`.
-/
local syntax "∑ " ident " in " term ", " term : term



/-
A *macro rule* tells Lean how to expand syntax to other (more basic) syntax.
`(...) is called *syntax quotation*; it represents a syntax object
The `$x` on both sides are called *antiquotations*:
they insert a piece of syntax inside a syntax quotation.
-/
local macro_rules | `(∑ $x in $l, $f) => `(List.sum (List.map (fun $x => $f) $l))


/-
An *unexpander* prints a term using this syntax.
It is cumbersome to write manually.
-/
@[local app_unexpander List.sum]
def unexpListMap : Unexpander
  | `(List.sum $a) =>
    match a with
    | `(List.map $f $l) =>
      match f with
      | `(fun $x:ident ↦ $f) => `(∑ $x : $l, $f)
      | _ => throw ()
    | _ => throw ()
  | _ => throw ()

#eval ∑ x in [1,2,3], x ^ 3
#check ∑ y in [1,2,3], y ^ 3


end

section
/-
A *macro* combines the `syntax` and `macro_rules` into a single command
-/
local macro "∑ " x:ident " in " l:term ", " f:term : term =>
  `(List.sum (List.map (fun $x => $f) $l))

#eval ∑ x in [1,2,3], x ^ 3
#check ∑ y in [1,2,3], y ^ 3

end



/- You can also declare macros for tactics or commands.
You have to use `(tactic| ... ) to write quotation for tactics. -/

macro "split" : tactic => `(tactic| constructor)
macro "quit" : tactic => `(tactic| all_goals sorry)

example : 2 + 2 = 5 ∧ 5 < 6 := by
  split
  quit

/- We can declare multiple macro-rules.
In that case, it will try the *last* declared macro first. -/

syntax "easy" : tactic

-- example : True := by easy


/- `focus (t; done)` runs tactic `t` on the first goal.
It only succeeds if it manages to prove the goal. -/
macro_rules | `(tactic|easy) => `(tactic|constructor <;> easy)
macro_rules | `(tactic|easy) => `(tactic|focus (simp; done))
macro_rules | `(tactic|easy) => `(tactic|focus (ring_nf; done))
macro_rules | `(tactic|easy) => `(tactic|assumption)

example (n m : ℕ) (h : n ≠ m) : n ≠ m ∧ n + m = m + n ∧ 0 ≤ n := by
  easy












/-
To understand better what is going on, I will say a bit
about *monadic programming*, a paradigm in *functional programming*.

For a more detailed introduction to functional programming in Lean,
see [Functional programming in Lean](https://lean-lang.org/functional_programming_in_lean/)

In imperative languages (e.g. C++, Python, Java) a program is a series of instructions
that are executed in sequence.
Variables are "mutable": they can be changed in the progam, and
the program can have
These steps have all sorts of "side effects", like
creating a file or printing to the console.

Example: (pseudocode)
```
def myFun(x):
  print(x)
  x := x + x
  print(x)
  for (i = 1; i <= 5; i += 1):
    x += i
    print(x)
  write_to_file("out.txt", x)
```

In functional languages (e.g. Haskell, Lean) a program is like a
mathematical definition.
Variables cannot be reassigned. The output depends only on the input.
If two functions output the same value, replacing one with the other
will not cause your program to compute a different result.
-/

/- Variables in Lean are immutable. Once declared, `squares` cannot be modified. -/
def sumOfSquares (l : List ℕ) : ℕ :=
  let squares := l.map (· ^ 2)
  squares.sum

#eval sumOfSquares [1, 4, 5]





/- Monads are a way to do imperative-style programming in a functional language.
Any side-effects a function can perform is specified by the return type of the function,
hidden from the programmer.

`IO` (input-output) is the monad that gives us access to the console and file system.
The return type `IO ℕ` indicates that the function returns a natural number
and has IO side-effects.

The `do` notation lets us write programs more easily.-/

-- this function computes `(n + 1) ^ 2` and prints intermediate steps.
def addOneSquare (n : ℕ) : IO ℕ := do
  IO.println s!"input is {n}"
  let m := n + 1
  IO.println s!"input plus one is {m}"
  let out := m ^ 2
  IO.println s!"output is {out}"
  return out

#eval addOneSquare 7

-- this function computes `(n + 1) ^ 2 / 2` and prints intermediate steps.
def addOneSquareDivTwo (n : ℕ) : IO ℕ := do
  /- Notice the difference between `let k ← ...` and `let l := ...`
  `←` is used to run another monadic function
  (e.g. a function that has as type `IO ...`)
  `:=` is used to compute a value without using a monadic function. -/
  let k ← addOneSquare n
  let l := k / 2
  IO.println s!"dividing the previous result by 2 gives {l}"
  return l

#eval addOneSquareDivTwo 7





/- Now we define a monad ourselves, using the "state monad".

The state monad carries some state with it, that each function can access and modify.
One should think of `f : StateM State α`
as a function with no inputs, that produces a value of type `α` and depends on
and affects some ambient value of type `State`.

If you expand the definitions, you can see that it is *implemented*
as `State → α × State`: it takes the current state,
and computes the output and the new state.

We will use this to define the sieve of Eratothenes to compute all primes
up to a certain number.
-/


namespace PrimeSieve

/- We keep two pieces of data in the state:
- for every number, is it prime? (returns `true` if we don't know yet)
- the list of primes we found so far.
-/
structure State where
  isPrime : Array Bool
  primes : List ℕ
deriving Repr

abbrev SieveMonad (α : Type) : Type := StateM State α

example {α : Type} : SieveMonad α = (State → α × State) := rfl

/-
The state monad comes with three functions that we'll use:
get the state, set the state and modify the state.
-/
#check (get : SieveMonad State)
#check (set : State → SieveMonad Unit)
#check (modify : (f : State → State) → SieveMonad Unit)


/- The next two functions update the state. -/
def addPrime (p : ℕ) : SieveMonad Unit := do
  modify fun state => { state with primes := p :: state.primes }

def setNotPrime (n : ℕ) : SieveMonad Unit := do
  modify fun state => { state with isPrime := state.isPrime.set! n false}

/- We check whether `n` is prime, according to the current state. -/
def isPrime (n : ℕ) : SieveMonad Bool := do
  let state ← get
  return state.isPrime[n]!

/- We now define the sieve of Eratothenes. -/
def eratosthenes (n : ℕ) : SieveMonad (List ℕ) := do
  -- we first initialize the state
  set (⟨Array.replicate n true, []⟩ : State)
  for p in 2...n do
    -- we can use `← A` to execute `A` and compute its result.
    if ← isPrime p then
      addPrime p
      -- for (int k = 2*p; k < n; k += p)
      for k in List.range' (2 * p) ((n - 1) / p - 1) (step := p) do
        setNotPrime k
  return (← get).primes.reverse

/- `run'` allows us so run a function in the state monad,
by specifying the initial state. -/
def primesLt (n : ℕ) : List ℕ :=
  (eratosthenes n).run' ⟨#[], []⟩

#eval primesLt 100

end PrimeSieve


/- If you want to use `do` notation to define a pure function,
you can use the `Id` monad. In that case, prepend the `do` by `Id.run`. -/
def mySum (l : List ℕ) : ℕ := Id.run do
  let mut s := 0
  for n in l do
    s := s + n
  return s
