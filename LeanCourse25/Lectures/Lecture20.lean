import Mathlib.Tactic

open Function
set_option linter.unusedVariables false
noncomputable section







/- # Last time

Last time:

- well-founded recursion
- more inductive types and propositions
- we implemented propositional logic in Lean, with
  - syntax: the inductive type `Formula`
  - semantics: `IsTrue` gives a notion of truth for formulas
  - proofs: we defined a notion of proof trees

**Today**: the logic of Lean

-/




/-
## What goes on under the hood?

When you write a Lean *declaration* (theorem, lemma, def, inductive) the following steps happen.

[https://lean-lang.org/doc/reference/latest/static/figures/pipeline-overview.svg]
[I'll draw a similar diagram in class]
-/

/-
* You start with the source code (e.g. `1 + 1 = 2`)
-/
/-
* Then this is *parsed* to get a (concrete) syntax Tree.
  (think of a tree with nodes labeled with `=, +, 1, 1, 2`)
-/
#check Lean.Syntax
/-
* There is *macro expansion*, which maps Syntax to Syntax.
  (e.g. expand out notation)
  - This also tries to resolve names, e.g. `subset_def` -> `Set.subset_def`
  Sometimes this returns a list of options, e.g. `add_mem` could be
  `Ideal.add_mem` or `AddSubgroup.add_mem` if both namespaces are opened.
-/
/-
* The biggest step is *elaboration*
  - It generates a *metavariable* for each implicit argument and
    underscore in terms. A metavariable is a value to be determined,
    usually written `?m`
  - It finds these implicit arguments through:
    - unification, e.g. in `@id ?m Nat.zero` we can deduce
      that `?m` must be `Nat`. from the type of `id`.
    - type-class inference for arguments in `[...]`
    - tactic execution
  - It chooses candidates among overloaded notation or names.
  - It also inserts *coercions* when necessary.
  - It expands *pattern-matching* notation into applications of recursors
  - This process generates *InfoTree*-objects that store information
    about the term (e.g. mouse-over text, tactic states)
  - The end-result is an `Expr` (think: `Formula` from last class, but more complicated)
  The result of elaborating `1 + 1 = 2` is something like
  `@Eq ℕ (@HAdd.hAdd ℕ ℕ ℕ _ 1 1) 2` (with `1` and `2` also
  represented by a more complicated expressions)
-/
#print Lean.Expr
#check Lean.Elab.InfoTree
/-
With expressions, Lean does multiple things, depending on the declaration.

* Lean sends declarations to the *kernel*
  - It checks that the expressions are well-formed and have the correct type.
  - This is the only component of Lean that you have to trust.
  - There are also *external type-checkers* that can independently do this step.
  - These checkers can be relatively small (a few thousand lines of code).
-/

/-
* For definitions: Lean has a *compiler* that
  compiles definitions into executable code
  - this is the code that `#eval` runs
  - You can write `partial` and `unsafe` definitions to define more flexible functions
    - `partial` functions have a value that is opaque to the kernel
    - `unsafe` functions are not sent to the kernel at all.
      You cannot use `unsafe` functions in a safe function.
  - Multiple fancy programming techniques are used in the compiler
    that are out of the scope of this class
    (see https://lean-lang.org/doc/reference/latest/Run-Time-Code/#runtime)
-/


/- Here is a function that Lean will not accept without `partial`. -/
partial def f : ℕ → ℕ
| 0 => 1
| n => f (n + 1)

#check f
#eval f 0
-- #eval f 1 -- infinite loop

/- The kernel only "knows" that `f` has type `ℕ → ℕ`,
but nothing about its values. -/
example : f 3 = f 3 := rfl
-- unprovable, since `f` is opaque
example : f 0 = 1 := by sorry

def h (n : ℕ) : ℕ := f n + f n

/- An `unsafe` function is not sent to the kernel altogether,
and cannot be used in other definitions. -/
unsafe def g : ℕ → Empty
| n => g (n + 1)

-- def k (n : ℕ) : Empty := g n


/-
* Finally, expressions are used to print output by the *pretty printer*.
  - There are *delaborators* that turn an expression back into a syntax object
  - There are *unexpanders* that operate on syntax
  - Finally there is a *formatter* that formats the syntax.
-/

/-
Most of these steps are extensible by the user!
Exceptions: expressions and the kernel cannot be modified
-/


/-
## Expressions

So what are expressions?
-/
open Lean
#print Expr

def double : ℕ → ℕ :=
  λ n : ℕ ↦ Nat.add n n
/-
The core components of an expression are
* variables (`n`)
* constants (any declaration: def, theorem, lemma, axiom, inductive, ...) `Nat.add`, `ℕ`
* functions binders, also called *lambda abstraction*: `fun n : ℕ ↦ ...`
* applications: we have two applications in `(Nat.add n) n`

For types we additionally have:
* (dependent) function types, also called *Pi-types*: `ℕ → ℕ`
* universes: `Type ...`
-/

/- Dependent functions can be written in multiple ways. -/
#check (n : ℕ) → Fin n
#check Π (n : ℕ), Fin n
#check ∀ (n : ℕ), Fin n -- allowed but discouraged

variable (f : (n : ℕ) → Fin n) (n : ℕ)
#check f n
#check f 3
/- Forall-statements are just dependent "functions" into a proposition. -/
#check (n : ℕ) → n = n  -- allowed but discouraged
#check Π (n : ℕ), n = n -- allowed but discouraged
#check ∀ (n : ℕ), n = n

/- Non-dependent functions (and implications) are a special case of this. -/
#check ℕ → ℕ
#check (n : ℕ) → ℕ
#check Π (n : ℕ), ℕ
#check ∀ (n : ℕ), ℕ

/- An inhabitant of a dependent function type `(n : ℕ) → P n`
is a function with domain `ℕ`, and sends `n : ℕ` to a term
`f n` of type `P n` -/

open Fin
#check Fin
#check val
#check isLt

example {n : ℕ} (x : Fin n) : val x < n := isLt x

example (f : (n : ℕ) → Fin n) : ∀ n : ℕ, val (f n) < n :=
  fun n ↦ (f n).isLt

/-
In this example:
- `f n` has type `Fin n`
- `isLt (f n)` has type `val (f n) < n`
- `fun n ↦ isLt (f n)` has type `∀ n : ℕ, f n < n`

Generally:
* If `t` has type `(x : A) → B x`, and `s : A` then `t s : B s`.
* If `t` is a term that can contain variable `x : A` and has type `B x`
  then `fun x ↦ t` has type `(x : A) → B x`
-/

/-
If an expression contains `f x`, the kernel checks that
* `f` is a function, it has as type something like `(x : A) → B n`
* `x` has as type that is *definitionally equal* to `A`

Here is an example where we need to unfold the definition of `copyNat` to
see that the application `f y` makes sense.
-/
def copyNat := ℕ
example (f : ℕ → ℕ) (y : copyNat) : f y = f y := rfl

/-
## Definitional equality

Definitional equality `≡` is the equivalence relation generated by:
- renaming variables in an abstraction:
  `(fun x : A ↦ f x) ≡ (fun y : A ↦ f y)` (α-equivalence)
- reduction of function applications:
 e.g. `(fun x : A ↦ x + x) t ≡ t + t` (β-reduction)
- unfolding definitions: e.g. `copyNat ≡ ℕ`. (δ-reduction)
- reducing unnecessary function abstractions:
  `(fun x : A ↦ f x) ≡ f` (η-reduction)
- reducing recursors of inductive types applied to constructors:
  e.g. `Nat.rec s_zero s_succ 0 ≡ s_zero` (ι-reduction)
- Reducing let-expressions
  e.g. `(let a := 3; a + a) ≡ 3 + 3` (ζ-reduction)
- There is also η-reduction for structures:
  if `p : ℕ × ℕ` then `(p.1, p.2) ≡ p`
- Proof irrelevance: if `h1, h2 : P` and `P : Prop` then `h1 ≡ h2`.
- There is an analogue to ι-reduction for quotients:
  `Quotient.lift f hf ⟦x⟧ ≡ f x`.
- it is a *congruence* relation: it respects all basic operations.
  e.g. if `f ≡ f'` and `a ≡ a'` then `f a ≡ f' a'`

Note: everything marked as *reduction* can be viewed as a
directed rule: computing the right-hand side from the left-hand side.
-/

example : (fun x : ℕ ↦ x + x) = (fun y : ℕ ↦ y + y) := rfl
example : (fun x : ℕ ↦ x + x) 3 = 3 + 3 := rfl
example : copyNat = ℕ := rfl
example (f : ℕ → ℕ) : (fun x ↦ f x) = f := rfl
example {P : ℕ → Type*} (h_zero : P 0) (h_succ : ∀ n, P n → P (n + 1)) :
    Nat.rec (motive := P) h_zero h_succ 0 = h_zero := rfl
example : (let a := 3; a + a) = 3 + 3 := rfl
example (p : ℕ × ℕ) : (p.1, p.2) = p := rfl
example {P : Prop} (h1 h2 : P) : h1 = h2 := rfl
example {α β : Type} {r : Setoid α} (f : α → β)
  (hf : ∀ x y, r x y → f x = f y) (x : α) :
  Quotient.lift f hf ⟦x⟧ = f x := rfl


example : 1 + 1 = 2 := by
  calc
   1 + 1 = Nat.add (Nat.succ Nat.zero) (Nat.succ Nat.zero) := rfl
  _ = Nat.succ (Nat.add (Nat.succ Nat.zero) Nat.zero) := rfl
  _ = Nat.succ (Nat.succ Nat.zero) := rfl
  _ = 2 := rfl


/-
One rule of the type theory is that if `t : A` and `A ≡ A'` then `t : A'`

Conversely, it is a meta-theorem that Lean has unique typing:
if `t : A` and `t : A'` then `A ≡ A'`.
-/

/- Reduction can get complicated -/

/- The type `A → A → A → ⋯ → A → B` with `n` occurrences of `A`. -/
def nAry : ℕ → Type → Type → Type
| 0, A, B => B
| n + 1, A, B => A → nAry n A B
-- or using a recursor:
-- fun n A B ↦ Nat.rec B (fun k nAry_k ↦ A → nAry_k) n

variable (f : nAry 1 ℕ ℕ) in
#check (f 0 : ℕ)
/-
To check that `f 0` has type `ℕ`, note that `f` has type
```
nAry 1 ℕ ℕ
≡ (fun n A B ↦ Nat.rec B (fun k nAry_k ↦ A → nAry_k) n) 1 ℕ ℕ
≡ Nat.rec ℕ (fun k nAry_k ↦ ℕ → nAry_k) 1
≡ ℕ → Nat.rec ℕ (fun k nAry_k ↦ ℕ → nAry_k) 0
≡ ℕ → ℕ
```
where the steps are respectively
- δ-reduction
- 3 times β-reduction
- η-reduction (plus twice β-reduction)
- η-reduction
-/


#check ∀ (f : nAry 3 ℕ ℕ), f 1 2 3 = (0 : ℕ)
#check ∀ (f : nAry 5 ℕ ℕ), f 1 2 3 4 5 = (0 : ℕ)
#check ∀ (F : (n : ℕ) → nAry n ℕ ℕ), F 3 0 0 0 = (0 : ℕ)
#check ∀ (F : (n : ℕ) → nAry n ℕ ℕ), F 5 0 0 0 0 0 = (0 : ℕ)


/- ## Universes

Lean has a hierarchy of universes `Sort u`.
-/


universe u v

#check ℕ
#check Type
example : Prop = Sort 0 := rfl
example : Type = Sort 1 := rfl
example : Type u = Sort (u + 1) := rfl

/- Quiz: where do function types live? -/

variable (A : Type u) (B : Type v)
#check A → B

variable (A : Type u) (B : A → Type v)
#check (a : A) → B a

/- Prop is *impredicative*: you can quantify over a large universe
with a family of propositions and get a new proposition.
-/
variable (A : Type u) (B : A → Prop)
#check ∀ (a : A), B a

variable (A : Sort u) (B : A → Sort v)
#check (a : A) → B a

/-
`imax` is a funny function on universes defined by:
`imax u (v + 1) := max u (v + 1)`
`imax u 0 := 0`
-/

/- Many definitions and theorems are *universe polymorphic*:
there is a "copy" of this definition at each universe level.-/

def identity (A : Sort u) (x : A) : A := x

#check identity
#check identity.{0}
#check identity.{1}
#check identity.{u}
#check identity.{u+1}



/- ## Inductive types

We saw inductive types in the last few classes.

The precise rules are too complicated to explain in detail.
You can find the precise rules here:
https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/

However, it is a meta-theorem that all inductives types
can be constructed (up to equivalence) from the following 8:
Empty, Sigma, Sum, ULift, Nonempty, WType, Eq, Acc
-/

-- dependent pair types
#print Sigma
-- universe lifting
#print ULift

#check ULift.{5, 3}
/-
W-types are general recursive types.
`WType α β` has `|α|`-many constructors and
constructor `i : α` has arity `β i`
-/
#print WType

/- Example: the natural numbers have 2 constructors,
one which is nullary (has no recursive arguments) and
one which is unary (has one recursive argument)-/
example : ℕ ≃ WType (α := Bool) (Bool.rec Empty Unit) := sorry




/- ## Quotients

Lean's type theory implements a mechanism to take quotients.
It comes with 5 primitive constants/axioms,
and 1 rule for definitional equalities.
-/
#print Quot
#check Quotient
#print Quot.mk
#print Quot.lift
#print Quot.ind
#print Quot.sound




/- ## Axioms

Lean's logic has 3 axioms.
-/
#print propext
#print Classical.choice
#print Quot.sound

/- You can see which definitions depend on which axioms. -/

#print axioms Nat.add_comm
#print axioms Real

/- `sorry` also uses an axiom (which is inconsistent). -/
def unfinished : True := sorry
#print axioms unfinished
#print sorryAx


/- You can add your own axioms.
Of course, then Lean's logic might become inconsistent. -/

axiom assume_this : 1 = 3

theorem oops : False := by
  have : 1 = 3 := assume_this
  have : 1 ≠ 3 := by decide
  contradiction

#print axioms oops

/-
## Misc

There are a few things in the kernel that are nice to have,
but mathematically aren't necessary.
-/

/-
**let-expressions** can be used to abbreviate something
without creating a new declaration.
-/
#check (let a := 4 * 5; a + a)

/-
Lean has natural number and string **literals**
to support efficient computation.

Normally `1000 + 1000` this would take 1001
steps of ι-reduction to arrive at `2000`.
However, the kernel uses a (normal) bitwise representation,
so that it can do this more efficiently
-/
#reduce 1000 + 1000
#reduce 1000000000000 + 1000000000000


/-
Lean has **primitive projections**

For example, `Prod.fst` and `Prod.snd` are defined using
primitive projections.

Mathematically, they could have equivalently
been defined using `Prod.rec`.

Having primitive projections is necessary
to have η-reduction for structures.
-/
#print Prod.fst
#print Prod.snd
#print Prod.rec

/- We've now seen almost all of the constructors of `Expr`.

Exceptions:
- `mdata` is used to store annotations inside an expression.
  It is ignored by the kernel.
- `mvar` (metavariables) are not allowed to occur
  in expressions sent to the kernel.
-/
#print Expr




/-
## Consistency

Is the logic of Lean consistent?

Yes, relatively to some other logic.

**Meta-theorem**: Lean's logic has the same *proof-theoretic strength*
as ZFC + sup_{n ∈ ℕ} (there are n inaccessible cardinals).

Two theories have the same proof-theoretic stength if the consistency of
one implies the consistency of the other.

The inaccessible cardinals correspond to Lean's universes.
Even though there are infinitely many universes,
you can only use finitely many of them in one particular proof,
which explains the supremum.

See [https://github.com/digama0/lean-type-theory/releases]
-/
