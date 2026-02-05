import Mathlib

/-! # Review: what did we see in class

Let us collect what we saw about Lean.

**How it works**
- rich type system with e.g. dependent types
- everything has a type: statements, but also types themselves
- universes: each type has a universe level (indexed by ℕ); `Type u` has type `Type (u+1)`

- two kinds of types: `Prop` vs `Type`
  - `Prop` are mathematical statements (can be true, false or unknown)
  - terms of a given `Prop` are proofs of this proposition
  - proof irrelevance: any two proofs of `A` are equal
  - `Type u` are "data", e.g. definitions
    objects (like ℕ), constructions using them (e.g., a map ℕ → ℕ)...

- you prove `A : Prop` by constructing a term of type `A`
- Lean can check proofs!

- can create types through `def`initions, `inductive`s, `structure`s,
function types, pi types/dependent types, subtypes, qoutient types, ...

- a `def` creates a new type
- `inductive` creates a new type with (potentially) several constructors,
and corresponding induction and recursion principles
example: `ℕ` is an inductive type with two constructors (`zero` and `succ`)
`False` is an inductive type with no constructor

*Question.* Is every type an inductive type? Are quotient types an inductive type?
*Answer.* "Almost" and no.
Every type in Lean is either an inductive type, or defined in terms of
universes (like the type `Type 2`), functions and quotient types.

- a `structure` can be used to "bundle" data and properties together into a new object
is a inductive type with one constructor

- a `class` is a structure with the `class` attribute, participates in typeclass search
  a big database of properties and implications between them
  e.g. `Group`, `TopologicalSpace`, `IsManifold`
- typeclass inference uses `instance`s to infer terms of a given typeclass
- intuition: if there are multiple ways to define a given structure on a type, do not make a `class`


proving propositions
- exhibit a term of the right type
- one proof strategy: specify a full proof term
- apply theorems to existing hypotheses, to successively build a proof term
- tactics are programs to (help you) build a proof term
  usually apply one step of mathematical reasoning, e.g. "simplify this expression using lemmas you
  know" or "try proving this just from the axioms of a ring"
- you can write your own tactics!

**metaprogramming**
- Lean is a (functional) programming language
- `do` notations allows programming like in imperative programming
- Lean is extensible: (almost) every aspect of it can be extended or modified
- examples: create custom notation, unexpanders and delaborators,
  new operators/different precedence etc.,
  macros, write tactics, customise elaboration,
  linters, ...

-/

-- Example of dependent types: A is a type parametrised by another type (ℕ)
def A (n : ℕ) := Fin (n + 1)
#check A

-- B is a *product type*: the type A i depends on the argument.
def B : (i : ℕ) → Type := fun i ↦ A i
#check (A 2) → (B 3)
-- Mathematical examples: tangent space of a manifold,
-- fibers of a vector bundles; stalks of sheaves

-- Attention: this is not a dependent type, but a dependent function.
def B' : (i : ℕ) → A i := fun i ↦ ⟨0, by cutsat⟩
-- Therefore, this does not typecheck: `B' 3` has type `A i`, and is not a type itself.
#check (A 2) → (B' 3)

-- An example of classes and instances.
-- Let's define a new class `Foo`, depending on a type `α`
class Foo (α : Type*) where
  a : ℕ

-- For *any* type α, we can provide an instance of Foo.
instance {α : Type*} : Foo α where
  a := 37

-- Suppose we can prove some statement, assuming such a `Foo` instance.
lemma mylemma (α : Type*) [Foo α] : 2 = 5 := by sorry

example {α : Type*} : 2 = 5 := by
  -- The `Foo` instance for `α` is inferred by Lean!
  exact mylemma α

#check False

/-
Useful Lean tactics

**basic logic**
- `constructor` applies a constructor of a type
  (creating subgoals for each parameter)
  e.g. split `And` goals in two subgoals,
  split `↔` goals into both direction
- `left` and `right` allow proving a conjunction by reducing to the left resp. right term
  (`exact Or.inl` resp. `exact Or.inr`)
- `obtain` or `rcases` allow splitting conjuctions in hypotheses
- `intro`
- `rw`
- `assumption`
- `rfl`
- `tauto` proves goals in propositional logic
- `contrapose` does a proof by contradiction;
  `contrapose!` also calls `push_neg` on the resulting goal
- `by_contra` does a proof by contraposition
- `contradiction` observes that the hypotheses are contradictory
  (in an obvious-to-Lean way)

- `apply` applies a given lemma
  given a goal of type `t` and a term of type `a → b → t`, it creates new subgoals for `a` and `b`
- `refine` is like apply, but
  requires writing `?_` for all missing subgoals;
  `apply` creates these subgoals (using unification)
- `exact` provides a proof term exactly matching your goal

- `simp` simplifies the goal by rewriting with a collection of known lemmas
  `simp at h` at an assumption simplifies `h` instead
- `dsimp` is like simp, but only applies definitional equalities

- `let` and `set` can be used to define new data
  `set` is like let, but creates a new theorem relating the new name and its definition
- `have` can be used for intermediate statements
  use `have` for propositions and `let` for data
- `suffices`
- `split_ifs` split a goal of (possibly nested) if statements into subgoals for the different cases;
eliminates impossible cases automatically
  `split` also works for `match` expressions

- `induction` applies an induction principle
- `omega`/`cutsat`/`lia` proves goals in integer arithmetic
- `fun_prop` proves goals like "the composition of continuous goals is continuous"
- `norm_num`
- `positivity`
- `gcongr`
- `grw` allows rewriting by inequalities
- `order`


-/
#check And

-- In an `iff` statement, `simp` will apply the lemma left to right.
-- There are a somewhat stupid example, and an actual example from mathlib.
@[simp] lemma bar : 4 = 4 ↔ True := sorry
#check continuousOn_univ

-- This would not be a good simp lemma, as the right hand side `2 = 2` can be simplified further
-- (to `True`).
@[simp] lemma baz : 4 = 4 ↔ 2 = 2 := sorry
