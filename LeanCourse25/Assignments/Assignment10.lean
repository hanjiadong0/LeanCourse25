import Mathlib.Tactic
import Mathlib.Data.W.Basic

open Function Set
noncomputable section

/-! # Exercises to practice -/

section

/-
**Exercise 1**
* Finish the exercises from Lecture 19
* Prove the following exercises, by copying them at the bottom of the Lecture 19 file.

example : Provable (~(A || B) ⇔ ~A && ~B) := by
  sorry
  done

example {C : Formula} : Provable (A || (B && C) ⇔ (A || B) && (A || C)) := by
  sorry
  done

example {C : Formula} : Provable (A && (B || C) ⇔ (A && B) || (A && C)) := by
  sorry
  done

-/


/-
**Exercise 2**
Define the inductive type of labeled binary trees.
A labeled binary tree is either
- a leaf, labeled with an element from `α : Type*`
- a node, labeled with an element from `β : Type*`,
  which has two children that are again labeled binary trees (labeled in the same way)

Define two operations on your inductive type:
- the `flip` operator that swaps the two children of *every* node in the tree
- a replacement operation that takes as argument a function from `α` to labeled binary trees,
  and it replaces all leaves labeled with `x` by the tree `f x` (for all `x`).

Now state and proof three lemmas:
- show that applying `flip` twice gives the original tree back.
- show that if you apply the replacement operation to a tree and then flip it,
  that is equal to flipping first and applying a (slightly different) replacement operation.
- show that if you apply the replacement operation twice (with two different functions),
  then you can also apply the replacement operation once (with a more complicated function).
-/











/-
**Exercise 3**
W-types are general recursive types.
`WType α β` has `|α|`-many constructors and
constructor `i : α` has arity `β i`
-/
#print WType

/- The natural numbers have 2 constructors,
`zero` is nullary (has no recursive arguments) and
`succ` is unary (has one recursive argument).

Prove this equivalence.
Hint: define the functions back-and-forth as separate definitions. -/
example : ℕ ≃ WType (α := Bool) (Bool.rec Empty Unit) := by
  sorry
  done


end


/-! # Exercises to hand in

**There are no exercises to hand-in this week. Enjoy the holidays!**

In January, there will be few exercises to be handed in.
Make sure to work on Project 2 instead.

You can work on Project 2 either:
* by creating Lean files in the `Projects` folder of the course repository.
  You can commit to your work to a fork (see `Projects/Git.md` for instructions)
* in your own new repository.
  You can create a new repository by using the extension symbol in VSCode:
  `∀ > New Project... > Create Project using Mathlib` and choosing a directory.

In both cases, once you have pushed something to GitHub, add the URL of your repository to the
[Sciebo table](https://uni-bonn.sciebo.de/s/tBzqggEFajsgwC6).
-/
