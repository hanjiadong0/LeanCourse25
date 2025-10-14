import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.RingTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real BigOperators
open scoped Nat





/-
# Practical remarks

* Register on both eCampus for the course
* Link to the course repository:
  https://github.com/fpvandoorn/LeanCourse25
* Follow the instruction on that page
  to install Lean and download the repository.
* Do this at home, and ask for help during
  the tutorial on Monday if you get stuck.
* Link to Mathematics in Lean for background reading:
  https://leanprover-community.github.io/mathematics_in_lean/
* You can use the `∀` symbol at the top middle (or right)
  of the screen to execute some Lean commands.
-/













/-
# Example

A sequence `u` of numbers converges to a number `l` if
`∀ ε > 0, ∃ N, ∀ n ≥ N, |u_n - l| < ε`
and a function `f : ℝ → ℝ` is continuous at `x₀` if
`∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ ⇒ |f(x) - f(x₀)| < ε`

Fact: if `f` is continuous at `x₀` and `u` converges to `x₀` then
`f ∘ u : n ↦ f(u_n)` converges to `f(x₀)`.
-/


/-- The sequence `u` of real numbers converges to `l`. -/
def SequenceHasLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |u n - l| < ε

/-- The function`f : ℝ → ℝ` is continuous at `x₀`.-/
def ContinuousAtPoint (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hu : SequenceHasLimit u x₀) (hf : ContinuousAtPoint f x₀) :
    SequenceHasLimit (f ∘ u) (f x₀) := by
  sorry












/-!
# How does Lean help you?

* Checks that you have correctly written all steps of the proof
* Displays tactic state
  "the current game board of a mathematical proof"
* Helps organize a proof

-/









/- Lean is a calculator and programming language -/
#eval 2 + 3

#eval 2 ^ 3 + 4 * 5 - 6







-- compute the sum `0 ^ 2 + 1 ^ 2 + ⋯ + 100 ^ 2`
#eval do
  let mut sum := 0
  -- `List.range 101 = [0, 1, ..., 100]`
  for j in List.range 101 do
    sum := sum + j ^ 2
  return sum


-- compute the sum `0 + 1 + ⋯ + 100` again
-- `Finset.range 101 = {0, 1, ..., 100}`
#eval ∑ j ∈ Finset.range 101, j ^ 2








/- That is not what this course is about.
We want to write proofs.

How does Lean check these proofs?

Partial answer: By giving a type to every mathematical object.

The `#check` command asks Lean to display the type of an object.
Note the colon that means "has type" or "having type".
-/

#check 1

#check fun x : ℝ ↦ x^2
#check fun n : ℤ ↦ n^2





/- We can write our own definitions.
Here we define the sequence consisting
of the square roots of natural numbers

Definitions involving `ℝ` are not *computable*. -/
noncomputable def u : ℕ → ℝ := fun n ↦ √n





/-
The most basic protection against error is type checking: mathematical objects
must be combined according to their type.

`u` has type `ℕ → ℝ`, hence it expects natural numbers
as inputs, and produces real numbers as outputs.

Hence `u 1` is ok and has type `ℝ`.
-/

#check u 1
#check u (1 + 2)
#check (u 1) + 2
#check u (1 + 2)



/-
But `u π` is not ok, we say it doesn't type-check.
-/

-- #check u π
-- #check u u






/- The type `Prop` contains all statements

Unfortunate clash in terminology:
* In math: "Proposition" means
    useful proven statement (less important than a theorem)
* In logic: "Proposition" means
    any statement that can be either true or false.
-/


#check 2 + 2 = 4
#check 3 < π




#check 2 + 2 = 5







def Statement1 : Prop :=
  ∃ p, Prime p ∧ Prime (p + 2) ∧ Prime (p + 4)

def Statement2 : Prop :=
  ∀ n : ℕ, ∃ p ≥ n, Prime p ∧ Prime (p + 2) ∧ Prime (p + 4)

def Statement3 : Prop :=
  ∀ n : ℕ, ∃ p ≥ n, Prime p ∧ Prime (p + 2)




/- Nat.Prime is a predicate on natural numbers, so it has type `ℕ → Prop`. -/

#check Nat.Prime



/- What is the type of the factorial function? -/
-- #check (Nat.factorial)
-- #check fun n ↦ n !



/- What is the type of the predicate
stating that a natural number is at least 2? -/
-- #check (Nat.AtLeastTwo)



/- What is the type of addition on the natural numbers? -/
-- #check fun n m : ℕ ↦ n + m



/- What is the type of `≤` on the integers? -/
-- #check fun n m : ℤ ↦ n ≤ m






/- Next time: if we have a statement `A : Prop`,
we can try to prove `A` using *tactics*. -/

example : 2 + 2 = 4 := by rfl

example : 2 + 2 ≠ 5 := by simp
