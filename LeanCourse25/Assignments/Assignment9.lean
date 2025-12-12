import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.RingTheory.Real.Irrational
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.JacobianOneDim

open BigOperators Function Set Real Topology Filter
open ENNReal MeasureTheory Interval intervalIntegral
set_option linter.unusedVariables false
noncomputable section

/-! # Exercises to practice -/

section

/- There are special cases of the change of variables theorems for affine transformations
(but you can also use the change of variable theorem from the lecture) -/
example (a b : ℝ) :
    ∫ x in a..b, sin (x / 2 + 3) =
    2 * cos (a / 2 + 3) - 2 * cos (b / 2  + 3) := by
  sorry
  done

/- Use the change of variables theorem for this exercise. -/
example (f : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    ∫ x in s, exp x * f (exp x) = ∫ y in exp '' s, f y := by
  sorry
  done

example (x : ℝ) : ∫ t in 0..x, t * exp t = (x - 1) * exp x + 1 := by
  sorry
  done

example (a b : ℝ) : ∫ x in a..b, 2 * x * exp (x ^ 2) =
    exp (b ^ 2) - exp (a ^ 2) := by
  sorry
  done


/- This is the last exercise from the lecture. -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ x in a..b, 1 / x + 1 / x ^ 2 =
  log b + 1 / a - log a - 1 / b := by
  have : 0 ∉ [[a, b]] := by sorry
  sorry
  done


/- Define tetration `n ↑↑ k = n^n^n^...^n` (`k` copies of `n`) on the natural numbers
recursively using `Nat.rec`. It is defined to be `1` when `k = 0`. -/

def tetration : sorry :=
  sorry


-- Uncomment these to test whether your function is (probably) correct.
-- example : tetration 2 4 = 65536 := rfl
-- example : tetration 3 3 = 7625597484987 := rfl
-- example : tetration 5 1 = 5 := rfl
-- example : tetration 0 5 = 0 := rfl
-- example : tetration 5 0 = 1 := rfl
-- example : tetration 0 0 = 1 := rfl

/- In class we mentioned that if Disjunction could eliminate to
types, this would lead to a contradiction. Proof this.
Recall: `rfl` can prove that any two proofs of the same proposition are equal. -/
inductive Disjunction (P Q : Prop) : Prop where
  | left  : P → Disjunction P Q
  | right : Q → Disjunction P Q

open Disjunction
example
    (rec : ∀ (P Q : Prop) (motive : Disjunction P Q → Type)
      (h_left : ∀ hp : P, motive (left hp)) (h_right : ∀ hq : Q, motive (right hq))
      (h : Disjunction P Q), motive h)
    (comp_left : ∀ P Q motive h_left h_right (hp : P),
      rec P Q motive h_left h_right (left hp) = h_left hp)
    (comp_right : ∀ P Q motive h_left h_right (hq : Q),
      rec P Q motive h_left h_right (right hq) = h_right hq) : False := by
  sorry
  done

end


/-! # Exercises to hand in -/

/-
There are just two exercises to hand in.
Also work on your project.
-/

/- Prove the following using the change of variables theorem. -/
lemma change_of_variables_exercise (f : ℝ → ℝ) :
    ∫ x in 0..π, sin x * f (cos x) = ∫ y in -1..1, f y := by
  sorry
  done


/-
In class we saw a definition of the Ackermann function.
Show that you can define this function just using `Nat.rec`
(without using pattern-matching notation), and show that it is equal
to the function defined by pattern matching.
When writing `Nat.rec`, give the `motive` explicitly using `Nat.rec (motive := ...)` -/

/- The Ackermann function, defined using pattern matching notation. -/
def A : ℕ → ℕ → ℕ
| 0,     n     => n + 1
| m + 1, 0     => A m 1
| m + 1, n + 1 => A m (A (m + 1) n)

def myA : ℕ → ℕ → ℕ :=
  sorry

example : A = myA := by
  sorry
  done
