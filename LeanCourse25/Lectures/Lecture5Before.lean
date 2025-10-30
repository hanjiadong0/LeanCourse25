import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.Finite.Basic

open Real
noncomputable section
variable (a b c : ℝ)

/-
# Practical remarks

* Syllabus update:
  The projects do *not* count towards your final grade.
  The final grade is fully determined by the final exam.
  The projects need to be finished with a passing grade
  to be admitted to the final exam.
-/


/- # Last time

Last time we saw:

* Main tactics for **Classical logic**:
  - `by_contra h` start a proof by contradiction.
  - `by_cases h : p` to start a proof by cases on statement `p`.
  - `push_neg` to push negations inside quantifiers and connectives.

* `ext` proves that two functions are equal if their values are equal.

* There are many way to find useful lemmas. Notably:
  - `apply?`: find all lemmas that apply to the current goal;
  - `rw??`: shift-click on expressions to get suggestions for lemmas;
  - `#loogle <query>`: syntactic searches;
  - `#leansearch "<query>."`: natural language searches.

* Orders:
  - `linarith` proves (in)equalities using linear combinations of hypotheses.
  - `gcongr` applies monotonicity of functions
-/

example (x : ℝ) : (Real.sin x) ^ 2 ≤ 1 := by
  sorry
  done

example : Complex.exp (Complex.I * π) + 1 = 0 := by
  sorry
  done


example {a b c d : ℝ} (h₀ : 0 < b) (h₁ : b < a) (h₂ : c ≤ d) :
    1 / a + Real.exp c ≤ 1 / b + Real.exp d := by
  sorry
  done

/-
# Today: Orders (continued) and Sets
-/


/- Remark: for equalities, you should use `congr` instead of `gcongr` -/

example (h : a = b) : c - exp b = c - exp a := by
  sorry
  done




/- `grw` can be used to rewrite with inequalities. -/

example {a b c d : ℝ} (h₀ : 0 < b) (h₁ : b < a) (h₂ : c ≤ d) :
    1 / a + exp c ≤ exp d + 1 / b := by
  sorry
  done




/-
`grw` can also be used to rewrite with other relations.
In contrast: `rw` can *only* rewrite with `=` or `↔`.
-/

#check 8 ≡ 3 [ZMOD 5]

example {a b n : ℤ} (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  grw [h]



example {a b c d n : ℤ} (h : a ≡ b [ZMOD n]) (h' : c ≡ d [ZMOD n]) :
    a ^ 2 * c ≡ b ^ 2 * d [ZMOD n] := by
  sorry
  done



example {a b c : ℤ} (h₁ : a ∣ b) (h₂ : b ∣ a ^ 2 * c) :
    a ∣ b ^ 2 * c := by
  sorry
  done



example (f g : ℝ → ℝ) (h : ∀ x : ℝ, f x ≤ g x)
    (h₂ : g a + g b ≤ 5) : f a + f b ≤ 5 := by
  sorry
  done






/-
`order` is a simple tactic that can perform purely
order-theoretic reasoning (not involving monotone operations).
-/

example {a b c d e : ℝ} (h₀ : a = b) (h₁ : b < c)
    (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  order
  done



/-
We've introduced a lot of tactics.
You can find an overview of common tactics
in the **Tactic cheatsheet** of this repository.
-/







/- # Sets

In set theory you can make sets with arbitrary elements.
In Lean, all sets have to be sets of elements from a specific type.

If `s : Set α` then `s` is a set with elements from `α`.
-/

#check Set ℕ
#check Set ℝ

variable {α β ι : Type*} (x : α) (s t u : Set α)

/- We can talk about membership and (strict) subsets. -/

#check x ∈ s       -- \in or \mem
#check x ∉ s       -- \notin
#check s ⊆ t       -- \sub
#check s ⊂ t       -- \ssub



/- We have the common set-theoretic operations.
Note: it is important that `s` and `t`
are sets of elements from the *same* type. -/

#check s ∩ t       -- \inter or \cap
#check s ∪ t       -- \union or \cup
#check s \ t       -- the normal symbol `\` on your keyboard,
                   -- (use a space afterwards to not use the unicode-replacement)

#check sᶜ          -- \compl or \^c
#check (∅ : Set α) -- \empty
#check (Set.univ : Set α)

/- If you *open* a namespace, you are able to use names in it
without the prefix. -/
open Set

#check (univ : Set α)






/- Showing that `x` is an element of `s ∩ t`, `s ∪ t` or `sᶜ`
corresponds by definition to conjunction, disjunction or negation. -/

#check mem_inter_iff x s t
#check mem_union x s t
#check mem_compl_iff s x

#check mem_univ x
#check notMem_empty x



/-
There are various ways to prove the following lemmas:
* use lemma `mem_inter_iff`
* use `simp`
* directly apply `constructor`
* give a direct proof: `⟨xs, xt⟩`
-/
example (hxs : x ∈ s) (hxt : x ∈ t) : x ∈ s ∩ t := by
  sorry
  done

example (hxs : x ∈ s) : x ∈ s ∪ t := by
  sorry
  done


example (hx : x ∈ s \ t) : x ∈ (s ∪ t) ∩ (sᶜ ∪ tᶜ) := by
  sorry
  done







/- `s ⊆ t` means that for every element `x` in `s`,
  `x` is also an element in `t`. -/
#check (subset_def : (s ⊆ t) = ∀ x ∈ s, x ∈ t)

example : s ∩ t ⊆ s ∩ (t ∪ u) := by
  sorry
  done

/- You can also prove it at the level of sets, without talking about elements. -/
example : s ∩ t ⊆ s ∩ (t ∪ u) := by
  sorry
  done





/- ## Proving two Sets are equal

You can prove that two sets are equal by applying `subset_antisymm`
or using the `ext` tactic.

`ext x` can prove that `s = t` if `x ∈ s ↔ x ∈ t` for a new variable `x`.
-/
#check (subset_antisymm : s ⊆ t → t ⊆ s → s = t)

example : s ∩ t = t ∩ s := by
  sorry
  done

/- We can also use existing lemmas and `calc`. -/
example : (s ∪ tᶜ) ∩ t = s ∩ t := by
  sorry
  done




/-
## Set-builder notation
We can define the set of elements in `t` satisfying `P` using
  `{ x : t | P x }`
There are also variants
  `{ x     | P x }`
  `{ x ∈ s | P x }`
-/

def evens : Set ℕ := {n : ℕ | Even n}
def odds : Set ℕ := {n | Odd n}

example : evensᶜ = odds := by
  sorry
  done





example : s ∩ t = {x | x ∈ s ∧ x ∈ t} := by rfl
example : s ∪ t = {x | x ∈ s ∨ x ∈ t} := by rfl
example : s \ t = {x | x ∈ s ∧ x ∉ t} := by rfl
example : s \ t = {x ∈ s | x ∉ t} := by rfl
example : sᶜ = {x | x ∉ s} := by rfl

example : (∅ : Set α) = {_x | False} := by rfl
example : (univ : Set α) = {_x | True} := by rfl


/-
## Other operations on sets
-/

/- We can take power sets. `𝒫` is typed using `\powerset`. -/
example (s : Set α) : 𝒫 s = {t | t ⊆ s} := by rfl


/- Question: What is the type of `powerset s`? -/
-- #check powerset s





/- We can take unions and intersections of families of sets
in three different ways:
* Given a family of sets `C : ι → Set α`
  we can take the union and intersection of `C i`
  as `i` ranges over all elements of `ι`.
-/
example (C : ι → Set α) :
    ⋃ i : ι, C i = {x : α | ∃ i : ι, x ∈ C i} := by ext; simp

example (C : ι → Set α) :
    ⋂ i : ι, C i = {x : α | ∀ i : ι, x ∈ C i} := by ext; simp



/-
* Given a family of sets `C : ι → Set α` and `s : Set ι`
  we can take the union and intersection of `C i`
  as `i` ranges over all elements in `s`.
-/
example (s : Set ι) (C : ι → Set α) :
    ⋃ i ∈ s, C i = {x : α | ∃ i ∈ s, x ∈ C i} := by ext; simp

example (s : Set ι) (C : ι → Set α) :
    ⋂ i ∈ s, C i = {x : α | ∀ i ∈ s, x ∈ C i} := by ext; simp




/-
* Given a collection of sets `C : Set (Set α)`
  we can take the union and intersection of `c`
  for all `c ∈ C`
-/

example (𝓒 : Set (Set α)) :
    ⋃₀ 𝓒 = {x : α | ∃ s ∈ 𝓒, x ∈ s} := by ext; simp

example (𝓒 : Set (Set α)) :
    ⋂₀ 𝓒 = {x : α | ∀ s ∈ 𝓒, x ∈ s} := by ext; simp


example (C : ι → Set α) (s : Set α) :
    s ∩ (⋃ i, C i) = ⋃ i, (C i ∩ s) := by
  sorry
  done





/- We can take images and preimages of sets.

`f ⁻¹' s` is the preimage of `s` under `f`.
`f '' s` is the image of `s` under `f`.

On paper, you would write `f(A)` or `f[A]` for the image
and `f⁻¹(B)` or `f⁻¹[B]` for the preimage.
This notation is hard to parse for Lean, since parentheses and ⁻¹
have so many different meanings in mathematics.
Therefore we use this funny notation.
-/

example (f : α → β) (s : Set β) : f ⁻¹' s = { x : α | f x ∈ s } := by rfl

example (f : α → β) (s : Set α) : f '' s = { y : β | ∃ x ∈ s, f x = y } := by rfl


example {s : Set α} {t : Set β} {f : α → β} : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t := by
  sorry
  done


/- We can do pointwise operations on sets (e.g. the Minkowski sum). -/

open Pointwise

example (s t : Set ℝ) :
    s + t = {x : ℝ | ∃ a ∈ s, ∃ b ∈ t, a + b = x } := by rfl

example (s : Set ℝ) : -s = {x : ℝ | -x ∈ s } := by rfl


/- We can write `{a, b, c, ...}` to write a set
where we explicitly enumerate its elements. -/

example : ({1, 3, 4} : Set ℝ) + {0, 3} = {1, 3, 4, 6, 7} := by
  sorry
  done



/- ## Intervals -/

/-
Lean has the following names for intervals:
("c" = closed, "o" = open, "i" = infinity)
Icc a b = [a, b]
Ico a b = [a, b)
Ioc a b = (a, b]
Ioo a b = (a, b)
Ici a   = [a, ∞)
Ioi a   = (a, ∞)
Iic b   = (-∞, b]
Iio b   = (-∞, b)
-/

example : Icc a b = {x | a ≤ x ∧ x ≤ b} := by rfl
example : Ico a b = {x | a ≤ x ∧ x < b} := by rfl
example : Ioc a b = {x | a < x ∧ x ≤ b} := by rfl
example : Ioo a b = {x | a < x ∧ x < b} := by rfl
example : Ici a   = {x | a ≤ x}         := by rfl
example : Ioi a   = {x | a < x}         := by rfl
example : Iic b   = {x | x ≤ b}         := by rfl
example : Iio b   = {x | x < b}         := by rfl

example : Icc a b ∩ Ici c = Icc (max a c) b := by
  sorry
  done
