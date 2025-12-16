import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.RingTheory.Real.Irrational
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.JacobianOneDim

open BigOperators Function Set Real Topology Filter
open ENNReal MeasureTheory Interval intervalIntegral
set_option linter.unusedVariables false
noncomputable section




inductive NaturalNumber where
| zero : NaturalNumber
| succ : NaturalNumber → NaturalNumber


/- # Last time

Last time we finished measure theory and integration.
Important theorems in this area:
* Fundamental theorem of calculus
* Dominated convergence theorem
* Fubini's theorem
* Change of variable formula

We saw inductive types. Declaring a new inductive type gives you:
- A new type, e.g. `NaturalNumber : Type`
- *constructors*, e.g. `NaturalNumber.zero` and `NaturalNumber.succ`
- A *recursor* `NaturalNumber.rec` that stated how to define functions
  recursively and prove things inductively.
- *computation rules* that state how to compute
  when the recursor is applied to a constructor.

Lean has a flexible *pattern-matching syntax* that elaborates
a recursive definition into applications of the recursor.



**Today**
* well-founded recursion and more on inductive types
* implementing logic in Lean



**Rest of the class**
We have given an introduction on how to do most core topics in Lean.

*Thursday* I will cover the logic of Lean
*Tuesday 23.12* the class is canceled.

In January will still cover:
* differential geometry
* a bit of metaprogramming
* good coding practices


Potential other topics:
* combinatorics (graph theory) (+1)
* cardinalities (and ordinals) (+1)
* Galois theory
* number theory
* ...
* anything you would like to see?

suggestions from class (no promises):
- schemes
- algorithm correctness + runtime
-/






/-
### Well-founded recursion

Lean also support *non-structural* recursion.
This is implemented using *well-founded recursion*.
Lean tries to prove automatically that the arguments
in the recursive calls are smaller than the input argument.
Lean raises an error if it cannot figure out why the function terminates
-/

/- the Fibonacci sequence -/
def F : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => F (n + 1) + F n

/- the number of factors 2 in a number.
Note: the `k@(n+1)` notation means that we pattern match
on the argument so that it has the shape `n + 1`,
but then uses the name `k` for `n + 1`. -/
def twoVal : ℕ → ℕ∞
  | 0         => ⊤
  | k@(n + 1) =>
    if k % 2 = 0 then
      twoVal (k / 2) + 1
    else
      0

def twoVal' : ℕ → ℕ∞
  | 0     => ⊤
  | n + 1 =>
    let k := n + 1
    if k % 2 = 0 then
      twoVal' (k / 2) + 1
    else
      0


/- The Ackermann function -/
def A : ℕ → ℕ → ℕ
| 0,     n     => n + 1
| m + 1, 0     => A m 1
| m + 1, n + 1 => A m (A (m + 1) n)
termination_by m n => (m, n)

/- `(b, n) ↦ ⌊log_b(n)⌋`, i.e. the logarithm rounded down.
In this case, we need to help Lean to show why it terminates.
You can also specify your own measure that decreases
using `termination_by`, though that is rarely needed. -/
def myLog (b : ℕ) : ℕ → ℕ
  | n => if h : b ≤ n ∧ 1 < b then myLog b (n / b) + 1 else 0
decreasing_by
  exact Nat.div_lt_self (by cutsat) h.2

/-
*Well-founded recursion* uses a special inductive type
`Acc` (for *accessibility*).

Take a look at these definitions if you want to know more information.
-/
#check WellFounded
#check Acc



/-
### Other inductive types

Many types in Lean are inductive types.
Here are some examples. Each of these inductive types
-/

#check Prod
/- Cartesian product of types. -/
inductive CartesianProduct (A B : Type*) where
  | pair : A → B → CartesianProduct A B

def CartesianProduct.fst {A B : Type*}
    (p : CartesianProduct A B) : A :=
  CartesianProduct.rec (fun a b ↦ a) p

#check Sum -- ⊕
/- Coproduct (disjoint union) of types. -/
inductive DisjointUnion (A B : Type*) where
  | left  : A → DisjointUnion A B
  | right : B → DisjointUnion A B

/- specific enumerated types. -/
inductive Booleans where
  | true : Booleans
  | false : Booleans

inductive SingletonType where
  | singlePoint : SingletonType

inductive EmptyType where
-- 0 constructors!


/-
*structures* are defined as non-recursive inductive types with one constructor.
Projections are automatically generated for structures -/
structure Point' where
  x : ℝ
  y : ℝ
  z : ℝ
#check Point'.rec
#check Point'.x

inductive Point where
  | mk : ℝ → ℝ → ℝ → Point

def Point.x : Point → ℝ
  | mk x y z => x
-- etc.




/- We can also define *inductive propositions*. -/

inductive Conjunction (A B : Prop) : Prop where
  | and_intro : A → B → Conjunction A B

inductive Disjunction (A B : Prop) : Prop where
  | left  : A → Disjunction A B
  | right : B → Disjunction A B

inductive Truth : Prop where
  | trivial : Truth

inductive Falsity : Prop where

inductive Existential (A : Type*) (P : A → Prop) : Prop where
  | intro : ∀ x, (P x → Existential A P)


inductive MyEquality (A : Type*) (a : A) : A → Prop where
  | mk : MyEquality A a a

/- Even equality is defined inductively.
This is a special: it is a inductive *family* of propositions.
We define for each type `A` we define `Equality A a b`
simultaneously for all `a b : A`. -/
inductive Equality (A : Type*) : A → A → Prop where
  | reflexivity : ∀ a : A, Equality A a a

#check Equality.rec
#check MyEquality.rec
/- it says roughly:
If I want to prove P(b)
and I know that a = b,
it is sufficient to prove P(a)
-/

/- We can define the proposition stating that a type is non-empty. -/
inductive IsNonempty (A : Type*) : Prop where
  | intro : A → IsNonempty A
-- IsNonempty A is equivalent to ∃ x : A, x = x
#check Classical.choice


/- Another example if inductive families comes from constructions
that construct the smallest collection of objects satisfying some property.

For example, if `g` is any collection of subsets of a type `X`,
the following gives the smallest topology where all sets in `g` are open.
Equivalently: it is the intersection of all topologies containing `g`. -/
inductive GenerateOpen {X : Type*} (g : Set (Set X)) : Set X → Prop
  | basic : ∀ s ∈ g, GenerateOpen g s
  | univ : GenerateOpen g univ
  | inter : ∀ s t, GenerateOpen g s → GenerateOpen g t → GenerateOpen g (s ∩ t)
  | sUnion : ∀ S : Set (Set X), (∀ s ∈ S, GenerateOpen g s) → GenerateOpen g (⋃₀ S)

def generateFrom {X : Type*} (g : Set (Set X)) : TopologicalSpace X where
  IsOpen := GenerateOpen g
  isOpen_univ := GenerateOpen.univ
  isOpen_inter := GenerateOpen.inter
  isOpen_sUnion := GenerateOpen.sUnion

/-
Something special happens with inductive propositions.
Some propositions (`∧`, `True`, `False`, `=`) can eliminate
to *any* sort (all types and `Prop`)
Other propositions (`∃`, `∨`, `Nonempty`) can only eliminate to `Prop`.

Look at type type of `motive` in the recursors below.

The difference is that the propositions `∃`, `∨` and `Nonempty`
can be proven with either different constructors
or one constructor applied to different arguments.
If such a proposition could eliminate to any type,
then (together with the computation rule)
you could derive a contradiction.

The behavior of eliminating to any Type is called "singleton elimination".
-/
#check Conjunction.rec
#check Disjunction.rec
#check Nonempty.rec
#check Equality.rec

example (P Q : Prop) (h : P ∨ Q) : ℕ := by
  obtain h|h := h -- this fails because disjunctions cannot eliminate to types.

/-
Induction on equality allows you to *cast* between type families applied to equal arguments.
(the same as substitution, but for types)
-/
example {n m : ℕ} (h : n = m) : Fin n → Fin m :=
  fun k ↦ Eq.rec k h




/-
# Logic
Now we will see how we can implement a logical system in Lean.
-/

/-
We will do propositional logic here for simplicity.

Mathlib also has `FirstOrder.Language.BoundedFormula`
(and related notions) to do first-order logic and model theory.
-/
def Variable : Type := ℕ

/- We define propositional formulae, and some notation for them. -/
inductive Formula : Type where
  | var : Variable → Formula
  | bot : Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | impl : Formula → Formula → Formula

open Formula
local notation:max (priority := high) "# " x:max => var x
local infix:30 (priority := high) " || " => disj
local infix:35 (priority := high) " && " => conj
local infix:28 (priority := high) " ⇒ " => impl
local notation (priority := high) "⊥" => bot



/- We define negation, truth and "if and only if"
from the primitive connectives. -/

def neg (A : Formula) : Formula := A ⇒ ⊥
local notation:(max+2) (priority := high) "~" x:max => neg x
def top : Formula := ~⊥
local notation (priority := high) "⊤" => top
def iff (A B : Formula) : Formula := (A ⇒ B) && (B ⇒ A)
local infix:29 (priority := high) " ⇔ " => iff






/- Let's define truth w.r.t. a valuation, i.e. classical validity -/

@[simp]
def IsTrue (φ : Variable → Prop) : Formula → Prop
  | ⊥      => False
  | # P    => φ P
  | A || B => IsTrue φ A ∨ IsTrue φ B
  | A && B => IsTrue φ A ∧ IsTrue φ B
  | A ⇒ B => IsTrue φ A → IsTrue φ B

def Valid (A : Formula) : Prop := ∀ φ, IsTrue φ A


def Satisfies (φ : Variable → Prop) (Γ : Set Formula) : Prop :=
  ∀ {A}, A ∈ Γ → IsTrue φ A

def Models (Γ : Set Formula) (A : Formula) : Prop :=
  ∀ {φ}, Satisfies φ Γ → IsTrue φ A

local infix:27 (priority := high) " ⊨ " => Models

variable {φ : Variable → Prop} {A B : Formula} {Γ Δ : Set Formula}

/- These lemmas will be useful later. -/

example (h : Γ ⊨ A) (h2 : Satisfies φ Γ) : True := by
  have h3 := h h2 -- the implicitness of φ in the definition of Models
  -- makes the argument φ here implicit.

@[simp] lemma isTrue_neg : IsTrue φ ~A ↔ ¬ IsTrue φ A := by simp [neg]

@[simp] lemma isTrue_top : IsTrue φ ⊤ := by simp [top]

@[simp] lemma isTrue_equiv :
    IsTrue φ (A ⇔ B) ↔ (IsTrue φ A ↔ IsTrue φ B) := by
  simp [iff, iff_def]

@[simp] lemma satisfies_insert_iff :
    Satisfies φ (insert A Γ) ↔ IsTrue φ A ∧ Satisfies φ Γ := by
  simp [Satisfies]

example : Valid (~~A ⇔ A) := by
  intro φ
  simp
  done




/- Let's define provability w.r.t. classical logic. -/
section
/- this is a hacky way to already use the notation for an inductive type
in the constructors while declaring the inductive type. -/
set_option hygiene false
local infix:27 " ⊢ " => ProvableFrom


/- `Γ ⊢ A` is the predicate stating that there is a proof tree
with conclusion `A` with assumptions from `Γ`.
This is a typical list of rules for natural deduction
with classical logic. -/
inductive ProvableFrom : Set Formula → Formula → Prop
  | ax    : ∀ {Γ A},   A ∈ Γ   → Γ ⊢ A
  | impI  : ∀ {Γ A B},  insert A Γ ⊢ B                → Γ ⊢ A ⇒ B
  | impE  : ∀ {Γ A B},           Γ ⊢ (A ⇒ B) → Γ ⊢ A  → Γ ⊢ B
  | andI  : ∀ {Γ A B},           Γ ⊢ A       → Γ ⊢ B  → Γ ⊢ A && B
  | andE1 : ∀ {Γ A B},           Γ ⊢ A && B           → Γ ⊢ A
  | andE2 : ∀ {Γ A B},           Γ ⊢ A && B           → Γ ⊢ B
  | orI1  : ∀ {Γ A B},           Γ ⊢ A                → Γ ⊢ A || B
  | orI2  : ∀ {Γ A B},           Γ ⊢ B                → Γ ⊢ A || B
  | orE   : ∀ {Γ A B C}, Γ ⊢ A || B → insert A Γ ⊢ C → insert B Γ ⊢ C → Γ ⊢ C
  | botC  : ∀ {Γ A},   insert ~A Γ ⊢ ⊥                → Γ ⊢ A
-- Remark: removing `insert ~A` from botC gives a constructive proof system.
end
/- Now we declare the notation for real. -/
local infix:27 (priority := high) " ⊢ " => ProvableFrom

def Provable (A : Formula) := ∅ ⊢ A

open ProvableFrom



/- We define a simple tactic `apply_ax`
to prove something using the `ax` rule.

This is done using Lean's *metaprogramming framework*.
We will see more of this in January. -/
syntax "solve_mem" : tactic
syntax "apply_ax" : tactic
macro_rules
  | `(tactic| solve_mem) =>
    `(tactic| first | apply mem_singleton
                    | apply mem_insert
                    | apply mem_insert_of_mem; solve_mem
                    | fail "tactic \'apply_ax\' failed")
  | `(tactic| apply_ax)  => `(tactic| { apply ax; solve_mem })


/- Let's see an example using the `apply_ax` tactic -/
example : {A, B} ⊢ A && B := by
  apply andI
  · apply_ax
  · apply_ax
  done


/- Exercise: prove that the double negation of a . -/
example : Provable (~~A ⇔ A) := by
  apply andI
  done

/- Exercise: prove the law of excluded middle. -/
example : Provable (A || ~A) := by
  sorry
  done

/- Exercise: We can now prove meta-theoretical properties about the logic.
In other words: what can we prove about the `Provable` predicate?

Here we show that if we can prove `A` from `Γ`, then we can prove it
from any superset of `Γ`. This is called *weakening*.

The `solve_by_elim` is a simple tactic that repeatedly applies
assumptions until the goal is solved. This can be useful in the following exercise.
-/
lemma weakening (h : Γ ⊢ A) (h2 : Γ ⊆ Δ) : Δ ⊢ A := by
  sorry
  done

/-
Let's prove the *soundness theorem*: if we can prove `A` from `Γ`,
then `A` is true whenever all formulas in `Γ` are true.
-/
theorem soundness_theorem (h : Γ ⊢ A) : Γ ⊨ A := by
  sorry
  done

/- The *completeness theorem* is the converse of the soundness theorem.
This is also true, but is significantly harder to prove,
so we will not do that here. -/



/- Exercise: prove one of the de-Morgan laws. -/
example : Provable (~(A && B) ⇔ ~A || ~B) := by
  sorry
  done
