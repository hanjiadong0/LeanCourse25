import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential

open Function

/-
# Announcement

There will be a seminar on more advanced aspects of Lean next semester (Tuesdays, 14-16).
No knowledge beyond attending this course is required.
The initial meeting (*Vorbesprechung*) is on Thursday, February 12 at 10.15 in room 0.011.
Detail can be found on the course webpage: https://github.com/grunweg/LeanSeminar26



# Last time: metaprogramming II

writing some simple tactics

# Today: cardinal and ordinal numbers

-/

/-
## Cardinal numbers

Let us recall the mathematics "on the blackboard" first.

Cardinal numbers are about comparing the size of sets (or types).
Two sets have the same cardinality if there is a bijection between them.
The core notion behind cardinals is comparing

**Definition.** We say two sets A and B have the same cardinality if and only if there is a
bijection φ : A ≃ B.

**Examples.**
(a) The sets `{1, 3, 5}` and `{2, 4, 6}` have the same cardinality.
(b) If `n` and `m` are distinct natural numbers, the sets `{0, 1, ..., n}` and `{0, 1, ..., m}`
    do *not* have the same cardinality. (Exercise. Use induction over n and then over m.)
(c) The sets `ℕ` and `2ℕ = { 2 * n | n ∈ ℕ} ⊆ ℕ` have the same cardinality.

The last example highlights a surprising fact: it's possible for a proper subset to be bijective
to the full set. (In fact, a set is infinite if and only if such a set exists.)

Two more examples:
(d) `ℕ × ℕ` and `ℕ` have the same cardinality.
(e) `ℚ` and `ℕ` have the same cardinality.
(f) `ℝ × ℝ` and `ℝ` have the same cardinality. (This is harder to prove.)

**Observe.** Having the same cardinality is an equivalence relation. (Exercise!)

**Definition.** A cardinal number is an equivalence class of sets,
w.r.t. the equivalence relation of having the same cardinality.

Thus, example (f) precisely says `|ℝ × ℝ| = |ℝ|`.

Let's go a step further and compare cardinalities.
**Definition.** Given two sets `A` and `B`, we say `|A| ≤ |B|` if and only if
  there exists an injective map `f : A → B`.

**Exercise.** We have `|A| ≤ |B|` if and only if there exists a surjective map `f : B → A`.

**Observe.** The relation `≤` on cardinalities is reflexive and transitive.

In fact, it is also anti-symmetric (i.e., `|A| ≤ |B|` and `|B| ≤ |A|` implies `|A| = |B|`)
and total (for any two sets, either `|A| ≤ |B|` or `|B| ≤ |A|`). This is harder to prove,
and follows from the **Cantor-Schröder-Bernstein theorem**.


We can define arithmetic operations on cardinals.
- addition: `|A| + |B| := |A ∪ B|` (disjoint union)
- multiplication: `|A| * |B| := |A × B|`
- exponentiation: `|B| ^ |A| := |A → B|`,
  where the right hand side denotes the set of functions from A to B.

**Definition.** The **successor** of a cardinal number `c` is the smallest cardinal number
which is larger than `c`. (This minimum exists: see below.)

-/

-- Let's look at the definition in Lean.
-- In Lean, we speak about types instead of sets. Given a type, there is a corresponding cardinal.
#check Cardinal.mk

-- Note the universe level `u`: for every universe level, there is a corresponding notion of
-- *cardinals in universe u* (which have type `Type (u + 1)`).
#check Cardinal

-- These are the quotient of `Type u` by the equivalence we defined above.
#check Cardinal.isEquivalent


-- The universe level `u` is important:
-- the notion of cardinals expands as you enlarge the universe you are considering.

-- To illustrate this, consider the natural numbers: they live in Type = Type 0.
#check (ℕ : Type 0)
-- To speak about the natural numbers in a higher universe, we can use `ULift`:
#check (ULift ℕ : Type 4)
-- Mathematically, however, nothing changed: they are still "the same type".


-- This is different for cardinal numbers. ULift induces a map
-- from `Cardinal.{u + 1}` to `Cardinal.{u + 2}`: this map is not surjective.

universe u
example : Add (Cardinal.{u}) := by infer_instance

variable {α β : Cardinal.{u}}
-- Let's verify the definitions of addition and multiplication:
-- Addition on cardinals is defined by taking the sum of the underlying types.
example : .mk (α.out ⊕ β.out) = α + β := by simp
-- Multiplication is defined by taking the product of the underlying types.
example : .mk (α.out × β.out) = α * β := by simp
-- Powers are defined by taking the function type between the underlying types.
example : .mk (α.out → β.out) = β ^ α := by simp

-- Let's verify how the order on cardinals is defined in Lean.
#synth LE Cardinal
#check Cardinal.instLE

-- This is the Cantor-Schroeder-Bernstein theorem (for bijective functions).
#check Embedding.schroeder_bernstein


/- ## Ordinal numbers

**Recall.** An order `≤` on a set `S` is called a **well-ordering** if and only if
every non-empty subset `T ⊆ S` has a least element (w.r.t. `≤`).

The **well-ordering principle** says that every non-empty set admits a well-order.
It is equivalent to the axiom of choice (i.e., assumed in standard mathematics).
So, e.g. the real numbers admit a well-ordering --- but we don't know at all how it looks.

**Definition.** An ordinal number is an equivalence class of well-ordered sets,
with respect to order-isomorphisms (i.e., bijections that preserve the ordering).

For two ordinals `α = [(S,≤)]` and `β = [(T, ≤')]`, we say `α ≤ β` if there exists an injection
`α : S → T` which is strictly monotone, i.e. preserves the ordering.

**Fact.** This defines a total order.
(This proof uses induction over ordinal numbers, which we may discuss later this session.)

Each ordinal number has a canonical representative: the set of all ordinals which are strictly
smaller than it.

**Fact.** Ordinals (w.r.t. this order above) are well-ordered.
**Non-proof.** By the axiom of choice, we know there exists some well-ordering on the collection
of all ordinals. Aside from set theory issues (is this a set? a class? etc.), this is not helpful:
we want to prove that *the order we defined* is a well-order!
**Proof sketch.** Let `S` be a non-empty set of ordinal numbers.
  Choose an element `α` of `S`; consider the *set* `A` of ordinals smaller than `α`.
  By the above, `A` is well-ordered (and so is any subset of `A`).
  If `S ∩ A` is empty, `α` is a least element of `S` and we're done.
  Otherwise, `S ∩ A` is a non-empty set and well-ordered, hence has a least element.

-/

#check Ordinal

#check Ordinal.isEquivalent

-- An equivalence of types which preserves the relations on these types.
#check RelIso


-- Let's verify how the order on ordinals is defined in Lean.
#synth LE Ordinal
#check Ordinal.partialOrder

-- The key lemma for the totality of the partial order.
#check InitialSeg.total

/-
We can also define arithmetic operations on ordinals
- addition: "first all elements from the first set, then the second one"
- multiplication: lexicographic ordering
- successor ordinals: "add a top element" (`WithTop` in Lean), i.e. `WithTop α`

-/


variable {α β : Ordinal.{u}}

-- Let's verify the definition of addition of ordinals.
#synth Add Ordinal
#check Ordinal.add
#check RelIso.sumLexCongr

-- Powers of ordinals are defined by *transfinite recursion*: let me omit the details.
#synth Pow Ordinal Ordinal
#check Ordinal.instPow



/- ## Cardinal and ordinal numbers

Cardinal and ordinal numbers are related: a cardinal number has an associated ordinal,
and vice versa. Both maps are order-preserving.

The cardinal number associated to an ordinal is easy to define:
it is the cardinal defined by the underlying type.

This map is not injective: for each infinite cardinality, there are many ordinal numbers with that
cardinality. (We will see examples later.) To a cardinal, however, we can associate the *smallest*
ordinal number of that cardinality. This is well-defined because ordinals are well-ordered.

-/

-- The cardinality of an ordinal.
#check Ordinal.card
-- The ordinal associated to a cardinal number.
#check Cardinal.ord

-- These maps are a one-sided inverses:
-- converting a cardinal to an ordinal and back yields the same cardinal.
example {α : Cardinal} : (Cardinal.ord α).card = α := by simp
#check Cardinal.ord_injective
#check Cardinal.card_surjective

-- In the other direction, we are replacing an ordinal by the smallest ordinal of the same
-- cardinality.
#check Cardinal.ord_eq

-- The map from cardinals to ordinals is order-preserving.

/-
**Corollary.** Cardinal numbers are well-ordered.
**Proof sketch.** Given a non-empty set `S` of cardinals, consider the set `T` of corresponding
ordinals. Since ordinal numbers are well-ordered, `T` has a least element `β = Cardinal.ord α`.
Then `α = Ordinal.card β` is a least element of `S`.
-/

/- Addition and multiplication on cardinals and ordinals coincide. -/
example {α β : Ordinal} : (α + β).card = α.card + β.card := by exact?
example {α β : Ordinal} : (α * β).card = α.card * β.card := by exact?

-- The other direction also holds, but mathlib seems to be missing this fact.
example {α β : Cardinal} : (α + β).ord = α.ord + β.ord := by sorry

-- In fact, the sum of cardinals is easy to describe.
-- If both cardinals are finite, [n] + [m] = [n + m]; otherwise addition is the maximum.
-- Cardinal.aleph0 is the cardinality of countable sets, the smallest infinite cardinal.
#check Cardinal.add_eq_max
-- Multiplication is similar: for finite cardinalities it is easy to describe; if one factor is zero
-- the product is zero. Otherwise, it is the maximum of the two cardinalities.
#check Cardinal.mul_eq_max_of_aleph0_le_right



/- Here is an operation which differs between cardinals and ordinals.

**Definition.**
The **successor** of an ordinal number `α` is the ordinal obtained by adding a new element ⊤
which is larger than any element in `α` (in Lean: `WithTop α`).
The **successor** of a cardinal `c` is the smallest cardinal which is larger than `c`.

Let's look at some specific cardinals and ordinals and see how these differ. -/

-- The smallest infinite cardinality is the cardinality of `ℕ`, countable types.
-- It is also called `ℵ₀` ("aleph nought").
#check Cardinal.aleph0
example : (Cardinal.mk ℕ) = Cardinal.aleph0 := by exact Cardinal.mk_nat

-- The smallest infinite ordinal is called `ω₀`, and
-- corresponds to the natural numbers as a well-ordered set.
#check Ordinal.omega0
example : Ordinal.lift (Ordinal.type (α := ℕ) (· < ·)) = Ordinal.omega0 := by exact?

example : Cardinal.aleph0.ord = Ordinal.omega0 := by exact?

-- The successor of `ω₀`, denoted `ω₀ + 1`, has cardinality `ℵ₀` again.
example : (Order.succ (Ordinal.omega0)).card = Cardinal.aleph0 := by simp

-- The successor of `ℵ₀` is the smallest uncountable cardinal, called `ℵ₁`.
-- The successor of `ℵ₁` is called `ℵ₂`, etc.
-- In fact, we can define a cardinal number `ℵₐ` for every ordinal number `a`.
#check Cardinal.aleph 1

/- How do larger cardinal numbers look? Cantor proved that the power set of a set has greater
cardinality: so starting with a set and forming the power set iteratively yields an infinite
strictly increasing sequence of cardinals.
In Lean, we take a type `α` and consider `Set α`. -/
#check Cardinal.mk_set

-- For instance, we have `|𝓟 ℕ| = |ℝ|`: the real numbers are uncountable.
-- Is this the smallest cardinality larger than `|ℕ|`? This is known as the continuum hypothesis.
lemma continuumHypothesis : Cardinal.mk (Set ℕ) = Cardinal.aleph 1 := by sorry

-- Is this true or false? **You may choose.**
-- The continuum hypothesis is independent of the standard axioms in set theory
-- (and also the rules of Lean's type theory).
-- You can add the continuum hypothesis, or its negation, as additional axiom as you prefer.






-- Thank you for listening. Take the remaining time to work on your project;
-- feel free to ask any questions you may be stuck with.
