import Mathlib.Tactic
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Category.RelCat
import Mathlib.CategoryTheory.Category.Grpd
import Mathlib.AlgebraicGeometry.Scheme

open CategoryTheory Functor Limits ConcreteCategory Opposite
set_option linter.unusedVariables false







/-
# Last time

Graph theory

- Lean has a notion of `Quiver`, `Digraph` and `SimpleGraph`
- Undirected graphs can be defined using a
  symmetric adjacency relation, or by defining it
  using unordered pairs `Sym2`.
- I showed an example of a graph algorithm (Dijkstra's algorithm)
  using `do` notation.

# Today: Category Theory
-/


/-
In category theory, we study the common structure from
different areas of mathematics in an abstract way.

What do groups, rings, topological spaces, sets, graphs,
measurable spaces and Banach spaces have in common?

* There is a notion of morphism between two objects
* We can compose morphisms, and there are identity morphisms.

This is captured in the notion of a *category*.
-/

universe v u v' u' w w'

/-
## Definition

From last time we saw the notion of a `Quiver`,
which associates a type `Hom x y` to any `x y : V`.
This is denoted `x ⟶ y` written with `\hom`.
It is a different arrow than the function arrow! -/

class MyQuiver (V : Type u) where
  Hom : V → V → Sort v

/-
A category moreover has
* an identity morphism `𝟙 X : X ⟶ X` (`\b1`)
* composition if `f : X ⟶ Y` and `g : Y ⟶ Z` then
  we have a composition `f ≫ g : X ⟶ Z`
  Note that the argument order is different than usual composition:
  `f ≫ g` corresponds to `g ∘ f`.
-/

class MyCategoryStruct (obj : Type u) : Type max u (v + 1)
    extends Quiver.{v + 1} obj where
  id : ∀ X : obj, Hom X X
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

/-
We require 3 axioms in a category:
* `𝟙 X` has to be a left and right identity
* `≫` is associative.
-/

class MyCategory (obj : Type u) : Type max u (v + 1)
    extends CategoryStruct.{v} obj where
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f := by cat_disch
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f := by cat_disch
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
      (f ≫ g) ≫ h = f ≫ g ≫ h := by cat_disch






/-
## Examples

The prototypical example of a category is the
*category of sets*, in Lean called the *category of types*. -/

example : Category (Type u) := by infer_instance

example (X Y : Type u) : (X ⟶ Y) = (X → Y) := by rfl

example {X Y Z : Type u} {g : Y ⟶ Z} {f : X ⟶ Y} : g ∘ f = f ≫ g := by rfl

example {X : Type u} : 𝟙 X = id := by rfl

/- Another example is the category of groups.
An object consists of a type `G` bundled together with
its group structure `Group G`. -/

structure MyGrpCat : Type (u + 1) where
  (carrier : Type u)
  [str : Group carrier]

example : Category GrpCat.{u} := by infer_instance

example (X Y : GrpCat.{u}) : (X ⟶ Y) ≃ (X →* Y) :=
  homEquiv (X := X) (Y := Y)
/- (we could make these two types definitionally equal,
but it's conventient for Lean to not conflate the two). -/


/- Similarly, there is a category of:
* monoid with monoid homomorphisms
* abelian groups with group homomorphisms
* rings with ring homomorphisms
* topological spaces with continuous functions
* finite types with functions
-/

#synth Category MonCat
#synth Category CommGrpCat
#synth Category RingCat
#synth Category TopCat
#synth Category FintypeCat




/- Morphisms do not have to be functions.
Another category is the category of types with relations.
A morphism `R : X ⟶ Y` is a relation over `X` and `Y`, i.e.
an element of `Set (X × Y)`. -/

#synth Category RelCat
#print RelCat

def myComp {X Y Z : Type*} (R : Set (X × Y)) (S : Set (Y × Z)) :
    Set (X × Z) :=
  {(a, c) | ∃ b, (a, b) ∈ R ∧ (b, c) ∈ S}




/- The objects of a category need not be types.
Given a partial order (or preorder) `(X, ≤)`,
then we can view `X` as a category by taking
* as objects the elements from `X`
* `x ⟶ y` has a unique inhabitant if `x ≤ y` and is empty otherwise.
-/

section PartialOrder

variable {X : Type*} [PartialOrder X]

#synth Category X

example {x y : X} (f : x ⟶ y) : x ≤ y := leOfHom f
example {x y : X} (h : x ≤ y) : x ⟶ y := homOfLE h

end PartialOrder

/-
Given two categories `C` and `D` we can define a *functor*
`F : C ⥤ D` (typed with `\functor`) as consisting of
* a map on objects `F.obj : C → D`
* a map on morphisms: if `f : x ⟶ y` in `C`,
  then `F.map f : F.obj x ⟶ F.obj Y`
* such that `F.map` respects `𝟙` and `≫`.
-/

structure MyFunctor.{v₁, v₂, u₁, u₂}
    (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] :
    Type max v₁ v₂ u₁ u₂ where
  obj : C → D
  map : ∀ {X Y : C}, (X ⟶ Y) → ((obj X) ⟶ (obj Y))
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X) := by cat_disch
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    map (f ≫ g) = map f ≫ map g := by cat_disch


/- This gives another category with as object categories
and as morphisms functors. -/

#synth Category Cat

/-
## Universes

In category theory you often have to think about universe levels
a bit more than usual.

If `X : Type u`, then `Category.{v, u} X` gives a category-structure on `X`,
where the morphisms live in `Type v`.
This can be abbreviated to `Category.{v} X`.

Most of the categories discussed above were *large* categories.
In set theory, this would mean that the objects of the category
are a collection that is *too large* to be a set.
E.g. the collection of all sets or the collection of all groups.

In Lean this means that the objects live one universe up:
e.g. the category of all groups from universe `u`
has as objects something that lives in universe `u + 1`
(and the morphisms live in universe `u`)
-/


variable {C : Type u} [Category.{v} C] {X Y : C}
#check X ⟶ Y











/- Given objects `X` and `Y` in a category,
we can ask whether they are isomorphic.
`X ≅ Y` (`\iso`) is the type of isomorphisms between `X` and `Y`
-/

#check X ≅ Y

structure MyIso (X Y : C) where
  hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv_id : hom ≫ inv = 𝟙 X := by cat_disch
  inv_hom_id : inv ≫ hom = 𝟙 Y := by cat_disch




/-
## Constructions

We can construct new categories from existing categories.
If `C` and `D` are categories, then
* `Cᵒᵖ` is the category `C` with all morphisms reversed.
* `C × D` is the product category with as morphisms
  a pair of a morphism in `C` and one in `D`.
* For `X : C`, the slice category `C / X` is called `Over X`.
  Objects are morphisms `Y ⟶ X` in `C` and morphisms are
  commutative triangles in `C`.
  (`Under X` is the coslice category)
* `C ⥤ D` is the functor category with as morphisms
  *natural transformations*.
-/

variable {D : Type u'} [Category.{v'} D] {X : C}

#synth Category Cᵒᵖ
#synth Category (C × D)
#synth Category (Over X)
#synth Category (Under X)
#synth Category (C ⥤ D)

structure MyNatTrans (F G : C ⥤ D) : Type max u v' where
  app : ∀ X : C, F.obj X ⟶ G.obj X
  naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    F.map f ≫ app Y = app X ≫ G.map f := by cat_disch

/-
Note: `Cᵒᵖ` is a category on the same objects as `C`.
In order for Lean to not get confused when
we write `X ⟶ Y` whether we mean morphisms in `C` or `Cᵒᵖ`,
`Cᵒᵖ` is actually defined as an equivalent copy of `C`
-/

example (X : C) : Cᵒᵖ := op X
example (X : Cᵒᵖ) : C := unop X
example {X Y : C} (f : X ⟶ Y) : op Y ⟶ op X := f.op
example {X Y : C} (f : op X ⟶ op Y) : Y ⟶ X := f.unop
example {X Y : C} (f : X ≅ Y) : op X ≅ op Y := f.op.symm


/-
## Limits

Many categories have more structure than just morphisms.
For example, types, groups, rings, topological spaces all
have a notion of *products*.
-/

#synth HasProducts (Type u)
#synth HasProducts RingCat

/-
This is a special case of a more general notion of
*limits* inside a category.

Given a diagram `F` in a category `C`, a cone is an
object in `C` and a morphism from `C` to any object in the diagram,
such that all resulting triangles commute.
-/

variable {J : Type w} [Category.{w'} J]

structure MyCone (F : J ⥤ C) where
  pt : C
  π : (const J).obj pt ⟶ F

/-
A cone `t` is a *limit cone* if the for every other cone `s`
there is a *unique* morphisms `s ⟶ t` such that
all the resulting triangles commute.
-/

structure MyIsLimit {F : J ⥤ C} (t : Cone F) where
  lift : ∀ s : Cone F, s.pt ⟶ t.pt
  fac : ∀ (s : Cone F) (j : J), lift s ≫ t.π.app j = s.π.app j := by
    cat_disch
  uniq : ∀ (s : Cone F) (m : s.pt ⟶ t.pt)
    (_ : ∀ j : J, m ≫ t.π.app j = s.π.app j), m = lift s := by
    cat_disch

structure MyLimitCone (F : J ⥤ C) where
  cone : Cone F
  isLimit : IsLimit cone

/- We say that a diagram has a limit if there
*exists* a limit cone.
Using this we can easily define whether a category
has limits of a certain shape, e.g.
whether it has products or pullbacks. -/

class MyHasLimit (F : J ⥤ C) : Prop where
  exists_limit : Nonempty (LimitCone F)

class MyHasLimitsOfShape : Prop where
  has_limit : ∀ F : J ⥤ C, HasLimit F

abbrev MyHasProducts :=
  ∀ J : Type w, HasLimitsOfShape (Discrete J) C

abbrev MyHasPullbacks :=
  HasLimitsOfShape WalkingCospan C

/- Entirely analogously, we define colimits. -/

#check HasColimit

/- We use `PreservesLimits` to say that a functor maps limit to limits. -/

#check PreservesLimits







/-
# More on Functors

An equivalence `C ≌ D` (`\backcongr`) of categories is defined
as a so-called *half-adjoint equivalence*.
-/

structure MyEquivalence
    (C : Type u) (D : Type u') [Category.{v} C] [Category.{v'} D] where
  functor : C ⥤ D
  inverse : D ⥤ C
  unitIso : 𝟭 C ≅ functor ⋙ inverse
  counitIso : inverse ⋙ functor ≅ 𝟭 D
  functor_unitIso_comp : ∀ X : C,
    functor.map (unitIso.hom.app X) ≫
    counitIso.hom.app (functor.obj X) =
      𝟙 (functor.obj X) := by cat_disch

/- The Yoneda-embedding `y` is defined as `y X Y := Hom Y X` -/

example : C ⥤ Cᵒᵖ ⥤ Type v := yoneda

example {X Y : C} : (yoneda.obj X).obj (op Y) = (Y ⟶ X) := rfl

/-
The *Yoneda-lemma* states that natural transformations
`y X ⟶ F`
are equivalent to `F X`

(other results show that this equivalence is natural in both `F` and `X`.)
-/

example {X : C} {F : Cᵒᵖ ⥤ Type v} :
    (yoneda.obj X ⟶ F) ≃ F.obj (op X) :=
  yonedaEquiv

/-
Given two functors `F : C ⥤ D` and `G : D ⥤ C`,
we say that this forms an *adjunction*, written `F ⊣ G` (`\dashv`),
if there are natural equivalences:
  `Hom_D(F X, Y) ≃ Hom_C(X, G Y)`
for any `X : C` and `Y : D`.
-/

variable {F : C ⥤ D} {G : D ⥤ C}

example (h : F ⊣ G) (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y) :=
  h.homEquiv X Y

/- Some examples of functors:
* `forget` is the *forgetful functor* from a concrete category to `Type _`
  A concrete category is a category where
  - the objects are types with some structure, and
  - the morphisms are functions that satisfy some properties.
* `forget₂` is the forgetful functor between concrete categories
  that only forgets some of the structure.
* `GrpCat.free` is the free group on a set.
-/

example : GrpCat.{u} ⥤ Type u := forget GrpCat
example : GrpCat ⥤ MonCat := forget₂ GrpCat MonCat
example : Type u ⥤ GrpCat.{u} := GrpCat.free

/- The free functor is left adjoint to the forgetful functor.
This is because for a set `X` and a group `G`, we have
`(free X →* G)  ≃  (X → G)`
-/

example : GrpCat.free ⊣ forget GrpCat := GrpCat.adj


/- Briefly: (but outside the scope of today's class)

* A *sheaf* on a topological space `X` in category `C`
  is a functor `(Opens X)ᵒᵖ ⥤ C` that satisfies a locality and gluing axiom.
  Roughly: a compatible family of elements uniquely defines
  an element over the union of those elements.
* A *scheme* is a topological space equipped with a sheaf of
  commutative rings, such that
  - every *stalk* is a local ring
  - it is "locally affine"
-/

#check Presheaf.IsSheaf
#check AlgebraicGeometry.Scheme
