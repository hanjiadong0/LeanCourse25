import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.CategoryTheory.Limits.Yoneda

open CategoryTheory Functor
noncomputable section

/-! # Exercises to practice -/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/--
**Exercise 1**: The category of walks.

Here is the notion of walk introduced in the lecture. -/
inductive MyWalk : V → V → Type _
  | nil {u : V} : MyWalk u u
  | cons {u v w : V} (h : G.Adj u v) (p : MyWalk v w) : MyWalk u w

def MyWalk.support {u v : V} : G.MyWalk u v → List V
  | nil => [u]
  | cons _ p => u :: p.support

/-- A walk is a *path* if no vertex is visited twice. -/
structure MyWalk.IsPath {u v : V} (p : G.MyWalk u v) : Prop where
  support_nodup : p.support.Nodup


/-
Define concatenation of walks, and show that this defines a category with object type `V` and
`Hom u v` defined as `G.MyWalk u v`.
-/

def concat {u v w : V} (p : G.MyWalk u v) (q : G.MyWalk v w) : G.MyWalk u w :=
  sorry

def walkCategory : Category V := sorry


/-
**Exercise 2**: define a reduction of a walk into a path by removing any loops it makes.
-/

def MyWalk.reduce {u v : V} (p : G.MyWalk u v) : G.MyWalk u v :=
  sorry

lemma MyWalk.isPath_reduce {u v : V} (p : G.MyWalk u v) : p.reduce.IsPath := by
  sorry
  done


end SimpleGraph

namespace Category

/-
**Exercise 3**: we will prove some lemmas about isomorphisms.

**Note**: We use our own version of isomorphisms, so you cannot use the results from Mathlib.
-/

variable {C : Type*} [Category C] {D : Type*} [Category D] {X Y Z : C}

structure MyIso (X Y : C) where
  hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv_id : hom ≫ inv = 𝟙 X := by cat_disch
  inv_hom_id : inv ≫ hom = 𝟙 Y := by cat_disch

local infixr:10 (priority := high) " ≅ " => MyIso

def MyIso.trans (f : X ≅ Y) (g : Y ≅ Z) : X ≅ Z := sorry

def MyIso.symm (f : X ≅ Y) : Y ≅ X := sorry

def MyIso.rfl : X ≅ X := sorry

/- hint: since we haven't marked `MyIso` with `@[ext]`, we cannot use the `ext` tactic here yet.
Instead, do cases on both `f` and `f'`, and then `simp` will simplify the goal. -/
@[ext]
lemma MyIso.ext {f f' : X ≅ Y} (h : f.hom = f'.hom) : f = f' := by
  sorry
  done


-- @[simps]
def MyIso.map {X X' : C} (F : C ⥤ D) (f : X ≅ X') : F.obj X ≅ F.obj X' := sorry

-- @[simps]
def MyIso.prod {X X' : C} {Y Y' : D} (f : X ≅ X') (g : Y ≅ Y') : (X, Y) ≅ (X', Y') := sorry

/- Now show that isomorphisms in the product category are pairs of isomorphisms.
The two functors below are already defined in Mathlib, and might be useful.

It will be useful to mark the definitions above as `simps`. This means that `(f.prod g).hom` and
`(f.prod g).inv` will both be simplified by unfolding the definition, but `f.prod g`
itself won't be.
-/

#check CategoryTheory.Prod.fst
#check CategoryTheory.Prod.snd

def prodIsoEquiv {X X' : C} {Y Y' : D} : ((X, Y) ≅ (X', Y')) ≃ (X ≅ X') × (Y ≅ Y') := sorry


end Category

/-! # No exercises to hand-in. -/
