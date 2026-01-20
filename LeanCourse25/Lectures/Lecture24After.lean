import LeanCourse25.Lectures.DifferentialGeometryNotation
import LeanCourse25.Lectures.Immersion
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere

open ContDiff Manifold Function Metric Module Set TopologicalSpace
noncomputable section




/-!
# Last time: category theory

* categories, functors
* examples
* universes in category theory
* constructions: opposite category, products, Over, Under, natural transformations
* limits
* Yoneda embedding; forgetful functors

-/

/- # Today: differential geometry

Let's see some intuition first.






Now, let's see the formal definition in "pen-and-paper mathematics".



Now, let us review the definition in Lean.

-/

/-
How do we formalise manifolds in mathlib? Let's ignore boundary and corners at first,
and just think about formalising **charts** and manifolds.

Let `M` be a manifold modelled on the topological space `H`:
we certainly need the following hypotheses
-/
variable {M H : Type*} [TopologicalSpace M] [TopologicalSpace H]

/- The naive definition of chart would be "a homeomorphism between open subsets of `M` and `H`". -/
def NaiveChart (s : Opens M) (t : Opens H) := s ≃ₜ t

/- However, this would be rather unpleasant to work with: given a point `p : M`,
to even write to "apply the chart at `p` to `p`", we need to pass a proof that `p` is in the domain
of the chart, *every single time* we apply this. -/

example {s : Opens M} {t : Opens H} {p : M} (hp : p ∈ s) (φ : NaiveChart s t) : H := by
  -- Cannot just apply φ to p; need to pass a proof that `p ∈ s`.
  --let y := φ.toFun p -- errors
  let y := φ.toFun ⟨p, hp⟩
  -- Cannot return `y` directly.
  -- apply y -- errors
  apply y.val

/- Solution: use the junk value pattern
Charts map `M` to `H`, but we only prescribe their value on their `source` and `target`.
-/
#check PartialEquiv
#check OpenPartialHomeomorph


/- A topological space is locally Euclidean if you have a
partial homeomorphism to `ℝⁿ` around each point in `X`.
We record a preferred chart for each point. -/
#check ChartedSpace



/- A smooth manifold is a charted space structure
such that for any two charts the coordinate change function
between the charts is smooth on their common domain.
We also require that the space is Hausdorff and second-countable. -/
variable {E M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [SecondCountableTopology M] [T2Space M]
  {e e' : OpenPartialHomeomorph M E}

/- We want to require the following condition for smooth manifolds. -/
#check ContDiffOn ℝ ⊤ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source


/- This is captured by the predicate `HasGroupoid`. -/
#check HasGroupoid

/- We can also equip a manifold with another groupoid structure,
to define the class of `C^k` manifolds or analytic manifolds,
or other classes of manifolds. -/
#check StructureGroupoid


/- Here `contDiffGroupoid` specifies the groupoid structure
on partial homeomorphisms stating that coordinate change functions
must be smooth -/
#check contDiffGroupoid

/- `e.symm ≫ₕ e' : ℝⁿ → ℝⁿ` is the coordinate change function from `e` to `e'`. -/
example [IsManifold 𝓘(ℝ, E) ⊤ M]
    {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ atlas E M) (he' : e' ∈ atlas E M) :
    ContDiffOn ℝ ⊤ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source := by
  have := (contDiffGroupoid ⊤ 𝓘(ℝ, E)).compatible he he'
  simpa [contDiffPregroupoid] using this.1


/- The general definition of manifolds in Mathlib is
more general than this example:
* It can be over any normed field, such as `ℝ`, `ℂ` or the p-adic numbers;
* It can have infinite dimension;
* It can have boundaries or corners. -/

/- Models with corners allow speaking about manifolds with boundary and corners.
There is a map `I : H → E` where `E` is a normed space over a field `𝕜`.

Example: `E = ℝⁿ`, `H` is a half-space, and `I : H → E` is the inclusion.
This map `I` is called a *model with corners*.
`𝓡 n` is notation for the identity map `ℝⁿ → ℝⁿ`.
`𝓡∂ n` is the inclusion from the half-space into `ℝⁿ` -/

#check ModelWithCorners

variable {n : ℕ}

#check 𝓡 n
#check 𝓡∂ 3

#check IsManifold


section examples

section unitInterval
open unitInterval

#check I -- I is notation for the interval [0, 1]

/- The interval [0, 1] is modelled by two charts with model space [0, ∞),
so it is a topological manifold -/
#synth ChartedSpace (EuclideanHalfSpace 1) I

/- To state that it is a smooth manifold, we have to say
that all coordinate changes live in the groupoid of smooth maps -/
#synth HasGroupoid I (contDiffGroupoid ∞ (𝓡∂ 1))

/- This is the same as saying that `I` forms a smooth manifold. -/
#synth IsManifold (𝓡∂ 1) ⊤ I

/- Atlases are not maximal in general, but we can use `maximalAtlas`
to consider a maximal atlas. -/
#check (contDiffGroupoid ∞ (𝓡∂ 1)).maximalAtlas I

end unitInterval


/- The sphere in a finite-dimensional inner product space is a smooth manifold -/

variable (n : ℕ) (E : Type*) [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [Fact (finrank ℝ E = n + 1)]

#synth IsManifold (𝓡 n) ω (sphere (0 : E) 1)

/- The map 𝕊ⁿ ↪ ℝⁿ⁺¹ is smooth -/
example : ContMDiff (𝓡 n) 𝓘(ℝ, E) ⊤
    (fun x ↦ x : sphere (0 : E) 1 → E) := by
  exact contMDiff_coe_sphere

/- The circle is a Lie group -/
example : LieGroup (𝓡 1) ⊤ Circle := by
  infer_instance

end examples









/- ## Interior and boundary points -/

#check ModelWithCorners.IsInteriorPoint

-- There are two kinds of manifolds without boundary.
-- (a) The model with corners has no boundary, because its range is the whole space.
#check ModelWithCorners.Boundaryless
-- (b) Every point is an interior point.
#check BoundarylessManifold
-- Condition (a) is easier to check, but condition (b) is more general.

-- There is a definition of "manifolds whose boundary is smooth", which is not in mathlib yet.



-- Here is how to declare a general manifold with boundary and corners. It's a little verbose.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I n M]
  -- Here's a second one.
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] (J : ModelWithCorners 𝕜 F G)
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J n N]

-- Here's how to access the atlas.
#check atlas H M

-- The preferred chart at x.
variable {x : M} in
#check chartAt H x

-- The corresponding *extended chart*, mapping into `E`.
variable {x : M} in
#check extChartAt I x


-- Differentiability, continuous differentiability etc. all have analogues for manifolds.
variable {f : M → N} {s : Set M} {x : M}

-- `f` is `C^n`
#check ContMDiff I J n f
-- Equivalently, you can write the following:
-- note that you don't need to specify the model with corners any more.
#check CMDiff n f

-- `f` is `C^n` at `x`
#check ContMDiffAt I J n f x
#check CMDiffAt n f x

-- `f` is differentiable on `s`
#check MDifferentiableOn I J f s
#check MDiff[s] f

-- `f` is `C^n` on `s`
#check CMDiff[s] n f



/- ## Tangent space & tangent bundle -/

-- A smooth manifold has a tangent space at each point.

/- A differentiable map between manifolds induces a map on tangent spaces. -/

example (f : M → N) (_hf : MDifferentiable I J f) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace J (f x) :=
  mfderiv I J f x
-- Or, in leaner notation
example (f : M → N) (_hf : MDiff f) (x : M) :
    TangentSpace% x →L[𝕜] TangentSpace% (f x) :=
  mfderiv% f x

-- There is also a version within a set, analogous to `fderivWithin`.
example (f : M → N) (_hf : MDiff f) (x : M) : TangentSpace% x →L[𝕜] TangentSpace% (f x) :=
  mfderiv[s] f x

-- If `f` is not differentiable at `x`, then `mfderiv I J f x` is defined to be zero.

-- Here is how to state the chain rule.
example {f g : M → M} (x : M)
    (hg : MDifferentiableAt I I g (f x)) (hf : MDifferentiableAt I I f x) :
    mfderiv I I (g ∘ f) x = (mfderiv I I g (f x)).comp (mfderiv I I f x) :=
  mfderiv_comp x hg hf

example {f g : M → M} (x : M)
    (hg : MDiffAt g (f x)) (hf : MDiffAt f x) :
    mfderiv% (g ∘ f) x = (mfderiv% g (f x)).comp (mfderiv% f x) :=
  mfderiv_comp x hg hf

/- I am showing you both notations since
(1) the notation without models with corners is relatively new,
  so this course's mathlib is not using it yet,
  and you will see the old notation when browsing mathlib
(2) for technical reasons, this only works 95% of the time

-/

/- END OF LECTURE -/

/- It also induces a map on the tangent bundle. -/

example (f : M → N) (_hf : MDifferentiable I J f) :
    TangentBundle I M → TangentBundle J N :=
  tangentMap I J f

example [IsManifold I 1 M] [IsManifold J 1 N] (f : M → N) (hf : ContMDiff I J ⊤ f) :
    ContMDiff I.tangent J.tangent ⊤ (tangentMap I J f) :=
  hf.contMDiff_tangentMap le_rfl


example [AddGroup N] [LieAddGroup J ⊤ N] {f g : M → N} {n : ℕ∞}
    (hf : ContMDiff I J n f) (hg : ContMDiff I J n g) :
    ContMDiff I J n (f + g) :=
  hf.add hg


-- Let `V` be a vector field on `M`: two completely equivalent phrasings.
variable {V : (x : M) → TangentSpace I x} {V : (x : M) → TangentSpace% x} [IsManifold I 1 M]
-- Suppose `V` is smooth.
  (hV : CMDiff ⊤ (T% V))

example {V W : (x : M) → TangentSpace% x} (hV : CMDiff ⊤ (T% V)) (hW : CMDiff ⊤ (T% W)) :
    CMDiff ⊤ (T% (V + W)) := by
  sorry

section

#check Diffeomorph

-- If `f` is a diffeomorphism, its differential is invertible.
-- (This follows easily from the chain rule.)
#check Diffeomorph.mfderivToContinuousLinearEquiv

-- Mathlib also knows about local diffeomorphisms: `f` is a local diffeomorphism
-- if for every point `p`, there exist open subsets `U` and `V` of `p` and `f p`
-- and a diffeomorphism `Φ : U ≃ V` which agrees with `f` on `U`.
#check IsLocalDiffeomorph

#check Diffeomorph.isLocalDiffeomorph

#check IsImmersion

-- mathlib also knows about smooth embeddings


/- Patrick Massot, Oliver Nash and Floris van Doorn have formalized
a result in differential geometry called *Gromov's h-principle*.

In particular, this allows you to abstractly define an eversion of a sphere. -/

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = 3)]

local notation "ℝ³" => E
local notation "𝕊²" => sphere (0 : ℝ³) 1

theorem sphere_eversion : ∃ f : ℝ → 𝕊² → ℝ³,
    (ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ³) ∞ (uncurry f)) ∧
    (f 0 = fun x : 𝕊² ↦ (x : ℝ³)) ∧
    (f 1 = fun x : 𝕊² ↦ -(x : ℝ³)) ∧
    ∀ t, IsImmersion (𝓡 2) 𝓘(ℝ, ℝ³) ⊤ (f t) :=
  sorry -- not yet in Mathlib

end



#check TangentBundle

#check VectorField.mlieBracket

#check VectorField.leibniz_identity_mlieBracket
