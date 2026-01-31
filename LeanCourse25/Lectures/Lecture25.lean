import LeanCourse25.Lectures.DifferentialGeometryNotation
import LeanCourse25.Lectures.SmoothEmbedding
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere

import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic

open ContDiff Manifold Function Metric Module Set TopologicalSpace
noncomputable section

/-
# Announcements

* Assignment 13 has many practice exercises, but does not require you to hand in anything.
  Work on your project instead.

* There will be a draft of the mock exam by the end of the week.

* There will be an "advanced Lean seminar" next semester
  (officially called Graduate Seminar in Applied Logic, S4A6).
  It will cover more advanced aspects, such as considerations how to design a large library,
  exploring the design of a particular area, learning how to review code or
  more advanced areas of Lean (e.g. the typeclass system, designing the simp set, ...).
  No knowledge beyond this class is necessary.
  Wishes for topics are welcome and may still be considered.
  The **initial meeting** will be on Thursday, February 12 at 10.15.

-/

/- # Last time: smooth manifolds

* topological and smooth manifolds, possibly with boundary and corners
* examples: normed spaces, open/closed intervals, spheres
* formalising them: charted spaces and models with corners
* interior and boundary points
* (continuous) differentiability of maps between manifolds

-/

/- Addendum: interior and boundary points -/

-- Let `M` and `N` be `C^n` manifolds.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}
  [IsManifold I n M] {x : M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] (J : ModelWithCorners 𝕜 F G)
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J n N]

example : extChartAt I x = I ∘ chartAt H x := by rfl

-- `x` is an interior point of `M` iff it lies in the interior of the range of its extended chart.
example : I.IsInteriorPoint x ↔ extChartAt I x x ∈ interior (range I) := by rfl

section

variable (n m : ℕ) (E' E'' : Type*) [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  [NormedAddCommGroup E''] [InnerProductSpace ℝ E'']

-- The product of two spheres 𝕊^n × 𝕊^m is a manifold.
variable [Fact (finrank ℝ E' = n + 1)] [Fact (finrank ℝ E'' = m + 1)] in
#synth IsManifold ((𝓡 n).prod (𝓡 m)) ω ((sphere (0 : E') 1) × (sphere (0 : E'') 1))

-- The 2-torus 𝕋² = 𝕊¹ × 𝕊¹ is a two-dimensional analytic manifold.
variable [Fact (finrank ℝ E' = 2)] in
#synth IsManifold ((𝓡 1).prod (𝓡 1)) ω ((sphere (0 : E') 1) × (sphere (0 : E') 1))

-- The disjoint union of 𝕊² with itself is also a two-dimensional analytic manifold.
variable [Fact (finrank ℝ E' = 3)] in
#synth IsManifold ((𝓡 2)) ω ((sphere (0 : E') 1) ⊕ (sphere (0 : E') 1))

end


/- # Differential geometry (continued)

## Tangent space & tangent bundle -/

-- A smooth manifold has a tangent space at each point.
-- Let's review the pen-and-paper definition first.


#check TangentSpace I x
#check TangentSpace% x



/-
In Lean, if `M` is a manifold modeled on `(H, E)`, the tangent space at a point `p`
is in fact just `E`. Relying heavily on this fact is *defeq abuse*: it's using a
definitional equality to an overly large extent, and creates brittle code. -/
example (p : M) : TangentSpace I p = E := rfl

/- We could the following, for example.
Don't do this at home; if you feel you need to, usually something has gone wrong somewhere else. -/

instance (p : M) : NormedAddCommGroup (TangentSpace I p) := inferInstanceAs (NormedAddCommGroup E)
example (p : M) : NormedSpace 𝕜 (TangentSpace I p) := inferInstanceAs (NormedSpace 𝕜 E)



















-- All tangent spaces fit together to give the tangent bundle of `M`.
#check TangentBundle I M


/- A differentiable map between manifolds induces a map on tangent spaces. -/

example (f : M → N) (_hf : MDifferentiable I J f) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace J (f x) :=
  mfderiv I J f x
-- Or, in cleaner notation
example (f : M → N) (_hf : MDiff f) (x : M) : TangentSpace% x →L[𝕜] TangentSpace% (f x) :=
  mfderiv% f x

/- It also induces a map on the tangent bundle. -/

example (f : M → N) (_hf : MDifferentiable I J f) :
    TangentBundle I M → TangentBundle J N :=
  tangentMap I J f

example [IsManifold I 1 M] [IsManifold J 1 N] (f : M → N) (hf : ContMDiff I J ⊤ f) :
    ContMDiff I.tangent J.tangent ⊤ (tangentMap I J f) :=
  hf.contMDiff_tangentMap le_rfl

example [IsManifold I 1 M] [IsManifold J 1 N] (f : M → N) (hf : CMDiff ⊤ f) :
    CMDiff ⊤ (tangentMap% f) :=
  hf.contMDiff_tangentMap le_rfl

example [AddGroup N] [LieAddGroup J ⊤ N] {f g : M → N} {n : ℕ∞}
    (hf : ContMDiff I J n f) (hg : ContMDiff I J n g) :
    ContMDiff I J n (f + g) :=
  hf.add hg

-- Let `V` be a vector field on `M`: two completely equivalent phrasings.
variable {V W : (x : M) → TangentSpace I x} {V : (x : M) → TangentSpace% x} [IsManifold I 1 M]
-- Suppose `V` is smooth. The notation `T%` converts `V` from a dependent function
-- to a function into the tangent bundle. We will explain this in more detail later.
  (hV : CMDiff ⊤ (T% V))

-- What happens if we comment the `IsManifold I 1 M`? Let's try to understand the error message.

-- The sum of two smooth vector fields is smooth.
-- We're using a more general lemma about smooth sections in a *smooth vector bundles*:
-- we will define these terms later today.
example {V W : (x : M) → TangentSpace% x} (hV : CMDiff ⊤ (T% V)) (hW : CMDiff ⊤ (T% W)) :
    CMDiff ⊤ (T% (V + W)) := by
  exact ContMDiff.add_section hV hW


-- One interesting operation on vector fields is the Lie bracket:
-- let us review the definition on paper first.

-- This is the Lean definition.
#check VectorField.mlieBracket

-- There is also a version within a set.
#check VectorField.mlieBracketWithin

open VectorField
-- The lie bracket is anti-symmetric and alternating.
example {s : Set M} : mlieBracketWithin I V W s = - mlieBracketWithin I W V s := by
  exact mlieBracketWithin_swap

example : mlieBracket I V V = 0 := mlieBracket_self

-- It also satisfies the Jacobi identity
#check VectorField.leibniz_identity_mlieBracket

-- The following result was formalised quite recently.
/-- **Product rule for Lie brackets**: given two vector fields `V` and `W` on `M` and a function
`f : M → 𝕜`, we have `[V, f • W] = (df V) • W + f • [V, W]`. -/
lemma mlieBracket_smul_right {f : M → 𝕜} (hf : MDiffAt f x) (hW : MDiffAt (T% W) x) :
    mlieBracket I V (f • W) x = (mfderiv% f x) (V x) • (W x) + (f x) • mlieBracket I V W x := by
  sorry

-- Fact: given two vector fields `X` and `Y`, their *local flows* commute iff `[X, Y] = 0`.






/- ## Smooth vector bundles -/

/- Given a continuous surjection `π : Z → M`.
A trivialization of `π` at `x : M` with fiber `F`
is a neighborhood `U` of `x` and a homeomorphism
`ϕ : π ⁻¹' U → U × F` that commutes with projections. -/
#check Trivialization

/- Fiber bundles have trivializations around each point in the base manifold -/
#check FiberBundle

/- In vector bundles the trivializations induce linear maps on the fibers.
Interestingly, for infinite-dimensional manifolds
you need an additional continuity condition. -/
#check VectorBundle

/- In smooth vector bundles the trivializations are smooth. -/
#check ContMDiffVectorBundle


-- If `M` is a `C^{n+1}`-manifold, the tangent bundle `TM` is a `C^n` vector bundle.
#check TangentBundle.contMDiffVectorBundle


open Bundle
/- Let `E₁` and `E₂` be smooth vector bundles over `M`. -/

variable
  (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  (E₁ : M → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x : M, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [ContMDiffVectorBundle n F₁ E₁ I]
variable
  (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  (E₂ : M → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x : M, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [ContMDiffVectorBundle n F₂ E₂ I]


/- A map `s : M → E₁` is called a *section* of a fibre bundle `π : E₁ → M` if `π ∘ s = id`,
i.e. `s x ∈ E₁ x` for all `x : M`. In Lean, this is simply a dependent function.
-/
variable {s : (x : M) → E₁ x}

-- Observe that a vector field on `M` is precisely a section of its tangent bundle `TM`.









/- If `E` is a smooth vector bundle, "`s` is a smooth section" is a sensible statement.
`ContMDiff` requires a non-dependent function as an argument.
The expression `T% s` takes the section `s` and converts it to a non-dependent section,
i.e. a map into the bundle's total space. (In other words, it denotes post-composition with
the inclusion of each bundle fiber into the total space.)
-/
variable {hs : CMDiff n (T% s)}

-- This is the equivalent expression without using `CMDiff` and `T%`.
variable {hs : ContMDiff I (I.prod 𝓘(𝕜, F₁)) n (fun x ↦ TotalSpace.mk' F₁ x (s x))}

-- There is also a type of bundled smooth sections, with special notation.
-- Note: "bundled" has nothing to do with vector or fiber bundles;
-- it refers to the fact that these combine a section with a proof of smoothenss.
#check ContMDiffSection
variable {t : Cₛ^n⟮I; F₁, E₁⟯}

-- The sum of smooth sections is a smooth section.
-- This was the statement we encountered about vector fields above.
example {s t : (x : M) → E₁ x} {hs : CMDiff n (T% s)} {ht : CMDiff n (T% t)} :
    CMDiff n (T% (s + t)) :=
  hs.add_section ht

-- We can also add bundled smooth sections:
-- under the hood, this is using the above example.
example {s' t' : Cₛ^n⟮I; F₁, E₁⟯} : Cₛ^n⟮I; F₁, E₁⟯ :=
  s' + t'
example {s' t' : Cₛ^n⟮I; F₁, E₁⟯} : (s' + t') x = s' x + t' x := rfl

/- The product of two bundles is a smooth vector bundle. -/

#synth ContMDiffVectorBundle n (F₁ × F₂) (E₁ ×ᵇ E₂) I


/- We can take construct the bundle of continuous linear maps between bundles. -/

variable [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, IsTopologicalAddGroup (E₂ x)]
  [∀ x, ContinuousSMul 𝕜 (E₂ x)]

#synth ContMDiffVectorBundle n (F₁ →L[𝕜] F₂) (fun (b : M) ↦ E₁ b →L[𝕜] E₂ b) I

/- We can pull back vector bundles. -/

variable (f : C^n⟮J, N; I, M⟯)

#synth ContMDiffVectorBundle n F₁ ((f : N → M) *ᵖ E₁) J






section

-- Let us explore some special kinds of maps.

#check Diffeomorph

-- If `f` is a diffeomorphism, its differential is invertible.
-- (This follows easily from the chain rule.)
#check Diffeomorph.mfderivToContinuousLinearEquiv

-- Mathlib also knows about local diffeomorphisms: `f` is a local diffeomorphism
-- if for every point `p`, there exist open subsets `U` and `V` of `p` and `f p`
-- and a diffeomorphism `Φ : U ≃ V` which agrees with `f` on `U`.
#check IsLocalDiffeomorph

#check Diffeomorph.isLocalDiffeomorph

-- If `M` is finite-dimensional, `f` is an immersion if each differential
-- `mfderiv% f p` is injective. Equivalently, each `p : M` has suitable
-- charts in which `f` looks like a map `u ↦ (u, 0)`.
-- In infinite dimensions, these definitions are no longer equivalent,
-- the second one is the correct condition (and implies the first one).
#check IsImmersion

-- mathlib also knows about smooth embeddings: smooth embeddings are smooth immersions automatically
#check IsSmoothEmbedding

example {f : M → N} (hf : IsSmoothEmbedding I J n f) : IsImmersion I J n f := by
  exact hf.isImmersion


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

-- Riemannian metrics
#check IsRiemannianManifold


/- Coming soon:
* connections (covariant derivatives)
* the Levi-Civita connection
* curvature
* geodesics
* the exponential map

-/
