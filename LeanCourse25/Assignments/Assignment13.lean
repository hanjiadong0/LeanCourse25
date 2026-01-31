import LeanCourse25.Lectures.DifferentialGeometryNotation
import LeanCourse25.Lectures.SmoothEmbedding
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Algebra.Group.InjSurj

open ContDiff Manifold Function Metric Module Set TopologicalSpace
noncomputable section

/-! # Exercises to practice -/

section

/-
Partial homeomorphisms are globally defined maps with a globally defined "inverse", but the only
relevant set is the *source*, which should be mapped homeomorphically to the *target*.

Define a partial homeomorphism from `ℝ` to `ℝ` which is just `x ↦ -x`, but on `(-1, 1)`. In
Lean, the interval `(-1, 1)` is denoted by `Ioo (-1 : ℝ) 1` (where `o` stands for _open_). -/

def myFirstLocalHomeo : OpenPartialHomeomorph ℝ ℝ where
  toFun := fun x ↦ -x
  invFun := fun x ↦ -x
  source := Ioo (-1) 1
  target := sorry
  map_source' := by
    sorry
  map_target' := by
    sorry
  left_inv' := by
    sorry
  right_inv' := by
    sorry
  open_source := sorry
  open_target := sorry
  continuousOn_toFun := sorry
  continuousOn_invFun := sorry

end

section

-- Let's prove that the real numbers are a smooth manifold,
-- with just one chart. This is the chart we want to define.
def identityMap : OpenPartialHomeomorph ℝ ℝ :=
  (Homeomorph.refl ℝ).toOpenPartialHomeomorph

-- Here's the atlas on one chart.
def foo : ChartedSpace ℝ ℝ where
  atlas := {identityMap}
  chartAt := sorry
  mem_chart_source := sorry
  chart_mem_atlas := sorry

-- Prove that makes ℝ into a smooth manifold.
attribute [local instance] foo in -- makes the following lemma use the atlas above
instance : IsManifold 𝓘(ℝ) ⊤ ℝ where
  compatible := by sorry

end

section OneChart

-- Let us prove the following exercise more generally: a charted space with only one chart
-- is automatically a smooth manifold.

variable {𝕜 M H E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace M] [TopologicalSpace H] [ChartedSpace H M] {I : ModelWithCorners 𝕜 E H}

/- If the atlas of `M` has only a single chart, `M` is automatically a smooth manifold. -/
example (h : Subsingleton (atlas H M)) : IsManifold I ⊤ M where
  compatible := by sorry

end OneChart

section

-- Euclidean space `ℝ^n` is a boundaryless manifold, by construction.
variable {n : ℕ} in
#synth IsManifold (𝓡 n) ⊤ (EuclideanSpace ℝ (Fin n))

example {n : ℕ} : (𝓡 n).Boundaryless :=
  modelWithCornersSelf_boundaryless ℝ (EuclideanSpace ℝ (Fin n))

-- In this exercise, you will view it as a manifold with model 𝓡∂ n,
-- and prove it is still boundaryless.
-- To do so, you construct charts whose range is contained in the interior of the range of 𝓡∂ n.

variable {n : ℕ} [NeZero n]

/- The point (2, 0, ..., 0) in Euclidean half-space. -/
def two : EuclideanHalfSpace n := ⟨fun i ↦ Finsupp.single 0 (2 : ℝ) i, by simp⟩

instance : MetricSpace (EuclideanHalfSpace n) := by
  unfold EuclideanHalfSpace; exact Subtype.metricSpace

-- The following construction will be helpful: fill in all the sorries.
def prechartAt (z₀ : EuclideanSpace ℝ (Fin n)) :
    PartialEquiv (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) where
  toFun z :=
    open scoped Classical in
    -- You may need to tweak this definition by shifting with another constant.
    if z ∈ ball z₀ 1 then ⟨z - z₀, sorry⟩ else two
  invFun z := z.val + z₀
  source := ball z₀ 1
  target := ball two 1
  map_source' := sorry
  map_target' := sorry
  left_inv' := sorry
  right_inv' := sorry

/- These will be the charts for your construction. -/
def mychartAt (z₀ : EuclideanSpace ℝ (Fin n)) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) where
  toPartialEquiv := prechartAt z₀
  open_source := sorry
  open_target := sorry
  continuousOn_toFun := sorry
  continuousOn_invFun := sorry

instance : ChartedSpace (EuclideanHalfSpace n) (EuclideanSpace ℝ (Fin n)) where
  atlas := sorry
  chartAt p := sorry
  mem_chart_source := sorry
  chart_mem_atlas := sorry

instance : IsManifold (𝓡∂ n) ⊤ (EuclideanSpace ℝ (Fin n)) where
  compatible := by sorry

example : BoundarylessManifold (𝓡∂ n) (EuclideanSpace ℝ (Fin n)) := by
  sorry

end

section Interval

/-!
### Smooth functions on `[0, 1]`

We will prove two simple lemmas about smooth maps on `[0, 1]`.
Mathlib doesn't have all the lemmas you might imagine
(in particular, don't expect any lemma about closed submanifolds),
but has most lemmas you will need here.
-/

open unitInterval

def g : I → ℝ := Subtype.val

/- Smoothness results for `EuclideanSpace` are expressed for general `L^p` spaces
(as `EuclideanSpace` has the `L^2` norm), in: -/
#check contDiff_piLp_apply 2
#check contDiff_piLp 2

-- this is the charted space structure on `I`
#check instIccChartedSpace

/- The first half has been proven by now: which mathlib lemma is it?

If you like a challenge, you can use `contMDiff_iff` and unfold the definition of
`modelWithCornersEuclideanHalfSpace` (and some other functions)
to give a proof yourself. -/
example : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ g := by
  sorry
  done

open Topology

lemma contMDiffOn_of_contDiffOn {f : ℝ → I} {s : Set ℝ} (h : ContDiffOn ℝ ∞ (fun x ↦ (f x : ℝ)) s) :
    ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) ∞ f s := by
  sorry
  done

end Interval

section VectorField

-- Let us define the pullback of a vector field.

-- Let `M` and `N` be `C^n` manifolds.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}
  [IsManifold I ⊤ M] {x : M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] (J : ModelWithCorners 𝕜 F G)
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J n N]

-- Suppose `V` is a vector field on `M`:
-- the **pullforward** of `V` under a diffeomorphism `f : M → N` is a vector field on `N`.
def pullback (V : (x : M) → TangentSpace% x) (f : Diffeomorph I J M N n) :
    (y : N) → TangentSpace% y :=
  fun y ↦  mfderiv% f (f.symm y) (V (f.symm y))

omit [IsManifold I ω M] in
lemma pullback_id (V : (x : M) → TangentSpace% x) : pullback I I V (.refl I M n) = V := by
  sorry

lemma pullback_comp (V : (x : M) → TangentSpace% x) {f g : Diffeomorph I I M M n} (hn : 1 ≤ n) :
    pullback I I V (g.trans f) = pullback I I (pullback I I V g) f := by
  sorry

end VectorField

section LieBracket

section prerequisites

-- Let `M` and `N` be `C^n` manifolds.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞} {x : M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] (J : ModelWithCorners 𝕜 F G)
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

@[simp]
lemma tangentMap_fst (f : M → N) (X : TangentSpace% x) :
  (tangentMap% f X).1 = f x := by rfl

@[simp]
lemma tangentMap_snd (f : M → N) (X : TangentSpace% x) :
  (tangentMap% f X).2 = (mfderiv% f x) X := by rfl

-- from https://github.com/leanprover-community/mathlib4/pull/26221
lemma mfderiv_const_smul (s : M → F) {x : M} (a : 𝕜) (v : TangentSpace I x) :
    mfderiv I 𝓘(𝕜, F) (a • s) x v = a • mfderiv I 𝓘(𝕜, F) s x v := by
  by_cases hs : MDiffAt s x
  · have hs' := hs.const_smul a
    suffices
      (fderivWithin 𝕜 ((a • s) ∘ (chartAt H x).symm ∘ I.symm) (range I) (I ((chartAt H x) x))) v =
       a • (fderivWithin 𝕜 (s ∘ (chartAt H x).symm ∘ I.symm) (range I)
       (I ((chartAt H x) x))) v by simpa [mfderiv, hs, hs']
    change fderivWithin 𝕜 (a • (s ∘ ↑(chartAt H x).symm ∘ ↑I.symm)) _ _ _ = _
    rw [fderivWithin_const_smul_field _ I.uniqueDiffWithinAt_image ]
    rfl
  · by_cases ha : a = 0
    · have : a • s = 0 := by ext; simp [ha]
      rw [this, ha]
      change (mfderiv I 𝓘(𝕜, F) (fun _ ↦ 0) x) v = _
      simp
    have hs' : ¬ MDifferentiableAt I 𝓘(𝕜, F) (a • s) x :=
      fun h ↦ hs (by simpa [ha] using h.const_smul a⁻¹)
    rw [mfderiv_zero_of_not_mdifferentiableAt hs, mfderiv_zero_of_not_mdifferentiableAt hs']
    simp
    rfl

end prerequisites

section ContMDiffMap

-- Let M be a real smooth manifold.
-- Note that most of this section could be generalised to a other target manifolds,
-- not just the real numbers.
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

theorem coe_injective' : Injective ((↑) : C^∞⟮I, M; ℝ⟯ → M → ℝ) :=
  ContMDiffMap.coe_injective

instance instAdd : Add C^∞⟮I, M; ℝ⟯ :=
  ⟨fun s t ↦ ⟨s + t, s.contMDiff.add t.contMDiff⟩⟩

@[simp]
theorem coe_add (s t : C^∞⟮I, M; ℝ⟯) : ⇑(s + t) = ⇑s + t :=
  rfl

instance instSub : Sub C^∞⟮I, M; ℝ⟯ :=
  ⟨fun s t ↦ ⟨s - t, s.contMDiff.sub t.contMDiff⟩⟩

@[simp]
theorem coe_sub (s t : C^∞⟮I, M; ℝ⟯) : ⇑(s - t) = s - t :=
  rfl

instance instZero : Zero C^∞⟮I, M; ℝ⟯ := ⟨0, contMDiff_zero⟩

@[simp]
theorem coe_zero : ⇑(0 : C^∞⟮I, M; ℝ⟯) = 0 :=
  rfl

instance instNeg : Neg C^∞⟮I, M; ℝ⟯ :=
  ⟨fun s ↦ ⟨-s, s.contMDiff.neg⟩⟩

@[simp]
theorem coe_neg (s : C^∞⟮I, M; ℝ⟯) : ⇑(-s : C^∞⟮I, M; ℝ⟯) = -s :=
  rfl

instance instNSMul : SMul ℕ C^∞⟮I, M; ℝ⟯ := ⟨nsmulRec⟩

@[simp]
theorem coe_nsmul (s : C^∞⟮I, M; ℝ⟯) (k : ℕ) : ⇑(k • s : C^∞⟮I, M; ℝ⟯) = k • ⇑s := by
  induction k with
  | zero => simp_rw [zero_smul]; rfl
  | succ k ih => simp_rw [succ_nsmul, ← ih]; rfl

instance instZSMul : SMul ℤ C^∞⟮I, M; ℝ⟯ :=
  ⟨zsmulRec⟩

@[simp]
theorem coe_zsmul (s : C^∞⟮I, M; ℝ⟯) (z : ℤ) : ⇑(z • s : C^∞⟮I, M; ℝ⟯) = z • ⇑s := by
  rcases z with n | n
  · refine (coe_nsmul s n).trans ?_
    simp only [Int.ofNat_eq_coe, natCast_zsmul]
  · refine (congr_arg Neg.neg (coe_nsmul s (n + 1))).trans ?_
    simp only [negSucc_zsmul]

instance instAddCommGroup : AddCommGroup C^∞⟮I, M; ℝ⟯ :=
  coe_injective'.addCommGroup  _ coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

instance instSMul : SMul ℝ C^∞⟮I, M; ℝ⟯ :=
  ⟨fun c s ↦ ⟨c • ⇑s, contMDiff_const.smul s.contMDiff⟩⟩

@[simp]
theorem coe_smul (r : ℝ) (s : C^∞⟮I, M; ℝ⟯) : ⇑(r • s : C^∞⟮I, M; ℝ⟯) = r • ⇑s :=
  rfl

instance instOne : One C^∞⟮I, M; ℝ⟯ := ⟨1, contMDiff_const⟩

@[simp]
theorem coe_one : ⇑(1 : C^∞⟮I, M; ℝ⟯) = 1 := rfl

@[simp]
lemma ContMDiffMap.one_smul {s : C^∞⟮I, M; ℝ⟯} : (1 : ℝ) • s = s := by
  ext; simp

@[simp]
lemma ContMDiffMap.zero_smul {s : C^∞⟮I, M; ℝ⟯} : (0 : ℝ) • s = 0 := by
  ext; simp

@[simp]
lemma ContMDiffMap.smul_zero {c : ℝ} : c • (0 : C^∞⟮I, M; ℝ⟯) = 0 := by ext; simp

instance : Module ℝ C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ where
  one_smul f := f.one_smul
  zero_smul f := f.zero_smul
  smul_zero c := by simp
  mul_smul a b f := by ext; simp; ring
  add_smul c f g := by ext; simp; ring
  smul_add c f g := by ext; simp; ring

end ContMDiffMap

-- Let M be a real smooth manifold.
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {p : M}

-- Let us formalise the definition of Lie derivative that we saw in class.
-- Mathlib's definition of Lie bracket is different, but this is a nice exercise anyway.

def LieDerivativeₚ (f : M → ℝ) (X : TangentSpace I p) : ℝ :=
  sorry

-- XXX: can we make this an explicit definition, over any normed field?
def proj : TangentBundle 𝓘(ℝ, ℝ) ℝ → ℝ := fun x ↦ x.2

lemma contMDiff_proj : CMDiff ∞ proj := by
  unfold proj
  exact contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)

/-- For any vector field `X`,
the Lie derivative defines a function `𝓛_Xf : M → ℝ` via `p ↦ df_p(X p)`. -/
-- Note: there is another, equivalent, definition which might make `contMDiff_lieDerivative` below
-- easier. See the comment below.
def LieDerivative (X : (x : M) → TangentSpace I x) (f : M → ℝ) : M → ℝ :=
  sorry

example (X : (x : M) → TangentSpace I x) (f : M → ℝ) :
    LieDerivative X f p = LieDerivativeₚ f (X p) := by
  sorry

/- If `X` is smooth, then `LieDerivative X f` is also smooth.

This exercise is more challenging.
In principle, you can prove this in coordinates: choose a chart on `U ∋ p`,
consider the induced basis of `TangentSpace I y` (for `y ∈ U`)
and compute everything in these coordinates. You will encounter a number of missing mathlib lemmas.

A more clever approach is to define the Lie derivative as a composition of `tangentMap`
and `T% X` (which maps to the tangent bundle anyway). The map `proj` above may be useful for this.
-/
lemma contMDiff_lieDerivative {X : (x : M) → TangentSpace I x} (hX : CMDiff ∞ (T% X))
    {f : M → ℝ} (hf : CMDiff ∞ f) :
    CMDiff ∞ (LieDerivative X f) := by
  sorry

-- Thus, a smooth vector field defines an operator `𝓛_X: C^∞(M) → C^∞(M)`.
-- `C^∞⟮I, M; 𝓘(ℝ), ℝ⟯` is the type of bundled smooth maps from M to ℝ.
def LieDerivativeOp {X : (x : M) → TangentSpace I x} (hX : CMDiff ∞ (T% X)) :
    C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ :=
  sorry

-- This operator is linear.
def LieDerivativeLM {X : (x : M) → TangentSpace I x} (hX : CMDiff ∞ (T% X)) :
    C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ where
  toFun := LieDerivativeOp hX
  map_add' f g := by
    sorry
  map_smul' c f := by
    -- Note: this might be slightly harder. Talk to us if you get stuck!
    sorry

end LieBracket


/-! # Exercises to hand in -/

/- There are **no graded exercises** this week: work on your formalisation projects.
If your project involves differential geometry, doing the practice exercises at some
point is highly recommended. -/
