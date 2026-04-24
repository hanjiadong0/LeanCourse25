import LeanCourse25.Projects.IwasawaPipeline

open scoped BigOperators Matrix
open Finset
noncomputable section

namespace MatrixTactics

namespace Iwasawa

variable {m : Nat}

/-- Package explicit witnesses `(z, k, d)` into `IwasawaFactorization`. -/
theorem exists_factorization_of_witnesses
    (g : GLn m) (z : Hn.H m) (k : O m) (d : RUnits)
    (h : z.toMat * (k : Mat m) * centerMat (m := m) d = (g : Mat m)) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) := by
  refine ⟨⟨z, k, d⟩, ?_⟩
  simpa [IwasawaFactorization.toMat] using h

/-- Concrete existence from a raw matrix decomposition lemma. -/
theorem exists_factorization_of_raw
    (g : GLn m)
    (hraw : ∃ z : Hn.H m, ∃ k : O m, ∃ d : RUnits,
      z.toMat * (k : Mat m) * centerMat (m := m) d = (g : Mat m)) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) := by
  rcases hraw with ⟨z, k, d, h⟩
  exact exists_factorization_of_witnesses (m := m) g z k d h

/-- Construction helper for the triangular-solver/Gram pipeline:
package a residual orthogonal matrix and scalar into a factorization. -/
theorem exists_factorization_of_solver_gram
    (g : GLn m) (z : Hn.H m) (Q : Mat m)
    (hQ : IsOrthogonal Q) (d : RUnits)
    (h : z.toMat * Q * centerMat (m := m) d = (g : Mat m)) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) := by
  exact exists_factorization_of_witnesses (m := m) g z ⟨Q, hQ⟩ d h

/-- Goldfeld core input matrix `A = g * gᵀ` is nonsingular. -/
theorem gram_nonsingular (g : GLn m) :
    Matrix.det ((g : Mat m) * (g : Mat m)ᵀ) ≠ 0 := by
  have hgdet : Matrix.det (g : Mat m) ≠ 0 := by
    intro hzero
    have h := g.val_inv
    apply_fun Matrix.det at h
    simp [Matrix.det_mul, hzero] at h
  rw [Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero hgdet hgdet

/-- Matrix-level unit form of `gram_nonsingular`. -/
theorem gram_isUnit (g : GLn m) :
    IsUnit ((g : Mat m) * (g : Mat m)ᵀ) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr (gram_nonsingular (m := m) g)

/-- An orthogonal upper-unipotent real matrix is the identity.

Each column-norm `∑_k Q_{kj}² = 1` (from `QᵀQ = I`);
upper-triangularity kills `k > j`, unipotency gives `Q_{jj} = 1`,
so every remaining `Q_{kj}²` vanishes by non-negativity over `ℝ`. -/
lemma orthogonal_unipotent_eq_one
    (Q : Mat m)
    (hQ : IsOrthogonal Q)
    (hU : IsUpperTriangular Q)
    (hD : ∀ i : Fin m, Q i i = 1) :
    Q = 1 := by
  ext i j
  simp only [Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp [hD]
  · rw [if_neg hij]
    -- Below diagonal: immediate from upper-triangularity
    by_cases hlt : j < i
    · exact hU hlt
    · -- Above diagonal (i < j): column-norm argument
      -- Column j has norm 1: ∑_k Q_{kj}² = 1
      have hcol : ∑ k : Fin m, Q k j * Q k j = 1 := by
        have h : (Qᵀ * Q) j j = 1 := by rw [hQ]; simp
        simp only [Matrix.mul_apply,
          Matrix.transpose_apply] at h
        exact h
      -- Diagonal entry: Q_{jj}² = 1
      have hdiag : Q j j * Q j j = 1 := by
        rw [hD j]; ring
      -- Split: Q_{jj}² + ∑_{k≠j} Q_{kj}² = 1
      have hsplit := Finset.add_sum_erase Finset.univ
        (fun k => Q k j * Q k j) (Finset.mem_univ j)
      dsimp only at hsplit
      -- Off-diagonal sum vanishes
      have hrest : (∑ k ∈ Finset.univ.erase j,
          Q k j * Q k j) = 0 := by linarith
      -- Q_{ij}² ≤ ∑_{k≠j} Q_{kj}² = 0 and ≥ 0
      have hmem : i ∈ Finset.univ.erase j :=
        Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
      have hle := Finset.single_le_sum
        (fun k _ => mul_self_nonneg (Q k j)) hmem
      exact mul_self_eq_zero.mp
        (by linarith [mul_self_nonneg (Q i j)])

/-- `scalarMat c = c • 1`. -/
private lemma scalarMat_eq_smul (c : ℝ) :
    scalarMat c = c • (1 : Mat m) := by
  ext i j
  simp only [scalarMat, diag, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

/-- `Q * Qᵀ = 1` from `Qᵀ * Q = 1` (square, finite). -/
private lemma orth_QQT (Q : Mat m)
    (hQ : IsOrthogonal Q) :
    Q * Qᵀ = 1 :=
  Matrix.mul_eq_one_comm.mp hQ

/-- Entry of `(x * diag D * xᵀ)`. -/
private lemma xDxT_entry (x : Mat m) (D : Fin m → ℝ)
    (i j : Fin m) :
    (x * diag D * xᵀ) i j =
      ∑ k : Fin m, x i k * D k * x j k := by
  rw [show x * diag D * xᵀ = (x * diag D) * xᵀ
    from rfl]
  rw [Matrix.mul_apply]
  congr 1; ext k
  rw [mul_diag_entry, Matrix.transpose_apply]

/-- The Gram matrix `fac.toMat * fac.toMatᵀ = d² • (z * zᵀ)`.
This eliminates the orthogonal factor `Q` from the picture. -/
private lemma fac_gram (fac : IwasawaFactorization m) :
    fac.toMat * fac.toMatᵀ =
      (fac.d : ℝ) ^ 2 • (fac.z.toMat * fac.z.toMatᵀ) := by
  have htoMat : fac.toMat =
      (fac.d : ℝ) • (fac.z.toMat * fac.k.Q) := by
    unfold IwasawaFactorization.toMat centerMat
    rw [scalarMat_eq_smul, mul_smul_comm, mul_one]
  rw [htoMat, Matrix.transpose_smul, smul_mul_assoc,
    mul_smul_comm, smul_smul, ← sq]
  congr 1
  rw [Matrix.transpose_mul, mul_assoc,
    ← mul_assoc fac.k.Q, orth_QQT _ fac.k.orth, one_mul]

/-- Concrete Gram identity for an Iwasawa factorization:
the orthogonal factor disappears in `g * gᵀ`. -/
theorem gram_of_factorization (fac : IwasawaFactorization m) :
    fac.toMat * fac.toMatᵀ =
      (fac.d : ℝ) ^ 2 • (fac.z.toMat * fac.z.toMatᵀ) :=
  fac_gram fac

/-- For upper-unipotent `x` with positive diagonal `y`,
the sum `∑_k x_{ik} y_k² x_{jk}` restricted to `k ≥ j`
equals `x_{ij} y_j² + ∑_{k > j} x_{ik} y_k² x_{jk}`.
Upper triangularity kills `k < j`. -/
private lemma gram_sum_split (x : Mat m) (D : Fin m → ℝ)
    (hU : IsUpperTriangular x)
    (hD1 : ∀ i, x i i = 1)
    (i j : Fin m) (hij : i ≤ j) :
    ∑ k : Fin m, x i k * D k * x j k =
      x i j * D j +
        ∑ k ∈ Finset.univ.filter (· > j),
          x i k * D k * x j k := by
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun k => x i k * D k * x j k) (Finset.mem_univ j)
  dsimp only at hsplit
  rw [← hsplit, hD1 j, mul_one]
  -- ∑_{erase j} f = ∑_{filter >j} f: extra terms (k < j) vanish
  congr 1
  refine (Finset.sum_subset ?_ ?_).symm
  · intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk
    exact mem_erase.mpr ⟨ne_of_gt hk, mem_univ k⟩
  · intro k hk_in hk_not
    simp only [mem_erase, mem_univ, and_true, mem_filter,
      true_and, not_lt] at hk_in hk_not
    rw [hU (lt_of_le_of_ne hk_not hk_in)]; ring

/-- LDLᵀ uniqueness: from `x₁ D₁ x₁ᵀ = x₂ D₂ x₂ᵀ` where
each `xᵢ` is upper-unipotent and `Dᵢ` is positive, we get
`x₁ = x₂` and `D₁ = D₂`. The proof processes columns from
right to left, using the sum-of-squares structure. -/
private lemma ldl_unique
    (x₁ x₂ : Mat m) (D₁ D₂ : Fin m → ℝ)
    (hU₁ : IsUpperTriangular x₁)
    (hU₂ : IsUpperTriangular x₂)
    (h1₁ : ∀ i, x₁ i i = 1)
    (h1₂ : ∀ i, x₂ i i = 1)
    (hD₁ : ∀ i, 0 < D₁ i)
    (hD₂ : ∀ i, 0 < D₂ i)
    (heq : ∀ i j : Fin m,
      ∑ k : Fin m, x₁ i k * D₁ k * x₁ j k =
      ∑ k : Fin m, x₂ i k * D₂ k * x₂ j k) :
    x₁ = x₂ ∧ D₁ = D₂ := by
  -- Column-by-column claim: D and x match at each column j
  -- Proved by reverse induction (right to left)
  suffices col : ∀ j : Fin m, D₁ j = D₂ j ∧
      ∀ i : Fin m, i < j → x₁ i j = x₂ i j by
    constructor
    · ext i j
      by_cases hij : i = j
      · subst hij; rw [h1₁, h1₂]
      · by_cases hlt : j < i
        · rw [hU₁ hlt, hU₂ hlt]
        · exact (col j).2 i (by omega)
    · ext j; exact (col j).1
  -- Induction on (m - 1 - j.val), processing right to left
  suffices ∀ n, ∀ j : Fin m, m - 1 - j.val ≤ n →
      D₁ j = D₂ j ∧ ∀ i : Fin m, i < j → x₁ i j = x₂ i j by
    intro j; exact this _ j le_rfl
  intro n; induction n with
  | zero =>
    intro j hj
    -- j is the rightmost column: all k > j are impossible
    have hempty : ∀ f : Fin m → ℝ,
        ∑ k ∈ univ.filter (· > j), f k = 0 := by
      intro f; apply sum_eq_zero; intro k hk
      simp only [mem_filter, mem_univ, true_and] at hk
      exact absurd (show k.val > j.val from hk) (by omega)
    have hDj : D₁ j = D₂ j := by
      have h := heq j j
      rw [gram_sum_split x₁ D₁ hU₁ h1₁ j j le_rfl,
          gram_sum_split x₂ D₂ hU₂ h1₂ j j le_rfl] at h
      rw [hempty (fun k => x₁ j k * D₁ k * x₁ j k),
          hempty (fun k => x₂ j k * D₂ k * x₂ j k),
          h1₁ j, h1₂ j] at h
      linarith
    refine ⟨hDj, fun i hi => ?_⟩
    have h := heq i j
    rw [gram_sum_split x₁ D₁ hU₁ h1₁ i j (le_of_lt hi),
        gram_sum_split x₂ D₂ hU₂ h1₂ i j (le_of_lt hi)] at h
    have e1 := hempty (fun k => x₁ i k * D₁ k * x₁ j k)
    have e2 := hempty (fun k => x₂ i k * D₂ k * x₂ j k)
    have h : x₁ i j * D₁ j = x₂ i j * D₂ j := by linarith
    rw [hDj] at h
    exact mul_right_cancel₀ (ne_of_gt (hD₂ j)) h
  | succ n ih =>
    intro j hj
    -- IH gives results for all columns k > j
    have ih_col : ∀ k : Fin m, j < k →
        D₁ k = D₂ k ∧ ∀ i, i < k → x₁ i k = x₂ i k :=
      fun k hk => ih k (by omega)
    -- Full column equality for k > j
    have ih_full : ∀ k : Fin m, j < k →
        ∀ i, x₁ i k = x₂ i k := by
      intro k hk i
      by_cases hik : i = k; · subst hik; rw [h1₁, h1₂]
      by_cases hilt : k < i; · rw [hU₁ hilt, hU₂ hilt]
      · exact (ih_col k hk).2 i (by omega)
    -- Tail sums match term by term
    have htail : ∀ i, ∑ k ∈ univ.filter (· > j),
        x₁ i k * D₁ k * x₁ j k =
        ∑ k ∈ univ.filter (· > j),
          x₂ i k * D₂ k * x₂ j k := by
      intro i; apply sum_congr rfl; intro k hk
      simp only [mem_filter, mem_univ, true_and] at hk
      rw [ih_full k hk i, (ih_col k hk).1, ih_full k hk j]
    -- D₁ j = D₂ j from the (j,j) Gram entry
    have hDj : D₁ j = D₂ j := by
      have h := heq j j
      rw [gram_sum_split x₁ D₁ hU₁ h1₁ j j le_rfl,
          gram_sum_split x₂ D₂ hU₂ h1₂ j j le_rfl] at h
      rw [h1₁ j, h1₂ j, one_mul, one_mul] at h
      linarith [htail j]
    refine ⟨hDj, fun i hi => ?_⟩
    have h := heq i j
    rw [gram_sum_split x₁ D₁ hU₁ h1₁ i j (le_of_lt hi),
        gram_sum_split x₂ D₂ hU₂ h1₂ i j (le_of_lt hi)] at h
    rw [hDj] at h
    exact mul_right_cancel₀ (ne_of_gt (hD₂ j))
      (by linarith [htail i])

/-- Uniqueness of the `z`-factor: if two Iwasawa factorisations
have the same product matrix, their `z` components agree.

Strategy: form the Gram matrix `g * gᵀ`, which eliminates the
orthogonal factor.  Then `z₁ * z₁ᵀ = z₂ * z₂ᵀ` (LDL),
and LDL uniqueness gives `z₁ = z₂`. -/
theorem unique_z_of_two_factorizations
    (g : GLn m) (fac1 fac2 : IwasawaFactorization m)
    (h1 : fac1.toMat = (g : Mat m))
    (h2 : fac2.toMat = (g : Mat m)) :
    fac1.z = fac2.z := by
  have heq : fac1.toMat = fac2.toMat := h1.trans h2.symm
  have hgram : fac1.toMat * fac1.toMatᵀ =
      fac2.toMat * fac2.toMatᵀ := by rw [heq]
  rw [fac_gram, fac_gram] at hgram
  -- Expand (d² • (z * zᵀ))_{ij} as ∑ k, x_{ik} * (d² * y_k²) * x_{jk}
  have expand : ∀ (z : Hn.H m) (d : RUnits)
      (i j : Fin m),
      ((d : ℝ) ^ 2 • (z.toMat * z.toMatᵀ)) i j =
      ∑ k, z.x.x i k * ((d : ℝ) ^ 2 * (z.y.d k) ^ 2) *
        z.x.x j k := by
    intro z d i j
    -- First establish that z.toMat entries factor
    have hentry : ∀ a b : Fin m,
        z.toMat a b = z.x.x a b * z.y.d b := by
      intro a b
      show ((z.x : Mat m) * z.y.toMat) a b = _
      exact mul_diag_entry z.x.x z.y.d a b
    simp only [Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.transpose_apply, hentry,
      Finset.mul_sum]
    congr 1; ext k; ring
  -- Entry-level Gram equality with D_k = d² * y_k²
  have hentry : ∀ i j : Fin m,
      ∑ k, fac1.z.x.x i k *
        ((fac1.d : ℝ) ^ 2 * (fac1.z.y.d k) ^ 2) *
        fac1.z.x.x j k =
      ∑ k, fac2.z.x.x i k *
        ((fac2.d : ℝ) ^ 2 * (fac2.z.y.d k) ^ 2) *
        fac2.z.x.x j k := by
    intro i j
    rw [← expand, ← expand]
    exact congr_fun (congr_fun hgram i) j
  -- Apply LDL uniqueness
  have ⟨hx_eq, hD_eq⟩ := ldl_unique
    fac1.z.x.x fac2.z.x.x
    (fun k => (fac1.d : ℝ) ^ 2 * (fac1.z.y.d k) ^ 2)
    (fun k => (fac2.d : ℝ) ^ 2 * (fac2.z.y.d k) ^ 2)
    fac1.z.x.upper fac2.z.x.upper
    fac1.z.x.diag_one fac2.z.x.diag_one
    (fun i => by
      have := Units.ne_zero fac1.d
      have := fac1.z.y.pos_all i; positivity)
    (fun i => by
      have := Units.ne_zero fac2.d
      have := fac2.z.y.pos_all i; positivity)
    hentry
  -- d₁² = d₂² from D equality at last index (where y = 1)
  have hd2 : (fac1.d : ℝ) ^ 2 = (fac2.d : ℝ) ^ 2 := by
    have h := congr_fun hD_eq
      ⟨m - 1, Nat.sub_lt fac1.z.y.hm Nat.one_pos⟩
    simp only at h
    have h1 := fac1.z.y.last_one
    have h2 := fac2.z.y.last_one
    simp only [h1, h2] at h; linarith
  -- y₁ = y₂ from D₁ = D₂ and d₁² = d₂²
  have hy_eq : fac1.z.y.d = fac2.z.y.d := by
    ext k
    have hk := congr_fun hD_eq k; simp only at hk
    -- y₁(k)² = y₂(k)² by cancelling d²
    have hd_pos : (fac1.d : ℝ) ^ 2 > 0 := by
      have := Units.ne_zero fac1.d; positivity
    have hy2 : (fac1.z.y.d k) ^ 2 =
        (fac2.z.y.d k) ^ 2 :=
      mul_left_cancel₀ (ne_of_gt hd_pos)
        (by nlinarith)
    -- y₁(k) = y₂(k) since both positive
    have hsub : (fac1.z.y.d k - fac2.z.y.d k) *
        (fac1.z.y.d k + fac2.z.y.d k) = 0 := by
      nlinarith
    have hsum : 0 < fac1.z.y.d k + fac2.z.y.d k :=
      by linarith [fac1.z.y.pos_all k, fac2.z.y.pos_all k]
    rcases mul_eq_zero.mp hsub with h | h
    · linarith
    · exact absurd h (ne_of_gt hsum)
  -- z₁.toMat = z₂.toMat from x₁ = x₂ and y₁ = y₂
  apply Hn.H_toMat_injective
  simp only [Hn.H.toMat, Hn.PosDiagNorm.toMat, hx_eq, hy_eq]

/-- `z.toMat` is upper triangular (since `x` is upper unipotent
and `diag y` is diagonal). -/
private lemma H_toMat_upperTriangular (z : Hn.H m) :
    IsUpperTriangular z.toMat := by
  intro i j hj
  show ((z.x : Mat m) * z.y.toMat) i j = 0
  simp only [Hn.PosDiagNorm.toMat]
  rw [mul_diag_entry]; exact mul_eq_zero_of_left (z.x.upper hj) _

/-- Our `diag` is `Matrix.diagonal`. -/
private lemma diag_eq_diagonal (d : Fin m → ℝ) :
    diag d = Matrix.diagonal d := by
  ext i j; simp [diag, Matrix.diagonal]

/-- `z.toMat` is a unit in the matrix ring. -/
private lemma H_toMat_isUnit (z : Hn.H m) : IsUnit z.toMat := by
  rw [Matrix.isUnit_iff_isUnit_det]
  -- z.toMat is upper triangular with diagonal = y.d
  have hBT : z.toMat.BlockTriangular id := H_toMat_upperTriangular z
  rw [Matrix.det_of_upperTriangular hBT]
  -- ∏ y.d i > 0, so IsUnit
  have hdiag : ∀ i, z.toMat i i = z.y.d i := by
    intro i; show ((z.x : Mat m) * z.y.toMat) i i = _
    simp only [Hn.PosDiagNorm.toMat]
    rw [mul_diag_entry, z.x.diag_one, one_mul]
  simp_rw [hdiag]
  rw [isUnit_iff_ne_zero]
  exact Finset.prod_pos (fun i _ => z.y.pos_all i) |>.ne'

/-- Embed `Hn.H` into `GL(n, ℝ)`. -/
private noncomputable def H_toGL (z : Hn.H m) :
    Matrix.GeneralLinearGroup (Fin m) ℝ :=
  (H_toMat_isUnit z).unit

@[simp]
private lemma H_toGL_val (z : Hn.H m) :
    ↑(H_toGL z) = z.toMat :=
  (H_toMat_isUnit z).unit_spec

/-- Identity bridge (`GLn m = GL (Fin m) ℝ`). -/
private def toGLn (u : Matrix.GeneralLinearGroup (Fin m) ℝ) :
    GLn m := by exact u

@[simp]
private lemma toGLn_val (u : Matrix.GeneralLinearGroup (Fin m) ℝ) :
    (toGLn u : Mat m) = ↑u := rfl

/-- Product of orthogonal matrices is orthogonal. -/
private lemma IsOrthogonal_mul {Q₁ Q₂ : Mat m}
    (h₁ : IsOrthogonal Q₁)
    (h₂ : IsOrthogonal Q₂) :
    IsOrthogonal (Q₁ * Q₂) := by
  show (Q₁ * Q₂)ᵀ * (Q₁ * Q₂) = 1
  rw [Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc Q₁ᵀ, h₁, Matrix.one_mul, h₂]

/-- The identity is orthogonal. -/
private lemma IsOrthogonal_one :
    IsOrthogonal (1 : Mat m) := by
  show (1 : Mat m)ᵀ * 1 = 1; simp

/-- Scalar matrices commute with everything. -/
private lemma centerMat_comm (c : RUnits) (A : Mat m) :
    centerMat (m := m) c * A = A * centerMat (m := m) c := by
  unfold centerMat
  rw [scalarMat_eq_smul, smul_mul_assoc, mul_smul_comm, mul_one, one_mul]

/-- Subgroup `O(n) · ℝˣ` inside `GL(n, ℝ)`, defined as the
subgroup generated by orthogonal matrices and nonzero scalar
matrices.  Since `O(n) · ℝˣ` is already closed under `*` and
`⁻¹`, the closure equals the set of products `Q * (c • I)`. -/
def OZ_subgroup (m : Nat) :
    Subgroup (Matrix.GeneralLinearGroup (Fin m) ℝ) :=
  Subgroup.closure
    { g : Matrix.GeneralLinearGroup (Fin m) ℝ |
      (∃ Q : Mat m, IsOrthogonal Q ∧
        (g : Mat m) = Q) ∨
      (∃ c : ℝˣ,
        (g : Mat m) = centerMat (m := m) c) }

/-- Generalized upper half-plane as a quotient. -/
abbrev Hquot (m : Nat) :=
  Matrix.GeneralLinearGroup (Fin m) ℝ ⧸ OZ_subgroup m

/-- `centerMat 1 = 1`. -/
private lemma centerMat_one :
    centerMat (m := m) (1 : RUnits) = (1 : Mat m) := by
  ext i j; simp [centerMat, scalarMat, diag, Matrix.one_apply]

/-- An orthogonal matrix is a unit. -/
private lemma IsUnit_of_orthogonal {Q : Mat m}
    (hQ : IsOrthogonal Q) : IsUnit Q := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h := congr_arg Matrix.det hQ
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  exact isUnit_of_mul_eq_one _ _ h

/-- `centerMat (a * b) = centerMat a * centerMat b`. -/
private lemma centerMat_mul (a b : RUnits) :
    centerMat (m := m) (a * b) =
      centerMat (m := m) a * centerMat (m := m) b := by
  unfold centerMat; rw [scalarMat_eq_smul, scalarMat_eq_smul,
    scalarMat_eq_smul, Units.val_mul, smul_mul_assoc,
    one_mul, mul_smul]

/-- `centerMat c` is a unit (constructed via `centerMat c⁻¹`). -/
private lemma IsUnit_centerMat (c : RUnits) :
    IsUnit (centerMat (m := m) c) :=
  ⟨⟨centerMat c, centerMat c⁻¹,
    by rw [← centerMat_mul, mul_inv_cancel, centerMat_one],
    by rw [← centerMat_mul, inv_mul_cancel, centerMat_one]⟩,
   rfl⟩

/-- The z-factor is invariant under right-multiplication by
orthogonal GL elements. -/
private lemma zFactor_orth_inv [HasIwasawa m]
    (a x : Matrix.GeneralLinearGroup (Fin m) ℝ)
    (Q : Mat m) (hQ : IsOrthogonal Q)
    (hval : (x : Mat m) = Q) :
    (HasIwasawa.iwasawa (m := m) (toGLn a)).z =
    (HasIwasawa.iwasawa (m := m) (toGLn (a * x))).z := by
  set fac := HasIwasawa.iwasawa (m := m) (toGLn a)
  have hcorr := HasIwasawa.correct (m := m) (toGLn a)
  let fac' : IwasawaFactorization m :=
    ⟨fac.z,
     ⟨fac.k.Q * Q, IsOrthogonal_mul fac.k.orth hQ⟩,
     fac.d⟩
  have htoMat' : fac'.toMat = (toGLn (a * x) : Mat m) := by
    have lhs_eq : fac'.toMat =
        Hn.H.toMat fac.z * (fac.k.Q * Q) *
        centerMat fac.d := rfl
    rw [lhs_eq, toGLn_val, Units.val_mul, hval,
      ← mul_assoc (Hn.H.toMat fac.z) fac.k.Q Q,
      mul_assoc _ Q (centerMat fac.d),
      ← centerMat_comm fac.d Q,
      ← mul_assoc _ (centerMat fac.d) Q,
      show Hn.H.toMat fac.z * fac.k.Q *
        centerMat fac.d = fac.toMat from rfl,
      hcorr, toGLn_val]
  exact (unique_z_of_two_factorizations (toGLn (a * x))
    _ fac' (HasIwasawa.correct _) htoMat').symm

/-- The z-factor is invariant under right-multiplication by
scalar GL elements. -/
private lemma zFactor_scalar_inv [HasIwasawa m]
    (a x : Matrix.GeneralLinearGroup (Fin m) ℝ)
    (c : ℝˣ) (hval : (x : Mat m) = centerMat (m := m) c) :
    (HasIwasawa.iwasawa (m := m) (toGLn a)).z =
    (HasIwasawa.iwasawa (m := m) (toGLn (a * x))).z := by
  set fac := HasIwasawa.iwasawa (m := m) (toGLn a)
  have hcorr := HasIwasawa.correct (m := m) (toGLn a)
  let fac' : IwasawaFactorization m :=
    ⟨fac.z, fac.k, fac.d * c⟩
  have htoMat' : fac'.toMat = (toGLn (a * x) : Mat m) := by
    have lhs_eq : fac'.toMat =
        Hn.H.toMat fac.z * fac.k.Q *
        centerMat (fac.d * c) := rfl
    rw [lhs_eq, toGLn_val, Units.val_mul, hval,
      centerMat_mul, ← mul_assoc,
      show Hn.H.toMat fac.z * fac.k.Q *
        centerMat fac.d = fac.toMat from rfl,
      hcorr, toGLn_val]
  exact (unique_z_of_two_factorizations (toGLn (a * x))
    _ fac' (HasIwasawa.correct _) htoMat').symm

/-- Target equivalence: `Hn`-data is equivalent to `GL / OZ`.

Requires the Iwasawa decomposition to exist (`HasIwasawa`).
Uses `unique_z_of_two_factorizations` for injectivity and
`OZ_subgroup` for the fiber description. -/
def Hn_equiv_quotient (m : Nat) [HasIwasawa m] :
    Hn.H m ≃ Hquot m where
  toFun z := QuotientGroup.mk (H_toGL z)
  invFun := Quotient.lift
    (fun g => (HasIwasawa.iwasawa (m := m) (toGLn g)).z)
    (by
      -- Coset invariance: a⁻¹ * b ∈ OZ → zFactor a = zFactor b
      intro a b hab
      set zF := fun g : Matrix.GeneralLinearGroup (Fin m) ℝ =>
        (HasIwasawa.iwasawa (m := m) (toGLn g)).z
      change zF a = zF b
      have hmem : a⁻¹ * b ∈ OZ_subgroup m :=
        (QuotientGroup.leftRel_apply).mp hab
      rw [show b = a * (a⁻¹ * b) from by group]
      suffices hsuff : ∀ g, zF g = zF (g * (a⁻¹ * b)) from
        hsuff a
      refine Subgroup.closure_induction
        (fun x hx g => ?_) (fun g => ?_)
        (fun x y _ _ ihx ihy g => ?_)
        (fun x _ ihx g => ?_) hmem
      · -- Generators
        rcases hx with ⟨Q, hQ, hval⟩ | ⟨c, hval⟩
        · exact zFactor_orth_inv g x Q hQ hval
        · exact zFactor_scalar_inv g x c hval
      · -- Identity: zF g = zF (g * 1)
        simp
      · -- Mul: P(x) → P(y) → P(x * y)
        calc zF g = zF (g * x) := ihx g
          _ = zF (g * x * y) := ihy (g * x)
          _ = zF (g * (x * y)) := by rw [mul_assoc]
      · -- Inv: P(x) → P(x⁻¹)
        have h := ihx (g * x⁻¹)
        rw [mul_assoc, inv_mul_cancel, mul_one] at h
        exact h.symm)
  left_inv z := by
    show (HasIwasawa.iwasawa (m := m)
      (toGLn (H_toGL z))).z = z
    let fac_id : IwasawaFactorization m :=
      ⟨z, ⟨1, IsOrthogonal_one⟩, 1⟩
    have htoMat : fac_id.toMat =
        (toGLn (H_toGL z) : Mat m) := by
      have lhs_eq : fac_id.toMat =
          Hn.H.toMat z * 1 * centerMat (1 : RUnits) := rfl
      rw [lhs_eq, mul_one, centerMat_one, mul_one,
        toGLn_val, H_toGL_val]
    exact unique_z_of_two_factorizations _
      _ fac_id (HasIwasawa.correct _) htoMat
  right_inv q := by
    refine Quotient.inductionOn q (fun g => ?_)
    set fac := HasIwasawa.iwasawa (m := m) (toGLn g)
      with hfac_def
    have hcorr := HasIwasawa.correct (m := m) (toGLn g)
    simp only [Quotient.lift_mk]
    suffices hmem : (H_toGL fac.z)⁻¹ * g ∈ OZ_subgroup m by
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr hmem)
    have hk_unit : IsUnit (fac.k.Q : Mat m) :=
      IsUnit_of_orthogonal fac.k.orth
    have hd_unit : IsUnit (centerMat (m := m) fac.d) :=
      IsUnit_centerMat fac.d
    have hk_mem : hk_unit.unit ∈ OZ_subgroup m :=
      Subgroup.subset_closure (Or.inl
        ⟨fac.k.Q, fac.k.orth, hk_unit.unit_spec⟩)
    have hd_mem : hd_unit.unit ∈ OZ_subgroup m :=
      Subgroup.subset_closure (Or.inr
        ⟨fac.d, hd_unit.unit_spec⟩)
    suffices h : (H_toGL fac.z)⁻¹ * g =
        hk_unit.unit * hd_unit.unit from
      h ▸ (OZ_subgroup m).mul_mem hk_mem hd_mem
    -- Key: H_toGL fac.z * hk_unit.unit * hd_unit.unit = g
    have key : H_toGL fac.z * hk_unit.unit * hd_unit.unit = g := by
      apply Units.val_injective
      simp only [Units.val_mul, H_toGL_val,
        hk_unit.unit_spec, hd_unit.unit_spec]
      have fold : Hn.H.toMat fac.z * fac.k.Q *
          centerMat fac.d = fac.toMat := rfl
      rw [fold, hcorr, toGLn_val]
    -- Derive: (H_toGL fac.z)⁻¹ * g = hk_unit.unit * hd_unit.unit
    rw [← key, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]

/-! ### GL(n, ℤ) action on the generalized upper half-plane

Goldfeld, Proposition 1.2.10: `GL(n, ℤ)` acts on `Hn.H m` by
`γ • z = z`-factor of `iwasawa(γ_ℝ · toMat(z))`.
-/

/-- The z-factor of a `GL(n, ℝ)` element via Iwasawa decomposition. -/
private noncomputable def zFactor [HasIwasawa m]
    (g : Matrix.GeneralLinearGroup (Fin m) ℝ) : Hn.H m :=
  (HasIwasawa.iwasawa (m := m) (toGLn g)).z

/-- Right-multiplying by any element of `OZ_subgroup` does not
change the z-factor. -/
private lemma zFactor_OZ_inv [HasIwasawa m]
    (a x : Matrix.GeneralLinearGroup (Fin m) ℝ)
    (hx : x ∈ OZ_subgroup m) :
    zFactor a = zFactor (a * x) := by
  unfold zFactor
  suffices hsuff : ∀ g, (HasIwasawa.iwasawa (m := m) (toGLn g)).z =
      (HasIwasawa.iwasawa (m := m) (toGLn (g * x))).z from
    hsuff a
  refine Subgroup.closure_induction
    (fun x hx g => ?_) (fun g => ?_)
    (fun x y _ _ ihx ihy g => ?_)
    (fun x _ ihx g => ?_) hx
  · -- Generators
    rcases hx with ⟨Q, hQ, hval⟩ | ⟨c, hval⟩
    · exact zFactor_orth_inv g x Q hQ hval
    · exact zFactor_scalar_inv g x c hval
  · -- Identity
    simp
  · -- Mul
    calc (HasIwasawa.iwasawa (m := m) (toGLn g)).z
        = (HasIwasawa.iwasawa (m := m) (toGLn (g * x))).z := ihx g
      _ = (HasIwasawa.iwasawa (m := m)
            (toGLn (g * x * y))).z := ihy (g * x)
      _ = (HasIwasawa.iwasawa (m := m)
            (toGLn (g * (x * y)))).z := by rw [mul_assoc]
  · -- Inv
    have h := ihx (g * x⁻¹)
    rw [mul_assoc, inv_mul_cancel, mul_one] at h
    exact h.symm

/-- The monoid homomorphism `GL(n, ℤ) →* GL(n, ℝ)` induced by
the ring inclusion `ℤ →+* ℝ`. -/
noncomputable def intToReal_GL :
    Matrix.GeneralLinearGroup (Fin m) ℤ →*
    Matrix.GeneralLinearGroup (Fin m) ℝ :=
  Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ)

/-- `GL(n, ℤ)` acts on the generalized upper half-plane `Hn.H m`
by `γ • z = z`-factor of the Iwasawa decomposition of
`γ_ℝ * toGL(z)`. -/
noncomputable instance GLZ_smul_Hn [HasIwasawa m] :
    SMul (Matrix.GeneralLinearGroup (Fin m) ℤ) (Hn.H m) where
  smul γ z := zFactor (intToReal_GL γ * H_toGL z)

/-- The identity in `GL(n, ℤ)` acts trivially on `Hn`. -/
private lemma GLZ_one_smul [HasIwasawa m]
    (z : Hn.H m) :
    (1 : Matrix.GeneralLinearGroup (Fin m) ℤ) • z = z := by
  show zFactor (intToReal_GL 1 * H_toGL z) = z
  rw [map_one, one_mul]
  -- Now: zFactor (H_toGL z) = z
  unfold zFactor
  let fac_id : IwasawaFactorization m :=
    ⟨z, ⟨1, IsOrthogonal_one⟩, 1⟩
  have htoMat : fac_id.toMat =
      (toGLn (H_toGL z) : Mat m) := by
    have lhs_eq : fac_id.toMat =
        Hn.H.toMat z * 1 * centerMat (1 : RUnits) := rfl
    rw [lhs_eq, mul_one, centerMat_one, mul_one,
      toGLn_val, H_toGL_val]
  exact unique_z_of_two_factorizations _
    _ fac_id (HasIwasawa.correct _) htoMat

/-- Helper: decompose a GL element into `H_toGL(z) * kd` where
`kd ∈ OZ_subgroup`. Returns the product `kd` and its OZ
membership. -/
private lemma factorization_OZ_decomp [HasIwasawa m]
    (g : Matrix.GeneralLinearGroup (Fin m) ℝ) :
    ∃ kd : Matrix.GeneralLinearGroup (Fin m) ℝ,
      kd ∈ OZ_subgroup m ∧
      g = H_toGL (zFactor g) * kd := by
  unfold zFactor
  set fac := HasIwasawa.iwasawa (m := m) (toGLn g)
  have hcorr := HasIwasawa.correct (m := m) (toGLn g)
  have hk_unit : IsUnit (fac.k.Q : Mat m) :=
    IsUnit_of_orthogonal fac.k.orth
  have hd_unit : IsUnit (centerMat (m := m) fac.d) :=
    IsUnit_centerMat fac.d
  refine ⟨hk_unit.unit * hd_unit.unit, ?_, ?_⟩
  · exact (OZ_subgroup m).mul_mem
      (Subgroup.subset_closure (Or.inl
        ⟨fac.k.Q, fac.k.orth, hk_unit.unit_spec⟩))
      (Subgroup.subset_closure (Or.inr
        ⟨fac.d, hd_unit.unit_spec⟩))
  · -- g = H_toGL fac.z * (k_unit * d_unit)
    have key : H_toGL fac.z * hk_unit.unit *
        hd_unit.unit = g := by
      apply Units.val_injective
      simp only [Units.val_mul, H_toGL_val,
        hk_unit.unit_spec, hd_unit.unit_spec]
      have fold : Hn.H.toMat fac.z * fac.k.Q *
          centerMat fac.d = fac.toMat := rfl
      rw [fold, hcorr, toGLn_val]
    rw [← key, mul_assoc]

/-- The `GL(n, ℤ)` action on `Hn` is associative:
`(γ * δ) • z = γ • (δ • z)`. -/
private lemma GLZ_mul_smul [HasIwasawa m]
    (γ δ : Matrix.GeneralLinearGroup (Fin m) ℤ)
    (z : Hn.H m) :
    (γ * δ) • z = γ • (δ • z) := by
  show zFactor (intToReal_GL (γ * δ) * H_toGL z) =
    zFactor (intToReal_GL γ * H_toGL
      (zFactor (intToReal_GL δ * H_toGL z)))
  rw [map_mul, mul_assoc]
  -- Decompose δ_ℝ * H_toGL z = H_toGL(δ•z) * kd
  obtain ⟨kd, hkd_mem, hdecomp⟩ :=
    factorization_OZ_decomp (intToReal_GL δ * H_toGL z)
  conv_lhs => rw [hdecomp]
  rw [← mul_assoc]
  exact (zFactor_OZ_inv
    (intToReal_GL γ * H_toGL (zFactor
      (intToReal_GL δ * H_toGL z))) kd hkd_mem).symm

/-- `GL(n, ℤ)` acts on the generalized upper half-plane `Hn.H m`
(Goldfeld, Proposition 1.2.10). -/
noncomputable instance GLZ_mulAction_Hn [HasIwasawa m] :
    MulAction (Matrix.GeneralLinearGroup (Fin m) ℤ) (Hn.H m) where
  one_smul := GLZ_one_smul
  mul_smul := GLZ_mul_smul

/-! ### Siegel sets and fundamental domain -/

/-- A point `z ∈ Hn` is *Siegel-reduced* with parameter `t > 0`
if its diagonal ratios satisfy `y_i ≥ t · y_{i+1}` and its
upper-triangular entries satisfy `|x_{ij}| ≤ 1/2`.

This is Goldfeld, Definition 1.2.8. -/
def IsSiegelReduced (t : ℝ) {m : Nat} (z : Hn.H m) : Prop :=
  (∀ i : Fin m, (h : i.1 + 1 < m) →
    t * z.y.d ⟨i.1 + 1, h⟩ ≤ z.y.d i) ∧
  (∀ i j : Fin m, i < j → |z.x.x i j| ≤ 1 / 2)

/-- The Siegel set `𝔖_t` for parameter `t`. -/
def SiegelSet (t : ℝ) (m : Nat) : Set (Hn.H m) :=
  { z | IsSiegelReduced t z }

/-- **Goldfeld, Theorem 1.2.11**: There exists `t > 0` such that
every `GL(n, ℤ)`-orbit on `Hn` meets the Siegel set `𝔖_t`.
(Goldfeld takes `t = √3 / 2`.)

The proof requires Minkowski reduction theory and is left as
a placeholder. -/
theorem siegel_fundamental_domain (m : Nat) [HasIwasawa m] :
    ∃ t : ℝ, 0 < t ∧ ∀ z : Hn.H m,
      ∃ γ : Matrix.GeneralLinearGroup (Fin m) ℤ,
        γ • z ∈ SiegelSet t m :=
  sorry

end Iwasawa

end MatrixTactics
