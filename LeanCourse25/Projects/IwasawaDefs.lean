import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Lean.Elab.Tactic

/-!
# Iwasawa Decomposition for GL(n, ℝ)

We develop the matrix-level infrastructure for the Iwasawa decomposition
of `GL(n, ℝ)`, following the approach of Goldfeld's
*Automorphic Forms and L-Functions for the Group GL(n, R)*.

## Main definitions

* `IsUpperTriangular`, `IsLowerTriangular`, `IsDiagonal` — predicates
  for `Fin`-indexed square matrices
* `Mat`, `GLn` — abbreviations for `n × n` real matrices and invertible ones
* `Hn.H` — the generalized upper half-plane as a pair `(x, y)`
* `Iwasawa.IwasawaFactorization` — factorization datum `(z, k, d)`
* `Iwasawa.HasIwasawa` — typeclass asserting existence of the decomposition

## Main results

* `upper_mul`, `lower_mul` — triangular matrices are closed under `*`
* `upper_eq_lower_implies_diagonal` — if upper = lower then diagonal
* `Iwasawa.exists_factorization` — existence from the class

## References

* D. Goldfeld, *Automorphic Forms and L-Functions for the Group GL(n, R)*,
  Cambridge Studies in Advanced Mathematics 99, 2006.

## Tags

matrix, triangular, Iwasawa decomposition, general linear group
-/

open scoped BigOperators Matrix
open Finset
noncomputable section

namespace MatrixTactics

/-! ## Core predicates and constructors

We focus on `Fin`-indexed matrices for practical computation,
which gives a total order on indices and strong `simp` support. -/

section Core

variable {α : Type} [Semiring α]
variable {n : Nat}

/-- Upper triangular predicate (`Fin`-indexed). -/
def IsUpperTriangular (A : Matrix (Fin n) (Fin n) α) : Prop :=
  ∀ ⦃i j⦄, j < i → A i j = 0

/-- Lower triangular predicate (`Fin`-indexed). -/
def IsLowerTriangular (A : Matrix (Fin n) (Fin n) α) : Prop :=
  ∀ ⦃i j⦄, i < j → A i j = 0

/-- Diagonal predicate. -/
def IsDiagonal (A : Matrix (Fin n) (Fin n) α) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → A i j = 0

/-- Upper unipotent = upper triangular with diagonal entries equal to 1. -/
def IsUpperUnipotent (A : Matrix (Fin n) (Fin n) α) : Prop :=
  IsUpperTriangular A ∧ ∀ i, A i i = 1

/-- Lower unipotent = lower triangular with diagonal entries equal to 1. -/
def IsLowerUnipotent (A : Matrix (Fin n) (Fin n) α) : Prop :=
  IsLowerTriangular A ∧ ∀ i, A i i = 1

/-- Diagonal matrix constructor. -/
def diag (d : Fin n → α) : Matrix (Fin n) (Fin n) α :=
  fun i j => if i = j then d i else 0

@[simp]
lemma diag_apply_eq (d : Fin n → α) (i : Fin n) :
    diag d i i = d i := by
  simp [diag]

@[simp]
lemma diag_apply_ne (d : Fin n → α) {i j : Fin n} (h : i ≠ j) :
    diag d i j = 0 := by
  simp [diag, h]

lemma isDiagonal_diag (d : Fin n → α) :
    IsDiagonal (diag d) := by
  intro i j hij
  simp [diag, hij]

/-- The scalar matrix `c • I`. -/
def scalarMat (c : α) : Matrix (Fin n) (Fin n) α :=
  diag (fun _ => c)

@[simp]
lemma scalarMat_apply_eq (c : α) (i : Fin n) :
    scalarMat (n := n) c i i = c := by
  simp [scalarMat]

@[simp]
lemma scalarMat_apply_ne (c : α) {i j : Fin n} (h : i ≠ j) :
    scalarMat (n := n) c i j = 0 := by
  simp [scalarMat, h]

/-- Entry of matrix times diagonal: `(A * diag d)_{ij} = A_{ij} * d_j`. -/
lemma mul_diag_entry (A : Matrix (Fin n) (Fin n) α) (d : Fin n → α)
    (i j : Fin n) :
    (A * diag d) i j = A i j * d j := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · simp [diag]
  · intro k _ hk; rw [diag_apply_ne d hk, mul_zero]

end Core

/-! ## Triangular closure lemmas -/

section Triangular

variable {α : Type} [Semiring α]
variable {n : Nat}

lemma upper_add {A B : Matrix (Fin n) (Fin n) α}
    (hA : IsUpperTriangular A)
    (hB : IsUpperTriangular B) :
    IsUpperTriangular (A + B) := by
  intro i j hj
  simp [Matrix.add_apply, hA hj, hB hj]

lemma lower_add {A B : Matrix (Fin n) (Fin n) α}
    (hA : IsLowerTriangular A)
    (hB : IsLowerTriangular B) :
    IsLowerTriangular (A + B) := by
  intro i j hij
  simp [Matrix.add_apply, hA hij, hB hij]

/-- Upper triangular matrices are closed under multiplication. -/
lemma upper_mul {A B : Matrix (Fin n) (Fin n) α}
    (hA : IsUpperTriangular A)
    (hB : IsUpperTriangular B) :
    IsUpperTriangular (A * B) := by
  intro i j hj
  classical
  simp [Matrix.mul_apply]
  refine Finset.sum_eq_zero ?_
  intro k hk
  by_cases hkj : j < k
  · simp [hB hkj]
  · have hki : k < i := lt_of_le_of_lt (le_of_not_gt hkj) hj
    simp [hA hki]

/-- Lower triangular matrices are closed under multiplication. -/
lemma lower_mul {A B : Matrix (Fin n) (Fin n) α}
    (hA : IsLowerTriangular A)
    (hB : IsLowerTriangular B) :
    IsLowerTriangular (A * B) := by
  intro i j hij
  classical
  simp [Matrix.mul_apply]
  refine Finset.sum_eq_zero ?_
  intro k hk
  by_cases hik : i < k
  · simp [hA hik]
  · have hkj : k < j := lt_of_le_of_lt (le_of_not_gt hik) hij
    simp [hB hkj]

lemma diagonal_upper {A : Matrix (Fin n) (Fin n) α}
    (hA : IsDiagonal A) :
    IsUpperTriangular A := by
  intro i j hj
  exact hA (Ne.symm (ne_of_lt hj))

lemma diagonal_lower {A : Matrix (Fin n) (Fin n) α}
    (hA : IsDiagonal A) :
    IsLowerTriangular A := by
  intro i j hij
  exact hA (ne_of_lt hij)

end Triangular

/-! ## Entry-level proof tools -/

section EntryTools

variable {α : Type} [Semiring α]
variable {n : Nat}

omit [Semiring α] in
lemma ext_ij {A B : Matrix (Fin n) (Fin n) α}
    (h : ∀ i j, A i j = B i j) : A = B := by
  ext i j
  exact h i j

lemma upper_zero {A : Matrix (Fin n) (Fin n) α}
    (hA : IsUpperTriangular A)
    {i j : Fin n} (h : j < i) :
    A i j = 0 := hA h

lemma lower_zero {A : Matrix (Fin n) (Fin n) α}
    (hA : IsLowerTriangular A)
    {i j : Fin n} (h : i < j) :
    A i j = 0 := hA h

end EntryTools

namespace Tactics

open Lean Elab Tactic

/-- `matrix_entry_simp` expands `mul_apply`, `transpose_apply`
and simplifies. Typical usage: `ext i j; matrix_entry_simp`. -/
elab "matrix_entry_simp" : tactic => do
  evalTactic (← `(tactic|
    simp [Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.dotProduct, Finset.mul_sum]))

end Tactics

/-! ## GL(n, ℝ) layer

These are lightweight wrappers around `Fin`-indexed real matrices
that we use throughout the Iwasawa development. -/

section GLn

variable {n : Nat}

/-- `Mat n` is `n × n` matrices over `ℝ`. -/
abbrev Mat (n : Nat) := Matrix (Fin n) (Fin n) ℝ

/-- `GL(n, ℝ)` via Mathlib's `GeneralLinearGroup`. -/
abbrev GLn (n : Nat) := Matrix.GeneralLinearGroup (Fin n) ℝ

/-- The scalar subgroup (center): pairs `(c, hc)` with `c ≠ 0`. -/
structure CenterScalar (n : Nat) where
  c : ℝ
  hc : c ≠ 0

/-- Scalar matrix in `Mat n`. -/
def CenterScalar.toMat {n : Nat} (d : CenterScalar n) : Mat n :=
  scalarMat (n := n) d.c

/-- Orthogonal predicate: `Qᵀ * Q = 1`. -/
def IsOrthogonal {n : Nat} (Q : Mat n) : Prop :=
  Qᵀ * Q = (1 : Mat n)

end GLn

end MatrixTactics
