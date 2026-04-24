import LeanCourse25.Projects.IwasawaDefs
import LeanCourse25.Projects.IwasawaTriangularSolver

open scoped BigOperators Matrix
open Finset
noncomputable section

namespace MatrixTactics

/-! ## Generalized upper half-plane Hn (Goldfeld-style)

We model `Hn` as matrices `z = x * y` where:
- `x` is upper unipotent (upper triangular, diagonal = 1)
- `y` is positive diagonal, normalized with last entry = 1

We package it as data `(x, y)` rather than a subset of matrices,
because it is much easier to compute with and prove uniqueness. -/

namespace Hn

variable {m : Nat}

/-- Positive diagonal with normalization: last entry = 1.
For `m = 0` this is degenerate; intended use is `m ≥ 2`. -/
structure PosDiagNorm (m : Nat) where
  hm : 0 < m
  d : Fin m → ℝ
  pos : ∀ i : Fin m, i.1 < m - 1 → 0 < d i
  last_one : d ⟨m - 1, by omega⟩ = 1

/-- Convert normalized diagonal data to a matrix. -/
def PosDiagNorm.toMat {m : Nat} (y : PosDiagNorm m) : Mat m :=
  diag y.d

/-- Every entry of a `PosDiagNorm` is positive. -/
lemma PosDiagNorm.pos_all {m : Nat} (y : PosDiagNorm m)
    (j : Fin m) : 0 < y.d j := by
  by_cases h : j.1 < m - 1
  · exact y.pos j h
  · suffices y.d j = 1 by linarith
    have hval : j.1 = m - 1 := le_antisymm
      (by omega) (Nat.not_lt.mp h)
    have : j = ⟨m - 1, Nat.sub_lt y.hm Nat.one_pos⟩ :=
      Fin.ext (by simp [hval])
    rw [this]; exact y.last_one

/-- Every entry of a `PosDiagNorm` is nonzero. -/
lemma PosDiagNorm.ne_zero {m : Nat} (y : PosDiagNorm m)
    (j : Fin m) : y.d j ≠ 0 :=
  ne_of_gt (y.pos_all j)

/-- Upper unipotent data (over `ℝ`). -/
structure UpperUnipotent (m : Nat) where
  x : Mat m
  upper : IsUpperTriangular x
  diag_one : ∀ i : Fin m, x i i = 1

instance : Coe (UpperUnipotent m) (Mat m) where
  coe u := u.x

/-- Convert elimination data from `TriangularSolver` into `Hn` form. -/
def UpperUnipotent.ofTriangularSolver
    (u : TriangularSolver.UpperUnipotent ℝ m) : UpperUnipotent m :=
  ⟨u.U, u.upper, u.diag_one⟩

/-- The generalized upper half-plane data. -/
structure H (m : Nat) where
  x : UpperUnipotent m
  y : PosDiagNorm m

/-- Underlying matrix `z = x * y`. -/
def H.toMat {m : Nat} (z : H m) : Mat m :=
  (z.x : Mat m) * z.y.toMat

/-- `H.toMat` is injective: the underlying matrix uniquely
determines the half-plane element. The `(i,j)` entry of
`x * diag(d)` is `x_{ij} * d_j`; the diagonal gives `d`,
and dividing off-diagonal entries by `d_j > 0` gives `x`. -/
lemma H_toMat_injective {m : Nat} (z₁ z₂ : H m)
    (h : z₁.toMat = z₂.toMat) : z₁ = z₂ := by
  have hentry : ∀ i j : Fin m,
      z₁.x.x i j * z₁.y.d j = z₂.x.x i j * z₂.y.d j := by
    intro i j
    have := congr_fun (congr_fun h i) j
    simp only [H.toMat, PosDiagNorm.toMat] at this
    rwa [mul_diag_entry, mul_diag_entry] at this
  have hd : z₁.y.d = z₂.y.d := by
    ext j
    have := hentry j j
    rw [z₁.x.diag_one, z₂.x.diag_one] at this
    linarith
  have hx : z₁.x.x = z₂.x.x := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [z₁.x.diag_one, z₂.x.diag_one]
    · by_cases hlt : j < i
      · rw [z₁.x.upper hlt, z₂.x.upper hlt]
      · have he := hentry i j
        rw [congr_fun hd j] at he
        exact mul_right_cancel₀ (z₂.y.ne_zero j) he
  rcases z₁ with ⟨⟨_, _, _⟩, ⟨_, _, _, _⟩⟩
  rcases z₂ with ⟨⟨_, _, _⟩, ⟨_, _, _, _⟩⟩
  simp only at hx hd
  subst hx; subst hd; rfl

end Hn

end MatrixTactics
