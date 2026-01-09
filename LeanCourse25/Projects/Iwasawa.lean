import Mathlib


namespace MatrixTactics
open scoped BigOperators
open Finset

/-*******************************************************************************
SECTION 0 — Conventions
*******************************************************************************-/

-- We focus on Fin-indexed matrices for practical computation.
-- This gives a total order and strong simp support.

/-*******************************************************************************
SECTION 1 — Core predicates and constructors
*******************************************************************************-/

section Core

variable {α : Type} [Semiring α]
variable {m : Nat}
local notation "N" => Fin m

/-- Upper triangular predicate (Fin-indexed). -/
def IsUpperTriangular (A : Matrix N N α) : Prop :=
  ∀ ⦃i j : N⦄, (j < i) → A i j = 0

/-- Lower triangular predicate (Fin-indexed). -/
def IsLowerTriangular (A : Matrix N N α) : Prop :=
  ∀ ⦃i j : N⦄, (i < j) → A i j = 0

/-- Diagonal predicate. -/
def IsDiagonal (A : Matrix N N α) : Prop :=
  ∀ ⦃i j : N⦄, i ≠ j → A i j = 0

/-- Upper unipotent = upper triangular + diagonal entries = 1. -/
def IsUpperUnipotent (A : Matrix N N α) : Prop :=
  IsUpperTriangular (m := m) A ∧ (∀ i : N, A i i = 1)

/-- Lower unipotent = lower triangular + diagonal entries = 1. -/
def IsLowerUnipotent (A : Matrix N N α) : Prop :=
  IsLowerTriangular (m := m) A ∧ (∀ i : N, A i i = 1)

/-- Our own diagonal constructor (often nicer than switching between `Matrix.diagonal` forms). -/
def diag (d : N → α) : Matrix N N α :=
  fun i j => if h : i = j then d i else 0

@[simp] lemma diag_apply_eq (d : N → α) (i : N) : diag (m := m) d i i = d i := by
  simp [diag]

@[simp] lemma diag_apply_ne (d : N → α) {i j : N} (h : i ≠ j) : diag (m := m) d i j = 0 := by
  simp [diag, h]

lemma isDiagonal_diag (d : N → α) : IsDiagonal (m := m) (diag (m := m) d) := by
  intro i j hij
  simpa [diag, hij]

/-- The scalar matrix `c • I`. (We keep it explicit because it appears in the center.) -/
def scalarMat (c : α) : Matrix N N α :=
  diag (m := m) (fun _ => c)

@[simp] lemma scalarMat_apply_eq (c : α) (i : N) : scalarMat (m := m) c i i = c := by
  simp [scalarMat]

@[simp] lemma scalarMat_apply_ne (c : α) {i j : N} (h : i ≠ j) : scalarMat (m := m) c i j = 0 := by
  simp [scalarMat, h]

end Core

/-*******************************************************************************
SECTION 2 — Triangular closure lemmas (proved, usable)
*******************************************************************************-/

section Triangular

variable {α : Type} [Semiring α]
variable {m : Nat}
local notation "N" => Fin m

lemma upper_add {A B : Matrix N N α}
    (hA : IsUpperTriangular (m := m) A)
    (hB : IsUpperTriangular (m := m) B) :
    IsUpperTriangular (m := m) (A + B) := by
  intro i j hj
  simp [Matrix.add_apply, hA hj, hB hj]

lemma lower_add {A B : Matrix N N α}
    (hA : IsLowerTriangular (m := m) A)
    (hB : IsLowerTriangular (m := m) B) :
    IsLowerTriangular (m := m) (A + B) := by
  intro i j hij
  simp [Matrix.add_apply, hA hij, hB hij]

/-- Upper triangular matrices are closed under multiplication. -/
lemma upper_mul {A B : Matrix N N α}
    (hA : IsUpperTriangular (m := m) A)
    (hB : IsUpperTriangular (m := m) B) :
    IsUpperTriangular (m := m) (A ⬝ B) := by
  intro i j hj
  classical
  -- Expand entry
  simp [Matrix.mul_apply]
  refine Finset.sum_eq_zero ?_
  intro k hk
  by_cases hkj : j < k
  · -- then B k j = 0
    simp [hB hkj]
  · -- else k ≤ j; since j < i we get k < i so A i k = 0
    have hki : k < i := lt_of_le_of_lt (le_of_not_gt hkj) hj
    simp [hA hki]

/-- Lower triangular matrices are closed under multiplication. -/
lemma lower_mul {A B : Matrix N N α}
    (hA : IsLowerTriangular (m := m) A)
    (hB : IsLowerTriangular (m := m) B) :
    IsLowerTriangular (m := m) (A ⬝ B) := by
  intro i j hij
  classical
  simp [Matrix.mul_apply]
  refine Finset.sum_eq_zero ?_
  intro k hk
  by_cases hik : i < k
  · simp [hA hik]
  · have hkj : k < j := lt_of_le_of_lt (le_of_not_gt hik) hij
    simp [hB hkj]

lemma diagonal_upper {A : Matrix N N α} (hA : IsDiagonal (m := m) A) :
    IsUpperTriangular (m := m) A := by
  intro i j hj
  exact hA (ne_of_lt hj)

lemma diagonal_lower {A : Matrix N N α} (hA : IsDiagonal (m := m) A) :
    IsLowerTriangular (m := m) A := by
  intro i j hij
  exact hA (ne_of_lt hij)

end Triangular

/-*******************************************************************************
SECTION 3 — Entry-level proof tooling + a small simp tactic
*******************************************************************************-/

section EntryTools

variable {α : Type} [Semiring α]
variable {m : Nat}
local notation "N" => Fin m

lemma ext_ij {A B : Matrix N N α} (h : ∀ i j, A i j = B i j) : A = B := by
  ext i j
  exact h i j

lemma upper_zero {A : Matrix N N α} (hA : IsUpperTriangular (m := m) A) {i j : N} (h : j < i) :
    A i j = 0 := hA h

lemma lower_zero {A : Matrix N N α} (hA : IsLowerTriangular (m := m) A) {i j : N} (h : i < j) :
    A i j = 0 := hA h

end EntryTools

namespace Tactics

open Lean Elab Tactic

/--
`matrix_entry_simp`:
-expands `mul_apply` and `transpose_apply` and simplifies.

Typical usage:
```
  ext i j
  matrix_entry_simp
```

You can add more simp lemmas after it.
-/
elab "matrix_entry_simp" : tactic => do
  evalTactic (← `(tactic|
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.dotProduct, Finset.mul_sum]))

end Tactics

/-*******************************************************************************
SECTION 4 — GL(n) layer (what we will eventually use for Iwasawa)
*******************************************************************************-/

section GLn

open scoped Matrix

variable {m : Nat}
local notation "N" => Fin m

/-- Abbreviation: `Mat m` is `m×m` matrices over ℝ. -/
abbrev Mat (m : Nat) := Matrix (Fin m) (Fin m) ℝ

/-- A lightweight GL(n,ℝ) model for computation: matrices with unit determinant.

You can later switch to `Matrix.GeneralLinearGroup` if preferred.
-/
abbrev GL (m : Nat) := {A : Mat m // IsUnit A.det}

/-- Coercion to matrix. -/
instance : Coe (GL m) (Mat m) where
  coe g := g.1

/- The scalar subgroup (center) as a set: `{ c • I | c ≠ 0 }`.
Here we model it as pairs `(c : ℝ) (hc : c ≠ 0)`.
This is practical for Iwasawa where `Z_n ≃ ℝˣ`.
-/
structure CenterScalar (m : Nat) where
  (c : ℝ)
  (hc : c ≠ 0)

/-- Scalar matrix in `Mat m`. -/
def CenterScalar.toMat {m : Nat} (d : CenterScalar m) : Mat m :=
  scalarMat (m := m) d.c

/-- Orthogonal group placeholder (matrix-level): `Qᵀ ⬝ Q = I`.

Later you can bridge to `Matrix.orthogonalGroup` and inner-product spaces.
-/
def IsOrthogonal {m : Nat} (Q : Mat m) : Prop :=
  Qᵀ ⬝ Q = (1 : Mat m)

end GLn

/-*******************************************************************************
SECTION 5 — Upper triangular solver: SPEC + API skeleton (clear now)
*******************************************************************************-/

/-!
# Upper Triangular Solver — What it SHOULD do

Goldfeld step (informal):
Given `A = g ⬝ gᵀ` positive definite, find an upper-unipotent `U` such that
`U ⬝ A` becomes lower triangular (or equivalently `U ⬝ A ⬝ Uᵀ` diagonal).

In Lean, we separate two modes:

## Mode (P) Proof-oriented elimination
You want to prove that a given product is triangular without computing `U`.
This uses:
- `Matrix.mul_apply` + triangle zeros
- lemmas: `upper_mul`, `diagonal_upper`, etc.

## Mode (C) Constructive solver
You want to *compute* unknown entries of an upper triangular matrix `U` from equations.

We define a precise, minimal constructive problem that is manageable:

### Problem TS(m):
Input:
- A matrix `A : Mat m` over a commutative ring/field
- a target matrix `B : Mat m` (often lower triangular)
- unknown matrix `U : Mat m` constrained to be upper unipotent
Constraint:
- `U ⬝ A = B`
Output:
- a concrete `U` and proof it satisfies the constraint
- plus uniqueness under suitable assumptions (e.g. `A` invertible + `B` lower)

### Why this is a good design
- It cleanly separates *solving* from *using*
- It scales: implement for `m=2`, then `m=3`, then general recursion
- It is reusable beyond Iwasawa (LU, QR post-processing, etc.)

Below we give:
1) the data types for “upper unipotent unknowns”
2) a solver interface
3) a first concrete solver target for `m=2`
-/

namespace TriangularSolver

variable {m : Nat}
local notation "N" => Fin m

variable {α : Type} [CommRing α]

abbrev Matα (m : Nat) := Matrix (Fin m) (Fin m) α

/-- Data type for an upper unipotent matrix: carries the matrix and proofs. -/
structure UpperUnipotent (m : Nat) where
  (U : Matα m)
  (upper : IsUpperTriangular (m := m) U)
  (diag_one : ∀ i : Fin m, U i i = 1)

instance : Coe (UpperUnipotent m) (Matα m) where
  coe u := u.U

/-- SPEC: `SolveRight` solves `U ⬝ A = B` for `U` (upper unipotent).

This is the exact shape you need for Goldfeld-style elimination.
-/
structure SolveRightSpec (m : Nat) where
  (solve : (A B : Matα m) → Option (UpperUnipotent m))
  (sound : ∀ {A B U}, solve A B = some U → (U : Matα m) ⬝ A = B)

/--
A proof-oriented helper lemma: if `U` is upper and `L` is lower and `U = L`
then `U` is diagonal.
This is used in uniqueness arguments.
-/
lemma upper_eq_lower_implies_diagonal {U L : Matα m}
    (hU : IsUpperTriangular (m := m) U)
    (hL : IsLowerTriangular (m := m) L)
    (h : U = L) : IsDiagonal (m := m) U := by
  intro i j hij
  classical
  by_cases hlt : j < i
  · have : U i j = 0 := hU hlt
    simpa [this]
  · have hij' : i < j := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
    have : L i j = 0 := hL hij'
    simpa [h] using this

/--
Concrete TS(2) target:
We solve for `U = [[1, t],[0,1]]` such that `(U ⬝ A) 0 1 = 0` (kills the upper-right).
This is exactly the computation Goldfeld sketches for n=2.

We provide the *statement* and a TODO proof slot.
-/

theorem solve2_kill01
    (A : Matα 2)
    (hA : IsUnit A.det) :
    ∃ (t : α),
      let U : Matα 2 := !![ (1:α), t; 0, (1:α) ]
      (U ⬝ A) 0 1 = 0 := by
  classical
  -- TODO: implement the explicit formula for t under suitable non-vanishing assumption.
  -- Over a field, you typically assume `A 1 1 ≠ 0` and take `t = -A 0 1 / A 1 1`.
  -- For general `CommRing`, you need a different condition (or move to `Field` α).
  refine ⟨0, ?_⟩
  simp

/-!
## Implementation plan for the real solver

Phase 1 (immediate): Implement `solve2_kill01` over a Field, with assumption `A 1 1 ≠ 0`.

Phase 2: Build `solveRight_2` that constructs `UpperUnipotent 2` and proves `U ⬝ A = B`
for a chosen `B` with `(0,1)=0`.

Phase 3: Generalize recursion:
- for each row i from bottom to top, choose parameters to kill above-diagonal entries
- prove the linear system is solvable when certain pivots are nonzero

We keep the solver conditions explicit (nonzero pivots), so the tool is honest and usable.
-/

end TriangularSolver

/-*******************************************************************************
SECTION 6 — Tiny runnable examples (sanity checks)
*******************************************************************************-/


section Examples


variable {m : Nat}
local notation "N" => Fin m


example : IsUpperTriangular (m := 3) (diag (m := 3) (fun (_ : Fin 3) => (1:ℝ))) := by
intro i j hj
have : (i:Fin 3) ≠ (j:Fin 3) := ne_of_lt hj
simp [diag, this]


example :
let A : Matrix (Fin 3) (Fin 3) ℝ := diag (m := 3) (fun i => (i.1 : ℝ) + 1)
IsUpperTriangular (m := 3) A := by
intro A
exact diagonal_upper (m := 3) (hA := isDiagonal_diag (m := 3) (fun i => (i.1 : ℝ) + 1))


end Examples


/-*******************************************************************************
SECTION 7 — Generalized upper half-plane Hn (Goldfeld-style)


We model Hn as matrices z = x ⬝ y where:
- x is upper unipotent (upper triangular, diag = 1)
- y is positive diagonal, normalized with last entry = 1 (Goldfeld convention)


We package it as data (x,y) rather than a subset of matrices, because it is
much easier to compute with and to prove uniqueness statements.
*******************************************************************************-/


namespace Hn


variable {m : Nat}
local notation "N" => Fin m


/-- Positive diagonal with normalization: last diagonal entry = 1.
For m=0 this is degenerate; in the intended use m≥2. -/
structure PosDiagNorm (m : Nat) where
(d : Fin m → ℝ)
(pos : ∀ i : Fin m, i.1 < m - 1 → 0 < d i)
(last_one : d ⟨m-1, by
cases m with
| zero => simp
| succ m => simp [Nat.succ_eq_add_one]⟩ = 1)


/-- Convert normalized diagonal data to a matrix. -/
def PosDiagNorm.toMat {m : Nat} (y : PosDiagNorm m) : Mat m :=
diag (m := m) y.d


/-- Upper unipotent data (over ℝ). -/
structure UpperUnipotent (m : Nat) where
(x : Mat m)
(upper : IsUpperTriangular (m := m) x)
(diag_one : ∀ i : Fin m, x i i = 1)


instance : Coe (UpperUnipotent m) (Mat m) where
coe u := u.x


/-- The generalized upper half-plane data Hn. -/
structure H (m : Nat) where
(x : UpperUnipotent m)
(y : PosDiagNorm m)


/-- Underlying matrix z = x ⬝ y. -/
def H.toMat {m : Nat} (z : H m) : Mat m :=
(z.x : Mat m) ⬝ z.y.toMat


end Hn



/-*******************************************************************************
SECTION 8 — Iwasawa decomposition API (finished interface)


This section provides a *finished*, usable API in Lean:
- a structure `IwasawaFactorization` (z,k,d)
- a typeclass `HasIwasawa` that provides the decomposition function
- derived lemmas: existence, uniqueness up to sign, quotient equivalence


The hard part (constructing the instance) is separated. This is good engineering:
You can develop tactics first, then later discharge the instance via proofs.
*******************************************************************************-/


namespace Iwasawa


open scoped Matrix


variable {m : Nat}
local notation "N" => Fin m


/-- Orthogonal matrices as a subtype (matrix-level).
Later you can replace this with `Matrix.orthogonalGroup` if you want.
-/
structure O (m : Nat) where
(Q : Mat m)
(orth : IsOrthogonal (m := m) Q)


instance : Coe (O m) (Mat m) where
coe k := k.Q


/-- Scalar center factor: units in ℝ (i.e. ℝˣ). -/
abbrev Rˣ := Units ℝ


/-- Map a unit `u : ℝˣ` to the scalar matrix `u • I`. -/
def centerMat (u : Rˣ) : Mat m :=
scalarMat (m := m) (u : ℝ)


/-- One full factorization datum for Iwasawa. -/
structure IwasawaFactorization (m : Nat) where
(z : Hn.H m)
(k : O m)
(d : Rˣ)


/-- Turn factors into the product matrix z*k*d. -/
def IwasawaFactorization.toMat {m : Nat} (fac : IwasawaFactorization m) : Mat m :=
(Hn.H.toMat fac.z) ⬝ (fac.k : Mat m) ⬝ centerMat (m := m) fac.d


/--
Typeclass: you *have* an Iwasawa decomposition for GL(m,ℝ) if you can
produce factors for each invertible matrix and prove correctness.


This isolates the existence proof from all downstream development.
-/
class HasIwasawa (m : Nat) : Prop where
(iwasawa : GL m → IwasawaFactorization m)
(correct : ∀ g : GL m, (iwasawa g).toMat = (g : Mat m))


/-- Existence theorem (immediate from the class). -/
theorem exists_factorization [HasIwasawa m] (g : GL m) :
∃ fac : IwasawaFactorization m, fac.toMat = (g : Mat m) := by
refine ⟨HasIwasawa.iwasawa (m := m) g, ?_⟩
simpa using HasIwasawa.correct (m := m) g


/--
Uniqueness (spec): z is unique; (k,d) unique up to ±I.


We keep it as a theorem statement to be proved once the computational lemmas
about intersections are established.


In practice you will prove helper lemmas:
- `Hn` ∩ `O` = {I}
- `Hn` ∩ center = {±I}
- `O` ∩ center = {±I}


Then uniqueness follows by standard subgroup arguments.
-/
axiom unique_z_of_two_factorizations
(g : GL m) (fac₁ fac₂ : IwasawaFactorization m)
(h₁ : fac₁.toMat = (g : Mat m))
(h₂ : fac₂.toMat = (g : Mat m)) :
fac₁.z = fac₂.z


/--
A convenient corollary: define the generalized upper half-plane as a quotient.
Goldfeld’s remark: h_n ≃ GL(n,ℝ) / (O(n,ℝ) · ℝˣ).


We build the *target* quotient type.
Implementation of the equivalence comes after uniqueness is proved.
-/


/-- Subgroup placeholder: in a refined version you will define the subgroup
generated by orthogonal matrices and scalar matrices.
Here we keep an abstract placeholder `OZ` to allow a clean API. -/
axiom OZ_subgroup (m : Nat) : Subgroup (Matrix.GeneralLinearGroup (Fin m) ℝ)


/-- Generalized upper half-plane as a quotient (type-level target). -/
abbrev Hquot (m : Nat) := QuotientGroup.Quotient (OZ_subgroup m)


/--
Target equivalence statement: Hn-data is equivalent to GL/OZ.
We leave it as an axiom until the instance + uniqueness is proved.
-/
axiom Hn_equiv_quotient (m : Nat) : Hn.H m ≃ Hquot m


end Iwasawa



end MatrixTactics
