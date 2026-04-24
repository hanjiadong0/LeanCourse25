import LeanCourse25.Projects.IwasawaDefs

open scoped BigOperators Matrix
open Finset
noncomputable section

namespace MatrixTactics

/-! ## Upper triangular solver

Goldfeld step (informal): given a positive-definite `A`, find an
upper-unipotent `U` such that `U * A` becomes lower triangular.

We separate two modes:
1. **Proof-oriented**: prove that a given product is triangular
2. **Constructive**: compute the entries of `U` from equations

Below we define data types, a solver interface, and a first
concrete target for `m = 2`. -/

namespace TriangularSolver

variable {m : Nat}
variable {α : Type} [CommRing α]

abbrev Matα (α : Type) [CommRing α] (m : Nat) :=
  Matrix (Fin m) (Fin m) α

/-- Upper unipotent matrix: carries the matrix and proofs. -/
structure UpperUnipotent (α : Type) [CommRing α] (m : Nat) where
  U : Matα α m
  upper : IsUpperTriangular U
  diag_one : ∀ i : Fin m, U i i = 1

instance (α : Type) [CommRing α] (m : Nat) :
    Coe (UpperUnipotent α m) (Matα α m) where
  coe u := u.U

/-- Solver spec: `SolveRight` solves `U * A = B` for upper
unipotent `U`. -/
structure SolveRightSpec (α : Type) [CommRing α] (m : Nat) where
  solve : (A B : Matα α m) → Option (UpperUnipotent α m)
  sound : ∀ {A B U}, solve A B = some U →
    (U : Matα α m) * A = B

namespace SolveRightSpec

/-- Completeness notion for `SolveRightSpec`: every target equation has a witness. -/
def Complete (S : SolveRightSpec α m) : Prop :=
  ∀ A B, ∃ U, S.solve A B = some U

/-- For `m > 0` over a nontrivial ring, `SolveRightSpec` cannot be complete:
the equation `U * 1 = 0` has no upper-unipotent solution. -/
theorem not_complete [Nontrivial α] {m : Nat} (S : SolveRightSpec α m)
    (hm : 0 < m) : ¬ S.Complete := by
  intro hcomplete
  rcases hcomplete (1 : Matα α m) (0 : Matα α m) with ⟨U, hU⟩
  have hEq : (U : Matα α m) * (1 : Matα α m) = (0 : Matα α m) :=
    S.sound hU
  have hzero : (U : Matα α m) = (0 : Matα α m) := by
    simp at hEq
    exact hEq
  let i : Fin m := ⟨0, hm⟩
  have hdiag0 : (U : Matα α m) i i = 0 := by
    simp [hzero]
  have hdiag1 : (U : Matα α m) i i = 1 := by
    simpa using U.diag_one i
  have h01 : (0 : α) = 1 := hdiag0.symm.trans hdiag1
  exact zero_ne_one h01

end SolveRightSpec

/-- If `U` is upper and `L` is lower and `U = L`, then `U` is
diagonal. -/
lemma upper_eq_lower_implies_diagonal
    {U L : Matα α m}
    (hU : IsUpperTriangular U)
    (hL : IsLowerTriangular L)
    (h : U = L) : IsDiagonal U := by
  intro i j hij
  classical
  by_cases hlt : j < i
  · have : U i j = 0 := hU hlt
    simp [this]
  · have hij' : i < j :=
      lt_of_le_of_ne (le_of_not_gt hlt) hij
    have : L i j = 0 := hL hij'
    simpa [h] using this

/-- Concrete TS(2) target: kill upper-right entry with a
unipotent matrix.  Given an inverse `inv11` of `A 1 1`, we set
`t = −(A 0 1) * inv11`. -/
theorem solve2_kill01
    (A : Matα α 2)
    (inv11 : α) (hinv : inv11 * A 1 1 = 1) :
    ∃ (t : α),
      let U : Matα α 2 := !![(1 : α), t; 0, (1 : α)]
      (U * A) 0 1 = 0 := by
  use -(A 0 1) * inv11
  have key : A 0 1 * inv11 * A 1 1 = A 0 1 := by
    rw [mul_assoc, hinv, mul_one]
  simp [Matrix.mul_apply, Fin.sum_univ_two, key]

/-- The explicit `2×2` upper-unipotent matrix used by `solve2_kill01`. -/
def unipotent2 (t : α) : Matα α 2 :=
  !![(1 : α), t; 0, (1 : α)]

/-- `unipotent2 t` is upper triangular. -/
lemma unipotent2_upper (t : α) :
    IsUpperTriangular (unipotent2 (α := α) t) := by
  intro i j hj
  fin_cases i <;> fin_cases j <;> simp [unipotent2] at hj ⊢

/-- The diagonal of `unipotent2 t` is `1`. -/
lemma unipotent2_diag_one (t : α) :
    ∀ i : Fin 2, unipotent2 (α := α) t i i = 1 := by
  intro i
  fin_cases i <;> simp [unipotent2]

/-- Constructive `2×2` elimination witness in structured form. -/
theorem solve2_upperUnipotent
    (A : Matα α 2)
    (inv11 : α) (hinv : inv11 * A 1 1 = 1) :
    ∃ U : UpperUnipotent α 2, ((U : Matα α 2) * A) 0 1 = 0 := by
  rcases solve2_kill01 (A := A) inv11 hinv with ⟨t, ht⟩
  refine ⟨⟨unipotent2 (α := α) t,
      unipotent2_upper (α := α) t,
      unipotent2_diag_one (α := α) t⟩, ?_⟩
  simpa [unipotent2] using ht

/-- `solve2_upperUnipotent` packaged with the produced matrix `B = U*A`. -/
theorem solve2_lowering_data
    (A : Matα α 2)
    (inv11 : α) (hinv : inv11 * A 1 1 = 1) :
    ∃ U : UpperUnipotent α 2, ∃ B : Matα α 2,
      (U : Matα α 2) * A = B ∧ B 0 1 = 0 := by
  rcases solve2_upperUnipotent (A := A) inv11 hinv with ⟨U, h01⟩
  refine ⟨U, (U : Matα α 2) * A, rfl, h01⟩

section Base2

variable [Field α]

/-- A concrete `2×2` solver over a field:
if `A 1 1 ≠ 0`, use `t = -(A 0 1) / (A 1 1)` and return the
corresponding upper-unipotent witness when it matches the target `B`. -/
noncomputable def solveRight2Field : SolveRightSpec α 2 where
  solve A B := by
    classical
    by_cases h11 : A 1 1 = 0
    · exact none
    ·
      let inv11 : α := (A 1 1)⁻¹
      let t : α := -(A 0 1) * inv11
      let U0 : UpperUnipotent α 2 :=
        ⟨unipotent2 (α := α) t,
          unipotent2_upper (α := α) t,
          unipotent2_diag_one (α := α) t⟩
      exact if hB : ((U0 : Matα α 2) * A = B) then some U0 else none
  sound := by
    intro A B U hU
    classical
    by_cases h11 : A 1 1 = 0
    · simp [h11] at hU
    · simp [h11] at hU
      rcases hU with ⟨hB, hEq⟩
      cases hEq
      exact hB

/-- Specialization of `solveRight2Field` to real matrices. -/
noncomputable def solveRight2Real : SolveRightSpec ℝ 2 :=
  solveRight2Field (α := ℝ)

end Base2

/-- Recursively build solver specs for dimensions `n+2`.

`base` is the `2×2` solver; `step n` lifts a solver at size `n+2`
to a solver at size `n+3`. -/
def buildSolveRightFamily
    (base : SolveRightSpec α 2)
    (step : ∀ n, SolveRightSpec α (n + 2) →
      SolveRightSpec α (n + 3)) :
    ∀ n, SolveRightSpec α (n + 2)
  | 0 => base
  | n + 1 => step n (buildSolveRightFamily base step n)

@[simp]
lemma buildSolveRightFamily_zero
    (base : SolveRightSpec α 2)
    (step : ∀ n, SolveRightSpec α (n + 2) →
      SolveRightSpec α (n + 3)) :
    buildSolveRightFamily (α := α) base step 0 = base := rfl

@[simp]
lemma buildSolveRightFamily_succ
    (base : SolveRightSpec α 2)
    (step : ∀ n, SolveRightSpec α (n + 2) →
      SolveRightSpec α (n + 3))
    (n : Nat) :
    buildSolveRightFamily (α := α) base step (n + 1) =
      step n (buildSolveRightFamily (α := α) base step n) := rfl

/-- Inductive data for constructing `SolveRightSpec` in all dimensions `m ≥ 2`. -/
structure RecursiveSolveRight (α : Type) [CommRing α] where
  base : SolveRightSpec α 2
  step : ∀ n, SolveRightSpec α (n + 2) →
    SolveRightSpec α (n + 3)

/-- One recursion step (`n+2 → n+3`) in Schur-complement style.

`reduce` extracts the smaller (`n+2`) elimination problem from the
current (`n+3`) one; `lift` reconstructs a size-`n+3` upper-unipotent
solution from the current pair `(A,B)` and a smaller solution; `sound`
certifies that this reconstructed solution solves the original problem. -/
structure SchurStep (α : Type) [CommRing α] (n : Nat) where
  reduce :
    Matα α (n + 3) → Matα α (n + 3) →
      Matα α (n + 2) × Matα α (n + 2)
  lift :
    Matα α (n + 3) → Matα α (n + 3) →
      UpperUnipotent α (n + 2) → Option (UpperUnipotent α (n + 3))
  sound : ∀ {A B : Matα α (n + 3)}
      (u : UpperUnipotent α (n + 2)),
      ∀ {U : UpperUnipotent α (n + 3)},
      lift A B u = some U →
      ((u : Matα α (n + 2)) * (reduce A B).1 = (reduce A B).2) →
      ((U : Matα α (n + 3)) * A = B)

/-- Build a solver step from Schur-step data. -/
def stepOfSchur {n : Nat}
    (S : SchurStep α n)
    (prev : SolveRightSpec α (n + 2)) :
    SolveRightSpec α (n + 3) where
  solve := fun A B =>
    let p := S.reduce A B
    match prev.solve p.1 p.2 with
    | none => none
    | some u => S.lift A B u
  sound := by
    intro A B U hU
    set p : Matα α (n + 2) × Matα α (n + 2) := S.reduce A B
    cases hprev : prev.solve p.1 p.2 with
    | none =>
      simp [p, hprev] at hU
    | some u =>
      simp [p, hprev] at hU
      have hsmall : (u : Matα α (n + 2)) * p.1 = p.2 :=
        prev.sound hprev
      exact S.sound (A := A) (B := B) u (U := U) hU
        (by simpa [p] using hsmall)

/-- Concrete recursive solver obtained from:
- base `2×2` solver
- Schur-complement step data in every dimension. -/
def recursiveSolveRightOfSchur
    (base : SolveRightSpec α 2)
    (schur : ∀ n, SchurStep α n) :
    RecursiveSolveRight α where
  base := base
  step := fun n prev => stepOfSchur (S := schur n) prev

/-- Shift an index from `Fin (n+2)` into `Fin (n+3)` by skipping `0`. -/
def succIdx {n : Nat} (i : Fin (n + 2)) : Fin (n + 3) :=
  ⟨i.1 + 1, by omega⟩

/-- Principal `(n+2)×(n+2)` submatrix obtained by deleting row/column `0`. -/
def dropFirst {n : Nat} (M : Matα α (n + 3)) : Matα α (n + 2) :=
  fun i j => M (succIdx i) (succIdx j)

/-- Canonical Schur reduction by principal submatrices. -/
def reducePrincipal {n : Nat}
    (A B : Matα α (n + 3)) :
    Matα α (n + 2) × Matα α (n + 2) :=
  (dropFirst A, dropFirst B)

/-- Top-row residual on columns `1..n+2`, viewed in `Fin (n+2)`. -/
def topRowDelta {n : Nat}
    (A B : Matα α (n + 3)) : Fin (n + 2) → α :=
  fun j => B 0 (succIdx j) - A 0 (succIdx j)

/-- Row-vector times matrix (explicit entry formula). -/
def rowMul {n : Nat}
    (r : Fin (n + 2) → α) (M : Matα α (n + 2)) :
    Fin (n + 2) → α :=
  fun j => ∑ k : Fin (n + 2), r k * M k j

/-- Embed `u : UpperUnipotent (n+2)` into size `n+3` by padding an identity
row/column at index `0`. -/
def padUpperUnipotent {n : Nat}
    (u : UpperUnipotent α (n + 2)) : UpperUnipotent α (n + 3) where
  U := fun i j =>
    if hi : i.1 = 0 then
      if hj : j.1 = 0 then 1 else 0
    else
      if hj : j.1 = 0 then 0 else
        u.U ⟨i.1 - 1, by omega⟩ ⟨j.1 - 1, by omega⟩
  upper := by
    intro i j hj
    by_cases hi0 : i.1 = 0
    · have : False := by omega
      exact (this.elim)
    · by_cases hj0 : j.1 = 0
      · simp [hi0, hj0]
      · have hsub : (j.1 - 1) < (i.1 - 1) := by omega
        have hs : (⟨j.1 - 1, by omega⟩ : Fin (n + 2)) <
            (⟨i.1 - 1, by omega⟩ : Fin (n + 2)) := by
          exact hsub
        simpa [hi0, hj0] using u.upper hs
  diag_one := by
    intro i
    by_cases hi0 : i.1 = 0
    · simp [hi0]
    · simp [hi0, u.diag_one ⟨i.1 - 1, by omega⟩]

/-- Constructive Schur completion candidate:
embed the reduced upper-unipotent `u` and compute top-row coefficients via
`delta * (dropFirst A)⁻¹` (using `nonsingInv`). -/
noncomputable def completePrincipalNonsingInv {n : Nat}
    (A B : Matα α (n + 3))
    (u : UpperUnipotent α (n + 2)) : UpperUnipotent α (n + 3) := by
  classical
  let A11 : Matα α (n + 2) := dropFirst A
  let delta : Fin (n + 2) → α := topRowDelta (α := α) A B
  let v : Fin (n + 2) → α :=
    rowMul (α := α) delta (A11⁻¹)
  refine
    { U := fun i j =>
        if hi : i.1 = 0 then
          if hj : j.1 = 0 then 1 else
            v ⟨j.1 - 1, by omega⟩
        else
          if hj : j.1 = 0 then 0 else
            u.U ⟨i.1 - 1, by omega⟩ ⟨j.1 - 1, by omega⟩
      upper := ?_
      diag_one := ?_ }
  · intro i j hj
    by_cases hi0 : i.1 = 0
    · have : False := by omega
      exact this.elim
    · by_cases hj0 : j.1 = 0
      · simp [hi0, hj0]
      · have hsub : (j.1 - 1) < (i.1 - 1) := by omega
        have hs : (⟨j.1 - 1, by omega⟩ : Fin (n + 2)) <
            (⟨i.1 - 1, by omega⟩ : Fin (n + 2)) := by
          exact hsub
        simpa [hi0, hj0] using u.upper hs
  · intro i
    by_cases hi0 : i.1 = 0
    · simp [hi0]
    · simp [hi0, u.diag_one ⟨i.1 - 1, by omega⟩]

/-- Template for a Schur step using principal reduction and a user-provided
top-row completion rule.

This is the concrete plug-in point for Goldfeld's recursive elimination:
you only need to supply `complete` and its `sound` proof. -/
def schurStepPrincipal {n : Nat}
    (complete :
      Matα α (n + 3) → Matα α (n + 3) →
        UpperUnipotent α (n + 2) → UpperUnipotent α (n + 3))
    (hsound : ∀ {A B : Matα α (n + 3)}
      (u : UpperUnipotent α (n + 2)),
      ((u : Matα α (n + 2)) * (reducePrincipal (α := α) A B).1 =
        (reducePrincipal (α := α) A B).2) →
      ((complete A B u : Matα α (n + 3)) * A = B)) :
    SchurStep α n where
  reduce := reducePrincipal (α := α)
  lift := fun A B u => some (complete A B u)
  sound := by
    intro A B u U hLift hu
    cases hLift
    simpa using hsound (A := A) (B := B) u hu

/-- Checked Schur step using principal reduction and a candidate completion.

`complete` proposes a lifted witness; the step keeps it only when it
verifies `U * A = B`. This yields a concrete `n+2 → n+3` recursion step
without requiring a separate soundness proof for `complete`. -/
noncomputable def schurStepPrincipalChecked {n : Nat}
    (complete :
      Matα α (n + 3) → Matα α (n + 3) →
        UpperUnipotent α (n + 2) → UpperUnipotent α (n + 3)) :
    SchurStep α n where
  reduce := reducePrincipal (α := α)
  lift := fun A B u => by
    classical
    let U0 : UpperUnipotent α (n + 3) := complete A B u
    exact if hU0 : ((U0 : Matα α (n + 3)) * A = B) then some U0 else none
  sound := by
    intro A B u U hLift _hu
    classical
    let U0 : UpperUnipotent α (n + 3) := complete A B u
    by_cases hU0 : ((U0 : Matα α (n + 3)) * A = B)
    · simp [U0, hU0] at hLift
      cases hLift
      simpa [U0] using hU0
    · simp [U0, hU0] at hLift

/-- Concrete principal step template: embed the reduced solution by padding
an identity row/column, and accept it when it solves `U * A = B`. -/
noncomputable def schurStepPadChecked {n : Nat} : SchurStep α n :=
  schurStepPrincipalChecked (α := α)
    (fun _A _B u => padUpperUnipotent (α := α) u)

/-- Concrete principal step template using `completePrincipalNonsingInv`. -/
noncomputable def schurStepPrincipalNonsingInvChecked {n : Nat} :
    SchurStep α n :=
  schurStepPrincipalChecked (α := α)
    (fun A B u => completePrincipalNonsingInv (α := α) A B u)

/-- Fully concrete recursive solver family:
base `2×2` solver + checked principal padding step in every higher size. -/
noncomputable def recursiveSolveRightPadChecked
    (base : SolveRightSpec α 2) :
    RecursiveSolveRight α :=
  recursiveSolveRightOfSchur (α := α) base
    (fun _ => schurStepPadChecked (α := α))

/-- Recursive solver family using the principal `nonsingInv` completion step,
validated by the checked Schur wrapper. -/
noncomputable def recursiveSolveRightNonsingInvChecked
    (base : SolveRightSpec α 2) :
    RecursiveSolveRight α :=
  recursiveSolveRightOfSchur (α := α) base
    (fun _ => schurStepPrincipalNonsingInvChecked (α := α))

namespace RecursiveSolveRight

/-- Family produced by recursion from base and step. -/
def family (R : RecursiveSolveRight α) :
    ∀ n, SolveRightSpec α (n + 2) :=
  buildSolveRightFamily (α := α) R.base R.step

/-- Access a solver at any dimension `m ≥ 2`. -/
def atDim (R : RecursiveSolveRight α) {m : Nat} (hm : 2 ≤ m) :
    SolveRightSpec α m := by
  have hm' : (m - 2) + 2 = m := by omega
  simpa [hm', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    R.family (m - 2)

@[simp]
lemma atDim_two (R : RecursiveSolveRight α) :
    R.atDim (m := 2) (by omega) = R.base := by
  unfold atDim family buildSolveRightFamily
  simp

end RecursiveSolveRight

/-! ### Implementation plan

Phase 1 (done): `solve2_kill01` over a `Field`, assuming `A 1 1 ≠ 0`.

Phase 2: Build `solveRight_2` that constructs `UpperUnipotent 2`
and proves `U * A = B` for a chosen `B` with `B 0 1 = 0`.

Phase 3: Generalize by recursion, killing above-diagonal entries
row by row from bottom to top. -/

end TriangularSolver

/-! ## Examples (sanity checks) -/

section Examples

example : IsUpperTriangular
    (diag (fun (_ : Fin 3) => (1 : ℝ))) := by
  intro i j hj
  have : (i : Fin 3) ≠ (j : Fin 3) := Ne.symm (ne_of_lt hj)
  simp [diag, this]

example :
    let A : Matrix (Fin 3) (Fin 3) ℝ :=
      diag (fun i => (i.1 : ℝ) + 1)
    IsUpperTriangular A := by
  intro A
  exact diagonal_upper
    (hA := isDiagonal_diag (fun i => (i.1 : ℝ) + 1))

end Examples

end MatrixTactics
