# Iwasawa.lean: Complete Function/Declaration Ability Reference

Source: `LeanCourse25/Projects/Iwasawa.lean`

This document lists every declaration (`def`, `theorem`, `lemma`, `structure`, `class`, `abbrev`, `instance`) and states its practical ability (what it provides to downstream code).

Note: Layer boundaries follow your 6-layer architecture. The overlap `L891-L901` is assigned to Layer 5 (pipeline machinery) to match usage.

Total declarations indexed: 170

## Layer 1: Predicates & Matrix Types

| Line | Kind | Qualified Name | Ability |
|---:|---|---|---|
| 62 | `def` | `MatrixTactics.IsUpperTriangular` | Upper triangular predicate (`Fin`-indexed). |
| 66 | `def` | `MatrixTactics.IsLowerTriangular` | Lower triangular predicate (`Fin`-indexed). |
| 70 | `def` | `MatrixTactics.IsDiagonal` | Diagonal predicate. |
| 74 | `def` | `MatrixTactics.IsUpperUnipotent` | Upper unipotent = upper triangular with diagonal entries equal to 1. |
| 78 | `def` | `MatrixTactics.IsLowerUnipotent` | Lower unipotent = lower triangular with diagonal entries equal to 1. |
| 82 | `def` | `MatrixTactics.diag` | Diagonal matrix constructor. |
| 86 | `lemma` | `MatrixTactics.diag_apply_eq` | No docstring immediately above. Header: `lemma diag_apply_eq (d : N → α) (i : N) :` |
| 91 | `lemma` | `MatrixTactics.diag_apply_ne` | No docstring immediately above. Header: `lemma diag_apply_ne (d : N → α) {i j : N} (h : i ≠ j) :` |
| 95 | `lemma` | `MatrixTactics.isDiagonal_diag` | No docstring immediately above. Header: `lemma isDiagonal_diag (d : N → α) :` |
| 101 | `def` | `MatrixTactics.scalarMat` | The scalar matrix `c • I`. |
| 105 | `lemma` | `MatrixTactics.scalarMat_apply_eq` | No docstring immediately above. Header: `lemma scalarMat_apply_eq (c : α) (i : N) :` |
| 110 | `lemma` | `MatrixTactics.scalarMat_apply_ne` | No docstring immediately above. Header: `lemma scalarMat_apply_ne (c : α) {i j : N} (h : i ≠ j) :` |
| 115 | `lemma` | `MatrixTactics.mul_diag_entry` | Entry of matrix times diagonal: `(A * diag d)_{ij} = A_{ij} * d_j`. |
| 133 | `lemma` | `MatrixTactics.upper_add` | No docstring immediately above. Header: `lemma upper_add {A B : Matrix N N α}` |
| 140 | `lemma` | `MatrixTactics.lower_add` | No docstring immediately above. Header: `lemma lower_add {A B : Matrix N N α}` |
| 148 | `lemma` | `MatrixTactics.upper_mul` | Upper triangular matrices are closed under multiplication. |
| 163 | `lemma` | `MatrixTactics.lower_mul` | Lower triangular matrices are closed under multiplication. |
| 177 | `lemma` | `MatrixTactics.diagonal_upper` | No docstring immediately above. Header: `lemma diagonal_upper {A : Matrix N N α}` |
| 183 | `lemma` | `MatrixTactics.diagonal_lower` | No docstring immediately above. Header: `lemma diagonal_lower {A : Matrix N N α}` |
| 200 | `lemma` | `MatrixTactics.ext_ij` | No docstring immediately above. Header: `lemma ext_ij {A B : Matrix N N α}` |
| 205 | `lemma` | `MatrixTactics.upper_zero` | No docstring immediately above. Header: `lemma upper_zero {A : Matrix N N α}` |
| 210 | `lemma` | `MatrixTactics.lower_zero` | No docstring immediately above. Header: `lemma lower_zero {A : Matrix N N α}` |
| 241 | `abbrev` | `MatrixTactics.Mat` | `Mat m` is `m × m` matrices over `ℝ`. |
| 244 | `abbrev` | `MatrixTactics.GLn` | A lightweight `GL(n, ℝ)` model: matrices with unit determinant. |
| 246 | `instance` | `(anonymous instance)` | No docstring immediately above. Header: `instance : Coe (GLn m) (Mat m) where` |
| 250 | `structure` | `MatrixTactics.CenterScalar` | The scalar subgroup (center): pairs `(c, hc)` with `c ≠ 0`. |
| 255 | `def` | `MatrixTactics.CenterScalar.toMat` | Scalar matrix in `Mat m`. |
| 259 | `def` | `MatrixTactics.IsOrthogonal` | Orthogonal predicate: `Qᵀ * Q = 1`. |

## Layer 2: Triangular Solver

| Line | Kind | Qualified Name | Ability |
|---:|---|---|---|
| 282 | `abbrev` | `MatrixTactics.TriangularSolver.Matα` | No docstring immediately above. Header: `abbrev Matα (α : Type) [CommRing α] (m : Nat) :=` |
| 286 | `structure` | `MatrixTactics.TriangularSolver.UpperUnipotent` | Upper unipotent matrix: carries the matrix and proofs. |
| 291 | `instance` | `(unnamed)` | No docstring immediately above. Header: `instance (α : Type) [CommRing α] (m : Nat) :` |
| 297 | `structure` | `MatrixTactics.TriangularSolver.SolveRightSpec` | Solver spec: `SolveRight` solves `U * A = B` for upper unipotent `U`. |
| 305 | `def` | `MatrixTactics.TriangularSolver.SolveRightSpec.Complete` | Completeness notion for `SolveRightSpec`: every target equation has a witness. |
| 310 | `theorem` | `MatrixTactics.TriangularSolver.SolveRightSpec.not_complete` | For `m > 0` over a nontrivial ring, `SolveRightSpec` cannot be complete: the equation `U * 1 = 0` has no upper-unipotent solution. |
| 331 | `lemma` | `MatrixTactics.TriangularSolver.upper_eq_lower_implies_diagonal` | If `U` is upper and `L` is lower and `U = L`, then `U` is diagonal. |
| 349 | `theorem` | `MatrixTactics.TriangularSolver.solve2_kill01` | Concrete TS(2) target: kill upper-right entry with a unipotent matrix. Given an inverse `inv11` of `A 1 1`, we set `t = −(A 0 1) * inv11`. |
| 361 | `def` | `MatrixTactics.TriangularSolver.unipotent2` | The explicit `2×2` upper-unipotent matrix used by `solve2_kill01`. |
| 365 | `lemma` | `MatrixTactics.TriangularSolver.unipotent2_upper` | `unipotent2 t` is upper triangular. |
| 371 | `lemma` | `MatrixTactics.TriangularSolver.unipotent2_diag_one` | The diagonal of `unipotent2 t` is `1`. |
| 377 | `theorem` | `MatrixTactics.TriangularSolver.solve2_upperUnipotent` | Constructive `2×2` elimination witness in structured form. |
| 388 | `theorem` | `MatrixTactics.TriangularSolver.solve2_lowering_data` | `solve2_upperUnipotent` packaged with the produced matrix `B = U*A`. |
| 403 | `def` | `MatrixTactics.TriangularSolver.solveRight2Field` | A concrete `2×2` solver over a field: if `A 1 1 ≠ 0`, use `t = -(A 0 1) / (A 1 1)` and return the corresponding upper-unipotent witness when it matches the target `B`. |
| 427 | `def` | `MatrixTactics.TriangularSolver.solveRight2Real` | Specialization of `solveRight2Field` to real matrices. |
| 436 | `def` | `MatrixTactics.TriangularSolver.buildSolveRightFamily` | Recursively build solver specs for dimensions `n+2`. `base` is the `2×2` solver; `step n` lifts a solver at size `n+2` to a solver at size `n+3`. |
| 445 | `lemma` | `MatrixTactics.TriangularSolver.buildSolveRightFamily_zero` | No docstring immediately above. Header: `lemma buildSolveRightFamily_zero` |
| 452 | `lemma` | `MatrixTactics.TriangularSolver.buildSolveRightFamily_succ` | No docstring immediately above. Header: `lemma buildSolveRightFamily_succ` |
| 461 | `structure` | `MatrixTactics.TriangularSolver.RecursiveSolveRight` | Inductive data for constructing `SolveRightSpec` in all dimensions `m ≥ 2`. |
| 472 | `structure` | `MatrixTactics.TriangularSolver.SchurStep` | One recursion step (`n+2 → n+3`) in Schur-complement style. `reduce` extracts the smaller (`n+2`) elimination problem from the current (`n+3`) one; `lift` reconstructs a size-`n+3` upper-unipotent solution from the current pair `(A,B)` and a smaller solution; `sound` certifies that this reconstructed solution solves the original problem. |
| 487 | `def` | `MatrixTactics.TriangularSolver.stepOfSchur` | Build a solver step from Schur-step data. |
| 512 | `def` | `MatrixTactics.TriangularSolver.recursiveSolveRightOfSchur` | Concrete recursive solver obtained from: - base `2×2` solver - Schur-complement step data in every dimension. |
| 520 | `def` | `MatrixTactics.TriangularSolver.succIdx` | Shift an index from `Fin (n+2)` into `Fin (n+3)` by skipping `0`. |
| 524 | `def` | `MatrixTactics.TriangularSolver.dropFirst` | Principal `(n+2)×(n+2)` submatrix obtained by deleting row/column `0`. |
| 528 | `def` | `MatrixTactics.TriangularSolver.reducePrincipal` | Canonical Schur reduction by principal submatrices. |
| 534 | `def` | `MatrixTactics.TriangularSolver.topRowDelta` | Top-row residual on columns `1..n+2`, viewed in `Fin (n+2)`. |
| 539 | `def` | `MatrixTactics.TriangularSolver.rowMul` | Row-vector times matrix (explicit entry formula). |
| 546 | `def` | `MatrixTactics.TriangularSolver.padUpperUnipotent` | Embed `u : UpperUnipotent (n+2)` into size `n+3` by padding an identity row/column at index `0`. |
| 575 | `def` | `MatrixTactics.TriangularSolver.completePrincipalNonsingInv` | Constructive Schur completion candidate: embed the reduced upper-unipotent `u` and compute top-row coefficients via `delta * (dropFirst A)⁻¹` (using `nonsingInv`). |
| 614 | `def` | `MatrixTactics.TriangularSolver.schurStepPrincipal` | Template for a Schur step using principal reduction and a user-provided top-row completion rule. This is the concrete plug-in point for Goldfeld's recursive elimination: you only need to supply `complete` and its `sound` proof. |
| 636 | `def` | `MatrixTactics.TriangularSolver.schurStepPrincipalChecked` | Checked Schur step using principal reduction and a candidate completion. `complete` proposes a lifted witness; the step keeps it only when it verifies `U * A = B`. This yields a concrete `n+2 → n+3` recursion step without requiring a separate soundness proof for `complete`. |
| 658 | `def` | `MatrixTactics.TriangularSolver.schurStepPadChecked` | Concrete principal step template: embed the reduced solution by padding an identity row/column, and accept it when it solves `U * A = B`. |
| 663 | `def` | `MatrixTactics.TriangularSolver.schurStepPrincipalNonsingInvChecked` | Concrete principal step template using `completePrincipalNonsingInv`. |
| 670 | `def` | `MatrixTactics.TriangularSolver.recursiveSolveRightPadChecked` | Fully concrete recursive solver family: base `2×2` solver + checked principal padding step in every higher size. |
| 678 | `def` | `MatrixTactics.TriangularSolver.recursiveSolveRightNonsingInvChecked` | Recursive solver family using the principal `nonsingInv` completion step, validated by the checked Schur wrapper. |
| 687 | `def` | `MatrixTactics.TriangularSolver.RecursiveSolveRight.family` | Family produced by recursion from base and step. |
| 692 | `def` | `MatrixTactics.TriangularSolver.RecursiveSolveRight.atDim` | Access a solver at any dimension `m ≥ 2`. |
| 699 | `lemma` | `MatrixTactics.TriangularSolver.RecursiveSolveRight.atDim_two` | No docstring immediately above. Header: `lemma atDim_two (R : RecursiveSolveRight α) :` |

## Layer 3: Hn Upper Half-Plane

| Line | Kind | Qualified Name | Ability |
|---:|---|---|---|
| 757 | `structure` | `MatrixTactics.Hn.PosDiagNorm` | Positive diagonal with normalization: last entry = 1. For `m = 0` this is degenerate; intended use is `m ≥ 2`. |
| 764 | `def` | `MatrixTactics.Hn.PosDiagNorm.toMat` | Convert normalized diagonal data to a matrix. |
| 768 | `lemma` | `MatrixTactics.Hn.PosDiagNorm.pos_all` | Every entry of a `PosDiagNorm` is positive. |
| 780 | `lemma` | `MatrixTactics.Hn.PosDiagNorm.ne_zero` | Every entry of a `PosDiagNorm` is nonzero. |
| 785 | `structure` | `MatrixTactics.Hn.UpperUnipotent` | Upper unipotent data (over `ℝ`). |
| 790 | `instance` | `(anonymous instance)` | No docstring immediately above. Header: `instance : Coe (UpperUnipotent m) (Mat m) where` |
| 794 | `def` | `MatrixTactics.Hn.UpperUnipotent.ofTriangularSolver` | Convert elimination data from `TriangularSolver` into `Hn` form. |
| 799 | `structure` | `MatrixTactics.Hn.H` | The generalized upper half-plane data. |
| 804 | `def` | `MatrixTactics.Hn.H.toMat` | Underlying matrix `z = x * y`. |
| 811 | `lemma` | `MatrixTactics.Hn.H_toMat_injective` | `H.toMat` is injective: the underlying matrix uniquely determines the half-plane element. The `(i,j)` entry of `x * diag(d)` is `x_{ij} * d_j`; the diagonal gives `d`, and dividing off-diagonal entries by `d_j > 0` gives `x`. |

## Layer 4: Factorization Datum

| Line | Kind | Qualified Name | Ability |
|---:|---|---|---|
| 856 | `structure` | `MatrixTactics.Iwasawa.O` | Orthogonal matrices as a subtype (matrix-level). |
| 860 | `instance` | `(anonymous instance)` | No docstring immediately above. Header: `instance : Coe (O m) (Mat m) where` |
| 864 | `abbrev` | `MatrixTactics.Iwasawa.RUnits` | Scalar center factor: units in `ℝ`. |
| 867 | `def` | `MatrixTactics.Iwasawa.centerMat` | Map a unit `u : ℝˣ` to the scalar matrix `u • I`. |
| 871 | `structure` | `MatrixTactics.Iwasawa.IwasawaFactorization` | One full factorization datum for Iwasawa. |
| 877 | `def` | `MatrixTactics.Iwasawa.IwasawaFactorization.toMat` | Turn factors into the product matrix `z * k * d`. |

## Layer 5: Pipeline Machinery

### 5.1 Concrete Packaging API

| Kind | Qualified Name | Ability |
|---|---|---|
| `structure` | `MatrixTactics.Iwasawa.ConcretePipeline` | Per-`g` concrete package `(x,y,Q,d)` plus reconstruction proof. |
| `def/theorem` | `...ConcretePipeline.zOf`, `...facOf`, `...facOf_correct`, `...rawWitness` | Projectors and correctness transport from pipeline data to Iwasawa witnesses. |
| `def` | `...ConcretePipeline.ofRaw` | Main constructor from raw witness formulas (the key handoff point from algorithmic formulas). |
| `theorem` | `...ConcretePipeline.exists_factorization_of_pipeline` | Existence theorem directly from one concrete pipeline. |

### 5.2 Dimension Recursion for Pipelines

| Kind | Qualified Name | Ability |
|---|---|---|
| `structure` | `...ConcretePipeline.RecursiveMkPipeline` | Inductive builder: `2×2` base + `n+2 → n+3` step. |
| `def/lemma` | `...RecursiveMkPipeline.family`, `...family_zero`, `...family_succ` | Recursively generated family and its unfold lemmas. |
| `structure` | `...ConcretePipeline.RecursiveConcretePipeline` | Converts recursive builder into `m ≥ 2`-indexed concrete pipelines. |
| `def/theorem` | `...RecursiveConcretePipeline.atDim`, `...exists_factorization_ge2` | Access at concrete size and derive all-`m` existence. |

### 5.3 Bridge: Triangular Solver -> Pipeline

| Kind | Qualified Name | Ability |
|---|---|---|
| `structure` | `...ConcretePipeline.FromTriangularSolver` | Packaging bridge from recursive triangular solvers to concrete Iwasawa pipelines. |
| `def` | `...FromTriangularSolver.pipelineFamily`, `...ofRecursiveMkPipeline` | Build pipeline family from solver family or recursive pipeline formulas. |
| `structure` | `...FromTriangularSolver.RawMkPipeline` | Raw witness layer (`baseRaw/stepRaw`) for explicit formulas. |
| `def` | `...RawMkPipeline.fromRecursiveMkPipeline`, `...fromFromTriangularSolver` | Reuse existing pipeline/bridge to auto-derive raw witness formulas. |
| `def` | `...RawMkPipeline.toRecursiveMkPipeline`, `...toFromTriangularSolver` | Build recursive pipeline/bridge back from raw witnesses. |
| `theorem` | `...FromTriangularSolver.exists_raw_ge2`, `...exists_factorization_ge2` (+ `..._fact`) | Global existence directly from recursive solver + packaging bridge. |

### 5.4 ConstructiveCore (Goldfeld Prop. 1.2.6 Core)

| Kind | Qualified Name | Ability |
|---|---|---|
| `structure` | `MatrixTactics.Iwasawa.ConstructiveCore` | Single object bundling base solver, Schur recursion, and packaging. |
| `def` | `...ConstructiveCore.ofRaw`, `...solverRec`, `...bridge` | Canonical assembly from raw witness data. |
| `inductive/def` | `...CheckedFlavor`, `...checkedSchur`, `...ofChecked` | New generic checked strategy API (`pad` / `nonsingInv`) replacing duplicated constructors. |
| `def` | `...ofCheckedFromRecursive`, `...ofCheckedFromFromTriangularSolver` | Generic constructors from recursive pipelines / bridge objects. |
| `def` | `...ofPadChecked*`, `...ofNonsingInvChecked*` | Compatibility aliases over generic checked constructors. |
| `theorem` | `...exists_factorization_ofChecked*`, `...exists_raw_ofChecked*` | Generic existence theorems parameterized by checked flavor. |
| `theorem` | `...exists_factorization_ofPadChecked*`, `...exists_raw_ofPadChecked*`, `...NonsingInv...` | Specialized wrappers preserving old API names. |

### 5.5 Layer-5 Projection to `HasIwasawa`

| Kind | Qualified Name | Ability |
|---|---|---|
| `class/theorem` | `MatrixTactics.Iwasawa.HasIwasawa`, `MatrixTactics.Iwasawa.exists_factorization` | Abstract existence interface and immediate theorem. |
| `def` | `...ConcretePipeline.toHasIwasawa`, `...FromTriangularSolver.toHasIwasawa(Fact)` | Promote a concrete pipeline or bridge to `HasIwasawa`. |
| `def` | `...ConstructiveCore.toHasIwasawa(Fact)` | Promote full constructive core to `HasIwasawa`. |
| `def` | `...ConstructiveCore.toHasIwasawaFact_ofCheckedFromRecursive` | New generic `HasIwasawa` wrapper by checked flavor + recursive builder. |
| `def` | `...ConstructiveCore.toHasIwasawaFact_ofCheckedFromFromTriangularSolver` | New generic `HasIwasawa` wrapper by checked flavor + bridge object. |
| `def` | `...ConstructiveCore.toHasIwasawaFact_ofPadCheckedFromRecursive`, `...toHasIwasawaFact_ofNonsingInvCheckedFromRecursive` | Backward-compatible specialized aliases. |

## Layer 6: Theorems & GL(n,Z) Action

| Line | Kind | Qualified Name | Ability |
|---:|---|---|---|
| 1495 | `class` | `MatrixTactics.Iwasawa.HasConstructiveCore` | Register one global constructive core for all dimensions. This packages the remaining construction data as a single global instance; after installing it, Iwasawa existence theorems depend only on `g` (and the dimension side-condition `2 ≤ m`). |
| 1502 | `class` | `MatrixTactics.Iwasawa.HasFromTriangularSolver` | Register one concrete algorithmic bridge (`FromTriangularSolver`). From this single object we derive a global `ConstructiveCore` via the principal `nonsingInv` checked constructor. |
| 1508 | `def` | `MatrixTactics.Iwasawa.HasFromTriangularSolver.constructiveCore` | The constructive core induced by the registered bridge. |
| 1514 | `instance` | `MatrixTactics.Iwasawa.HasFromTriangularSolver.toHasConstructiveCore` | Any registered bridge gives a global constructive core instance. |
| 1523 | `instance` | `MatrixTactics.Iwasawa.HasConstructiveCore.hasIwasawaFact` | Canonical `HasIwasawa` instance induced by a registered constructive core. |
| 1528 | `theorem` | `MatrixTactics.Iwasawa.HasConstructiveCore.exists_raw_fact` | Raw Goldfeld-style existence from the registered constructive core. |
| 1535 | `theorem` | `MatrixTactics.Iwasawa.HasConstructiveCore.exists_factorization_fact` | Structured factorization existence from the registered constructive core. |
| 1544 | `theorem` | `MatrixTactics.Iwasawa.exists_factorization_of_witnesses` | Package explicit witnesses `(z, k, d)` into `IwasawaFactorization`. |
| 1553 | `theorem` | `MatrixTactics.Iwasawa.exists_factorization_of_raw` | Concrete existence from a raw matrix decomposition lemma. |
| 1564 | `theorem` | `MatrixTactics.Iwasawa.exists_factorization_of_solver_gram` | Construction helper for the triangular-solver/Gram pipeline: package a residual orthogonal matrix and scalar into a factorization. |
| 1577 | `lemma` | `MatrixTactics.Iwasawa.orthogonal_unipotent_eq_one` | An orthogonal upper-unipotent real matrix is the identity. Each column-norm `∑_k Q_{kj}² = 1` (from `QᵀQ = I`); upper-triangularity kills `k > j`, unipotency gives `Q_{jj} = 1`, so every remaining `Q_{kj}²` vanishes by non-negativity over `ℝ`. |
| 1658 | `theorem` | `MatrixTactics.Iwasawa.gram_of_factorization` | Concrete Gram identity for an Iwasawa factorization: the orthogonal factor disappears in `g * gᵀ`. |
| 1790 | `theorem` | `MatrixTactics.Iwasawa.unique_z_of_two_factorizations` | Uniqueness of the `z`-factor: if two Iwasawa factorisations have the same product matrix, their `z` components agree. Strategy: form the Gram matrix `g * gᵀ`, which eliminates the orthogonal factor. Then `z₁ * z₁ᵀ = z₂ * z₂ᵀ` (LDL), and LDL uniqueness gives `z₁ = z₂`. |
| 1945 | `def` | `MatrixTactics.Iwasawa.OZ_subgroup` | Subgroup `O(n) · ℝˣ` inside `GL(n, ℝ)`, defined as the subgroup generated by orthogonal matrices and nonzero scalar matrices. Since `O(n) · ℝˣ` is already closed under `*` and `⁻¹`, the closure equals the set of products `Q * (c • I)`. |
| 1955 | `abbrev` | `MatrixTactics.Iwasawa.Hquot` | Generalized upper half-plane as a quotient. |
| 2044 | `def` | `MatrixTactics.Iwasawa.Hn_equiv_quotient` | Target equivalence: `Hn`-data is equivalent to `GL / OZ`. Requires the Iwasawa decomposition to exist (`HasIwasawa`). Uses `unique_z_of_two_factorizations` for injectivity and `OZ_subgroup` for the fiber description. |
| 2168 | `def` | `MatrixTactics.Iwasawa.intToReal_GL` | The monoid homomorphism `GL(n, ℤ) →* GL(n, ℝ)` induced by the ring inclusion `ℤ →+* ℝ`. |
| 2176 | `instance` | `MatrixTactics.Iwasawa.GLZ_smul_Hn` | `GL(n, ℤ)` acts on the generalized upper half-plane `Hn.H m` by `γ • z = z`-factor of the Iwasawa decomposition of `γ_ℝ * toGL(z)`. |
| 2252 | `instance` | `MatrixTactics.Iwasawa.GLZ_mulAction_Hn` | `GL(n, ℤ)` acts on the generalized upper half-plane `Hn.H m` (Goldfeld, Proposition 1.2.10). |
| 2264 | `def` | `MatrixTactics.Iwasawa.IsSiegelReduced` | A point `z ∈ Hn` is *Siegel-reduced* with parameter `t > 0` if its diagonal ratios satisfy `y_i ≥ t · y_{i+1}` and its upper-triangular entries satisfy `\\|x_{ij}\\| ≤ 1/2`. This is Goldfeld, Definition 1.2.8. |
| 2270 | `def` | `MatrixTactics.Iwasawa.SiegelSet` | The Siegel set `𝔖_t` for parameter `t`. |
| 2279 | `theorem` | `MatrixTactics.Iwasawa.siegel_fundamental_domain` | **Goldfeld, Theorem 1.2.11**: There exists `t > 0` such that every `GL(n, ℤ)`-orbit on `Hn` meets the Siegel set `𝔖_t`. (Goldfeld takes `t = √3 / 2`.) The proof requires Minkowski reduction theory and is left as a placeholder. |

