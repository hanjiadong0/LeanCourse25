import LeanCourse25.Projects.IwasawaDefs
import LeanCourse25.Projects.IwasawaTriangularSolver
import LeanCourse25.Projects.IwasawaHn

open scoped BigOperators Matrix
open Finset
noncomputable section

namespace MatrixTactics

/-! ## Iwasawa decomposition API

This section provides a finished, usable API:
- a structure `IwasawaFactorization` for the datum `(z, k, d)`
- a typeclass `HasIwasawa` that provides the decomposition
- derived lemmas: existence, uniqueness up to sign

The hard part (constructing the instance) is separated so that
one can develop tactics first and later discharge the instance. -/

namespace Iwasawa

variable {m : Nat}

/-- Orthogonal matrices as a subtype (matrix-level). -/
structure O (m : Nat) where
  Q : Mat m
  orth : IsOrthogonal Q

instance : Coe (O m) (Mat m) where
  coe k := k.Q

/-- Scalar center factor: units in `ℝ`. -/
abbrev RUnits := Units ℝ

/-- Map a unit `u : ℝˣ` to the scalar matrix `u • I`. -/
def centerMat (u : RUnits) : Mat m :=
  scalarMat (u : ℝ)

/-- One full factorization datum for Iwasawa. -/
structure IwasawaFactorization (m : Nat) where
  z : Hn.H m
  k : O m
  d : RUnits

/-- Turn factors into the product matrix `z * k * d`. -/
def IwasawaFactorization.toMat {m : Nat}
    (fac : IwasawaFactorization m) : Mat m :=
  (Hn.H.toMat fac.z) * (fac.k : Mat m) *
    centerMat (m := m) fac.d

/-- Concrete `n×n` construction package.

This isolates the algorithmic part of the Iwasawa construction:
for each `g`, provide
- an upper-unipotent solver output `x`,
- a normalized positive diagonal `y`,
- a residual orthogonal matrix `Q`,
- a scalar unit `d`,
and a reconstruction proof `z*Q*d = g`, where `z := (x,y)`.

Once this data is available, the API-level `HasIwasawa` instance is automatic. -/
structure ConcretePipeline (m : Nat) where
  xOf : GLn m → TriangularSolver.UpperUnipotent ℝ m
  yOf : GLn m → Hn.PosDiagNorm m
  qOf : GLn m → Mat m
  qOrth : ∀ g : GLn m, IsOrthogonal (qOf g)
  dOf : GLn m → RUnits
  correct : ∀ g : GLn m,
    let z : Hn.H m :=
      ⟨Hn.UpperUnipotent.ofTriangularSolver (xOf g), yOf g⟩
    z.toMat * qOf g * centerMat (m := m) (dOf g) = (g : Mat m)

namespace ConcretePipeline

/-- The `z`-factor extracted from concrete pipeline data. -/
def zOf {m : Nat} (P : ConcretePipeline m) (g : GLn m) : Hn.H m :=
  ⟨Hn.UpperUnipotent.ofTriangularSolver (P.xOf g), P.yOf g⟩

/-- The full factorization extracted from concrete pipeline data. -/
def facOf {m : Nat} (P : ConcretePipeline m) (g : GLn m) :
    IwasawaFactorization m :=
  ⟨zOf P g, ⟨P.qOf g, P.qOrth g⟩, P.dOf g⟩

/-- Correctness of the packaged factorization. -/
theorem facOf_correct {m : Nat} (P : ConcretePipeline m) (g : GLn m) :
    (facOf P g).toMat = (g : Mat m) := by
  simpa [facOf, zOf, IwasawaFactorization.toMat] using P.correct g

/-- Raw witness package extracted from a concrete pipeline at one matrix `g`. -/
theorem rawWitness {m : Nat} (P : ConcretePipeline m) (g : GLn m) :
    ∃ x : TriangularSolver.UpperUnipotent ℝ m,
    ∃ y : Hn.PosDiagNorm m,
    ∃ Q : Mat m,
    ∃ d : RUnits,
      IsOrthogonal Q ∧
      ((⟨Hn.UpperUnipotent.ofTriangularSolver x, y⟩ : Hn.H m).toMat *
        Q * centerMat (m := m) d = (g : Mat m)) := by
  refine ⟨P.xOf g, P.yOf g, P.qOf g, P.dOf g, P.qOrth g, ?_⟩
  simpa using P.correct g

/-- Build a concrete pipeline from raw witness extraction.

This is the direct constructor to use once you have explicit formulas
for `(x,y,Q,d)` (possibly produced from Schur-complement recursion). -/
noncomputable def ofRaw {m : Nat}
    (raw : ∀ g : GLn m,
      ∃ x : TriangularSolver.UpperUnipotent ℝ m,
      ∃ y : Hn.PosDiagNorm m,
      ∃ Q : Mat m,
      ∃ d : RUnits,
        IsOrthogonal Q ∧
        ((⟨Hn.UpperUnipotent.ofTriangularSolver x, y⟩ : Hn.H m).toMat *
          Q * centerMat (m := m) d = (g : Mat m))) :
    ConcretePipeline m := by
  classical
  choose x y Q d hQ hcorr using raw
  refine
    { xOf := x
      yOf := y
      qOf := Q
      qOrth := hQ
      dOf := d
      correct := ?_ }
  intro g
  simpa using hcorr g

/-- Concrete existence theorem (`n×n`) without typeclass search. -/
theorem exists_factorization_of_pipeline
    {m : Nat} (P : ConcretePipeline m) (g : GLn m) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) := by
  exact ⟨facOf P g, facOf_correct P g⟩

/-- Recursive constructor for concrete pipelines.

`base` provides the `2×2` pipeline.
`step n` builds the `(n+3)` pipeline from:
- the `(n+3)` triangular solver,
- the previously-built `(n+2)` pipeline. -/
structure RecursiveMkPipeline where
  base : ConcretePipeline 2
  step : ∀ n,
    TriangularSolver.SolveRightSpec ℝ (n + 3) →
      ConcretePipeline (n + 2) →
      ConcretePipeline (n + 3)

namespace RecursiveMkPipeline

/-- Family of pipelines built by recursion from `base` and `step`. -/
def family (R : RecursiveMkPipeline)
    (S : TriangularSolver.RecursiveSolveRight ℝ) :
    ∀ n, ConcretePipeline (n + 2)
  | 0 => R.base
  | n + 1 => R.step n (S.family (n + 1)) (family R S n)

@[simp]
lemma family_zero (R : RecursiveMkPipeline)
    (S : TriangularSolver.RecursiveSolveRight ℝ) :
    R.family S 0 = R.base := rfl

@[simp]
lemma family_succ (R : RecursiveMkPipeline)
    (S : TriangularSolver.RecursiveSolveRight ℝ) (n : Nat) :
    R.family S (n + 1) =
      R.step n (S.family (n + 1)) (R.family S n) := rfl

end RecursiveMkPipeline

/-- Build concrete Iwasawa pipelines by induction on the dimension (`m = n+2`). -/
structure RecursiveConcretePipeline where
  base : ConcretePipeline 2
  step : ∀ n, ConcretePipeline (n + 2) →
    ConcretePipeline (n + 3)

namespace RecursiveConcretePipeline

/-- Family of pipelines produced recursively. -/
def family (R : RecursiveConcretePipeline) :
    ∀ n, ConcretePipeline (n + 2) :=
  fun
    | 0 => R.base
    | n + 1 => R.step n (family R n)

/-- Access a concrete pipeline at any dimension `m ≥ 2`. -/
def atDim (R : RecursiveConcretePipeline) {m : Nat} (hm : 2 ≤ m) :
    ConcretePipeline m := by
  have hm' : (m - 2) + 2 = m := by omega
  simpa [hm', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    R.family (m - 2)

@[simp]
lemma atDim_two (R : RecursiveConcretePipeline) :
    R.atDim (m := 2) (by omega) = R.base := by
  unfold atDim family
  simp

/-- Existence theorem at any size `m ≥ 2`, obtained by recursive pipeline construction. -/
theorem exists_factorization_ge2
    (R : RecursiveConcretePipeline)
    {m : Nat} (hm : 2 ≤ m) (g : GLn m) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) := by
  exact exists_factorization_of_pipeline (P := R.atDim hm) g

end RecursiveConcretePipeline

/-- Bridge from the recursive triangular-solver algorithm to concrete
Iwasawa pipelines.

`mkPipeline n` is the algorithmic "Gram + residual orthogonal + scalar"
packaging step that turns a solver at size `n+2` into the corresponding
concrete Iwasawa pipeline at size `n+2`. -/
structure FromTriangularSolver where
  solver : TriangularSolver.RecursiveSolveRight ℝ
  mkPipeline : ∀ n,
    TriangularSolver.SolveRightSpec ℝ (n + 2) →
      ConcretePipeline (n + 2)

namespace FromTriangularSolver

/-- Pipeline family induced by recursive solver family. -/
def pipelineFamily (C : FromTriangularSolver) :
    ∀ n, ConcretePipeline (n + 2) :=
  fun n => C.mkPipeline n (C.solver.family n)

/-- Concrete `mkPipeline` implementation from recursive base+step data. -/
def ofRecursiveMkPipeline
    (solver : TriangularSolver.RecursiveSolveRight ℝ)
    (R : RecursiveMkPipeline) :
    FromTriangularSolver where
  solver := solver
  mkPipeline := fun n _ => R.family solver n

@[simp]
lemma ofRecursiveMkPipeline_pipelineFamily
    (solver : TriangularSolver.RecursiveSolveRight ℝ)
    (R : RecursiveMkPipeline) (n : Nat) :
    (ofRecursiveMkPipeline solver R).pipelineFamily n =
      R.family solver n := rfl

/-- Step data for building concrete pipelines directly from raw witnesses. -/
structure RawMkPipeline where
  baseRaw : ∀ g : GLn 2,
    ∃ x : TriangularSolver.UpperUnipotent ℝ 2,
    ∃ y : Hn.PosDiagNorm 2,
    ∃ Q : Mat 2,
    ∃ d : RUnits,
      IsOrthogonal Q ∧
      ((⟨Hn.UpperUnipotent.ofTriangularSolver x, y⟩ : Hn.H 2).toMat *
        Q * centerMat (m := 2) d = (g : Mat 2))
  stepRaw : ∀ n,
    TriangularSolver.SolveRightSpec ℝ (n + 3) →
      ConcretePipeline (n + 2) →
      (∀ g : GLn (n + 3),
        ∃ x : TriangularSolver.UpperUnipotent ℝ (n + 3),
        ∃ y : Hn.PosDiagNorm (n + 3),
        ∃ Q : Mat (n + 3),
        ∃ d : RUnits,
          IsOrthogonal Q ∧
          ((⟨Hn.UpperUnipotent.ofTriangularSolver x, y⟩ : Hn.H (n + 3)).toMat *
            Q * centerMat (m := n + 3) d = (g : Mat (n + 3))))

namespace RawMkPipeline

/-- Build raw witness formulas from an already-defined recursive
pipeline builder. This removes separate existential proof plumbing
for `baseRaw/stepRaw`. -/
noncomputable def fromRecursiveMkPipeline
    (R : RecursiveMkPipeline) : RawMkPipeline where
  baseRaw := fun g => ConcretePipeline.rawWitness (P := R.base) g
  stepRaw := fun n s p g =>
    ConcretePipeline.rawWitness (P := R.step n s p) g

/-- Build raw witness formulas directly from a `FromTriangularSolver`
object by reusing its `mkPipeline` outputs. -/
noncomputable def fromFromTriangularSolver
    (C : FromTriangularSolver) : RawMkPipeline where
  baseRaw := fun g => ConcretePipeline.rawWitness (P := C.pipelineFamily 0) g
  stepRaw := fun n s _p g =>
    ConcretePipeline.rawWitness (P := C.mkPipeline (n + 1) s) g

/-- Turn raw step formulas into the recursive pipeline builder. -/
noncomputable def toRecursiveMkPipeline
    (R : RawMkPipeline) : RecursiveMkPipeline where
  base := ConcretePipeline.ofRaw (m := 2) R.baseRaw
  step := fun n s p => ConcretePipeline.ofRaw (m := n + 3) (R.stepRaw n s p)

/-- Build a full `FromTriangularSolver` object from:
- recursive solver family,
- raw base+step witness formulas. -/
noncomputable def toFromTriangularSolver
    (solver : TriangularSolver.RecursiveSolveRight ℝ)
    (R : RawMkPipeline) :
    FromTriangularSolver :=
  ofRecursiveMkPipeline solver R.toRecursiveMkPipeline

end RawMkPipeline

/-- A recursive concrete pipeline extracted from solver recursion. -/
def toRecursiveConcretePipeline
    (C : FromTriangularSolver) :
    RecursiveConcretePipeline where
  base := C.pipelineFamily 0
  step := fun n _ => C.pipelineFamily (n + 1)

/-- Raw Goldfeld-style existence (`z,k,d`) for all `m ≥ 2`, obtained
from recursive triangular solvers plus the pipeline packaging step. -/
theorem exists_raw_ge2
    (C : FromTriangularSolver)
    {m : Nat} (hm : 2 ≤ m) (g : GLn m) :
    ∃ z : Hn.H m, ∃ k : O m, ∃ d : RUnits,
      z.toMat * (k : Mat m) * centerMat (m := m) d = (g : Mat m) := by
  let P : ConcretePipeline m :=
    (C.toRecursiveConcretePipeline).atDim hm
  refine ⟨zOf P g, ⟨P.qOf g, P.qOrth g⟩, P.dOf g, ?_⟩
  simpa [zOf] using P.correct g

/-- Structured factorization existence (`IwasawaFactorization`) for all `m ≥ 2`. -/
theorem exists_factorization_ge2
    (C : FromTriangularSolver)
    {m : Nat} (hm : 2 ≤ m) (g : GLn m) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) := by
  exact RecursiveConcretePipeline.exists_factorization_ge2
    (R := C.toRecursiveConcretePipeline) hm g

/-- `exists_raw_ge2` with the lower-bound packaged as a typeclass fact. -/
theorem exists_raw_fact
    (C : FromTriangularSolver)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ z : Hn.H m, ∃ k : O m, ∃ d : RUnits,
      z.toMat * (k : Mat m) * centerMat (m := m) d = (g : Mat m) :=
  C.exists_raw_ge2 (m := m) Fact.out g

/-- `exists_factorization_ge2` with the lower-bound packaged as a typeclass fact. -/
theorem exists_factorization_fact
    (C : FromTriangularSolver)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) :=
  C.exists_factorization_ge2 (m := m) Fact.out g

end FromTriangularSolver

end ConcretePipeline

/-- Full constructive package for Goldfeld Prop. 1.2.6 core.

To instantiate:
1. fill the base `2×2` solver,
2. fill Schur-complement recursion data (`n+2 → n+3`),
3. fill recursive pipeline builder (`x,y,Q,d` from solver data).

Everything else (global existence and typeclass-level packaging) is derived. -/
structure ConstructiveCore where
  solverBase : TriangularSolver.SolveRightSpec ℝ 2
  solverSchur : ∀ n, TriangularSolver.SchurStep ℝ n
  pipelineBuilder : ConcretePipeline.RecursiveMkPipeline

namespace ConstructiveCore

/-- Recursive solver obtained from base + Schur-step data. -/
def solverRec (C : ConstructiveCore) :
    TriangularSolver.RecursiveSolveRight ℝ :=
  TriangularSolver.recursiveSolveRightOfSchur
    C.solverBase C.solverSchur

/-- Bridge object giving concrete Iwasawa pipelines from recursive solver data. -/
def bridge (C : ConstructiveCore) :
    ConcretePipeline.FromTriangularSolver :=
  ConcretePipeline.FromTriangularSolver.ofRecursiveMkPipeline
    (solver := C.solverRec) (R := C.pipelineBuilder)

/-- Build a `ConstructiveCore` directly from raw pipeline witness formulas. -/
noncomputable def ofRaw
    (solverBase : TriangularSolver.SolveRightSpec ℝ 2)
    (solverSchur : ∀ n, TriangularSolver.SchurStep ℝ n)
    (raw : ConcretePipeline.FromTriangularSolver.RawMkPipeline) :
    ConstructiveCore where
  solverBase := solverBase
  solverSchur := solverSchur
  pipelineBuilder := raw.toRecursiveMkPipeline

/-- Build `ConstructiveCore` from:
- base `2×2` solver,
- explicit Schur completion formula `complete` (checked at each step),
- raw pipeline witness formulas. -/
noncomputable def ofPrincipalChecked
    (solverBase : TriangularSolver.SolveRightSpec ℝ 2)
    (complete : ∀ n,
      TriangularSolver.Matα ℝ (n + 3) →
        TriangularSolver.Matα ℝ (n + 3) →
        TriangularSolver.UpperUnipotent ℝ (n + 2) →
          TriangularSolver.UpperUnipotent ℝ (n + 3))
    (raw : ConcretePipeline.FromTriangularSolver.RawMkPipeline) :
    ConstructiveCore :=
  ofRaw solverBase
    (fun n =>
      TriangularSolver.schurStepPrincipalChecked (α := ℝ) (complete n))
    raw

/-- Choice of checked Schur completion strategy used by `ConstructiveCore`. -/
inductive CheckedFlavor where
  | pad
  | nonsingInv

/-- Schur-step family corresponding to a checked strategy. -/
noncomputable def checkedSchur (fl : CheckedFlavor) :
    ∀ n, TriangularSolver.SchurStep ℝ n
  | n =>
    match fl with
    | .pad => TriangularSolver.schurStepPadChecked (α := ℝ) (n := n)
    | .nonsingInv =>
        TriangularSolver.schurStepPrincipalNonsingInvChecked
          (α := ℝ) (n := n)

/-- Generic checked constructor from raw witness packaging data. -/
noncomputable def ofChecked
    (fl : CheckedFlavor)
    (raw : ConcretePipeline.FromTriangularSolver.RawMkPipeline) :
    ConstructiveCore :=
  ofRaw TriangularSolver.solveRight2Real (checkedSchur fl) raw

/-- Generic checked constructor where raw witnesses are derived
from a recursive pipeline builder. -/
noncomputable def ofCheckedFromRecursive
    (fl : CheckedFlavor)
    (R : ConcretePipeline.RecursiveMkPipeline) : ConstructiveCore :=
  ofChecked fl
    (raw := ConcretePipeline.FromTriangularSolver.RawMkPipeline.fromRecursiveMkPipeline R)

/-- Generic checked constructor where raw witnesses are derived
from a `FromTriangularSolver` bridge object. -/
noncomputable def ofCheckedFromFromTriangularSolver
    (fl : CheckedFlavor)
    (C : ConcretePipeline.FromTriangularSolver) : ConstructiveCore :=
  ofChecked fl
    (raw := ConcretePipeline.FromTriangularSolver.RawMkPipeline.fromFromTriangularSolver C)

/-- Specialized checked constructor using the principal padding step. -/
noncomputable def ofPadChecked
    (raw : ConcretePipeline.FromTriangularSolver.RawMkPipeline) :
    ConstructiveCore :=
  ofChecked .pad raw

/-- Specialized checked constructor using the principal `nonsingInv`
completion step. -/
noncomputable def ofNonsingInvChecked
    (raw : ConcretePipeline.FromTriangularSolver.RawMkPipeline) :
    ConstructiveCore :=
  ofChecked .nonsingInv raw

/-- `ofPadChecked` where raw witnesses are auto-derived from an existing
recursive pipeline builder. -/
noncomputable def ofPadCheckedFromRecursive
    (R : ConcretePipeline.RecursiveMkPipeline) : ConstructiveCore :=
  ofCheckedFromRecursive .pad R

/-- `ofNonsingInvChecked` where raw witnesses are auto-derived from an
existing recursive pipeline builder. -/
noncomputable def ofNonsingInvCheckedFromRecursive
    (R : ConcretePipeline.RecursiveMkPipeline) : ConstructiveCore :=
  ofCheckedFromRecursive .nonsingInv R

/-- `ofPadChecked` where raw witnesses are auto-derived from an existing
`FromTriangularSolver` bridge object. -/
noncomputable def ofPadCheckedFromFromTriangularSolver
    (C : ConcretePipeline.FromTriangularSolver) : ConstructiveCore :=
  ofCheckedFromFromTriangularSolver .pad C

/-- `ofNonsingInvChecked` where raw witnesses are auto-derived from an existing
`FromTriangularSolver` bridge object. -/
noncomputable def ofNonsingInvCheckedFromFromTriangularSolver
    (C : ConcretePipeline.FromTriangularSolver) : ConstructiveCore :=
  ofCheckedFromFromTriangularSolver .nonsingInv C

/-- Raw Goldfeld-style existence (`z,k,d`) for all `m ≥ 2`. -/
theorem exists_raw_ge2 (C : ConstructiveCore)
    {m : Nat} (hm : 2 ≤ m) (g : GLn m) :
    ∃ z : Hn.H m, ∃ k : O m, ∃ d : RUnits,
      z.toMat * (k : Mat m) * centerMat (m := m) d = (g : Mat m) :=
  C.bridge.exists_raw_ge2 hm g

/-- Structured factorization existence for all `m ≥ 2`. -/
theorem exists_factorization_ge2 (C : ConstructiveCore)
    {m : Nat} (hm : 2 ≤ m) (g : GLn m) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) :=
  C.bridge.exists_factorization_ge2 hm g

/-- Structured factorization existence using `[Fact (2 ≤ m)]`. -/
theorem exists_factorization_fact (C : ConstructiveCore)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) :=
  C.bridge.exists_factorization_fact g

/-- Raw existence using `[Fact (2 ≤ m)]`. -/
theorem exists_raw_fact (C : ConstructiveCore)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ z : Hn.H m, ∃ k : O m, ∃ d : RUnits,
      z.toMat * (k : Mat m) * centerMat (m := m) d = (g : Mat m) :=
  C.bridge.exists_raw_fact g

/-- Generic all-`n` factorization theorem from checked constructor
plus raw witness packaging data. -/
theorem exists_factorization_ofChecked
    (fl : CheckedFlavor)
    (raw : ConcretePipeline.FromTriangularSolver.RawMkPipeline)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) :=
  (ofChecked fl raw).exists_factorization_fact g

/-- Generic all-`n` raw existence theorem from checked constructor
plus raw witness packaging data. -/
theorem exists_raw_ofChecked
    (fl : CheckedFlavor)
    (raw : ConcretePipeline.FromTriangularSolver.RawMkPipeline)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ z : Hn.H m, ∃ k : O m, ∃ d : RUnits,
      z.toMat * (k : Mat m) * centerMat (m := m) d = (g : Mat m) :=
  (ofChecked fl raw).exists_raw_fact g

/-- Generic all-`n` factorization theorem from a recursive pipeline builder. -/
theorem exists_factorization_ofCheckedFromRecursive
    (fl : CheckedFlavor)
    (R : ConcretePipeline.RecursiveMkPipeline)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) :=
  (ofCheckedFromRecursive fl R).exists_factorization_fact g

/-- Generic all-`n` raw existence theorem from a recursive pipeline builder. -/
theorem exists_raw_ofCheckedFromRecursive
    (fl : CheckedFlavor)
    (R : ConcretePipeline.RecursiveMkPipeline)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ z : Hn.H m, ∃ k : O m, ∃ d : RUnits,
      z.toMat * (k : Mat m) * centerMat (m := m) d = (g : Mat m) :=
  (ofCheckedFromRecursive fl R).exists_raw_fact g

/-- Generic all-`n` factorization theorem from a `FromTriangularSolver` bridge. -/
theorem exists_factorization_ofCheckedFromFromTriangularSolver
    (fl : CheckedFlavor)
    (C : ConcretePipeline.FromTriangularSolver)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) :=
  (ofCheckedFromFromTriangularSolver fl C).exists_factorization_fact g

/-- Generic all-`n` raw existence theorem from a `FromTriangularSolver` bridge. -/
theorem exists_raw_ofCheckedFromFromTriangularSolver
    (fl : CheckedFlavor)
    (C : ConcretePipeline.FromTriangularSolver)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ z : Hn.H m, ∃ k : O m, ∃ d : RUnits,
      z.toMat * (k : Mat m) * centerMat (m := m) d = (g : Mat m) :=
  (ofCheckedFromFromTriangularSolver fl C).exists_raw_fact g

/-- Direct all-`n` factorization theorem from the padding checked core
constructor plus raw witness packaging data. -/
theorem exists_factorization_ofPadChecked
    (raw : ConcretePipeline.FromTriangularSolver.RawMkPipeline)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) :=
  exists_factorization_ofChecked .pad raw g

/-- Direct all-`n` raw existence theorem from the padding checked core
constructor plus raw witness packaging data. -/
theorem exists_raw_ofPadChecked
    (raw : ConcretePipeline.FromTriangularSolver.RawMkPipeline)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ z : Hn.H m, ∃ k : O m, ∃ d : RUnits,
      z.toMat * (k : Mat m) * centerMat (m := m) d = (g : Mat m) :=
  exists_raw_ofChecked .pad raw g

/-- Direct all-`n` factorization theorem from the principal
`nonsingInv` checked core constructor plus raw witness packaging data. -/
theorem exists_factorization_ofNonsingInvChecked
    (raw : ConcretePipeline.FromTriangularSolver.RawMkPipeline)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) :=
  exists_factorization_ofChecked .nonsingInv raw g

/-- Direct all-`n` raw existence theorem from the principal
`nonsingInv` checked core constructor plus raw witness packaging data. -/
theorem exists_raw_ofNonsingInvChecked
    (raw : ConcretePipeline.FromTriangularSolver.RawMkPipeline)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ z : Hn.H m, ∃ k : O m, ∃ d : RUnits,
      z.toMat * (k : Mat m) * centerMat (m := m) d = (g : Mat m) :=
  exists_raw_ofChecked .nonsingInv raw g

/-- Direct all-`n` factorization theorem from a recursive pipeline builder,
using the padding checked solver recursion. -/
theorem exists_factorization_ofPadCheckedFromRecursive
    (R : ConcretePipeline.RecursiveMkPipeline)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) :=
  exists_factorization_ofCheckedFromRecursive .pad R g

/-- Direct all-`n` raw existence theorem from a recursive pipeline builder,
using the padding checked solver recursion. -/
theorem exists_raw_ofPadCheckedFromRecursive
    (R : ConcretePipeline.RecursiveMkPipeline)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ z : Hn.H m, ∃ k : O m, ∃ d : RUnits,
      z.toMat * (k : Mat m) * centerMat (m := m) d = (g : Mat m) :=
  exists_raw_ofCheckedFromRecursive .pad R g

/-- Direct all-`n` factorization theorem from a recursive pipeline builder,
using the principal `nonsingInv` checked solver recursion. -/
theorem exists_factorization_ofNonsingInvCheckedFromRecursive
    (R : ConcretePipeline.RecursiveMkPipeline)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) :=
  exists_factorization_ofCheckedFromRecursive .nonsingInv R g

/-- Direct all-`n` raw existence theorem from a recursive pipeline builder,
using the principal `nonsingInv` checked solver recursion. -/
theorem exists_raw_ofNonsingInvCheckedFromRecursive
    (R : ConcretePipeline.RecursiveMkPipeline)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ z : Hn.H m, ∃ k : O m, ∃ d : RUnits,
      z.toMat * (k : Mat m) * centerMat (m := m) d = (g : Mat m) :=
  exists_raw_ofCheckedFromRecursive .nonsingInv R g

/-- Direct all-`n` factorization theorem from a `FromTriangularSolver` bridge,
using the padding checked solver recursion. -/
theorem exists_factorization_ofPadCheckedFromFromTriangularSolver
    (C : ConcretePipeline.FromTriangularSolver)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) :=
  exists_factorization_ofCheckedFromFromTriangularSolver .pad C g

/-- Direct all-`n` raw existence theorem from a `FromTriangularSolver` bridge,
using the padding checked solver recursion. -/
theorem exists_raw_ofPadCheckedFromFromTriangularSolver
    (C : ConcretePipeline.FromTriangularSolver)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ z : Hn.H m, ∃ k : O m, ∃ d : RUnits,
      z.toMat * (k : Mat m) * centerMat (m := m) d = (g : Mat m) :=
  exists_raw_ofCheckedFromFromTriangularSolver .pad C g

/-- Direct all-`n` factorization theorem from a `FromTriangularSolver` bridge,
using the principal `nonsingInv` checked solver recursion. -/
theorem exists_factorization_ofNonsingInvCheckedFromFromTriangularSolver
    (C : ConcretePipeline.FromTriangularSolver)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) :=
  exists_factorization_ofCheckedFromFromTriangularSolver .nonsingInv C g

/-- Direct all-`n` raw existence theorem from a `FromTriangularSolver` bridge,
using the principal `nonsingInv` checked solver recursion. -/
theorem exists_raw_ofNonsingInvCheckedFromFromTriangularSolver
    (C : ConcretePipeline.FromTriangularSolver)
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ z : Hn.H m, ∃ k : O m, ∃ d : RUnits,
      z.toMat * (k : Mat m) * centerMat (m := m) d = (g : Mat m) :=
  exists_raw_ofCheckedFromFromTriangularSolver .nonsingInv C g

end ConstructiveCore

/-- Typeclass: existence of an Iwasawa decomposition for
`GL(m, ℝ)`. Isolates the existence proof from downstream
development. -/
class HasIwasawa (m : Nat) where
  iwasawa : GLn m → IwasawaFactorization m
  correct : ∀ g : GLn m,
    (iwasawa g).toMat = (g : Mat m)

/-- Existence theorem (immediate from the class). -/
theorem exists_factorization [HasIwasawa m] (g : GLn m) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) := by
  refine ⟨HasIwasawa.iwasawa (m := m) g, ?_⟩
  simpa using HasIwasawa.correct (m := m) g

namespace ConcretePipeline

/-- Any concrete pipeline induces a `HasIwasawa` instance. -/
def toHasIwasawa {m : Nat} (P : ConcretePipeline m) : HasIwasawa m where
  iwasawa := facOf P
  correct := facOf_correct P

namespace FromTriangularSolver

/-- `HasIwasawa` produced from the recursive triangular-solver construction
at a fixed dimension `m ≥ 2`. -/
def toHasIwasawa
    (C : ConcretePipeline.FromTriangularSolver)
    {m : Nat} (hm : 2 ≤ m) : HasIwasawa m :=
  ConcretePipeline.toHasIwasawa
    (P := (C.toRecursiveConcretePipeline).atDim hm)

/-- Convenience form using a `Fact` assumption for `m ≥ 2`. -/
def toHasIwasawaFact
    (C : ConcretePipeline.FromTriangularSolver)
    {m : Nat} [Fact (2 ≤ m)] : HasIwasawa m :=
  C.toHasIwasawa (m := m) Fact.out

end FromTriangularSolver

end ConcretePipeline

namespace ConstructiveCore

/-- `HasIwasawa` from the full constructive package at a fixed `m ≥ 2`. -/
def toHasIwasawa (C : ConstructiveCore)
    {m : Nat} (hm : 2 ≤ m) : HasIwasawa m :=
  ConcretePipeline.FromTriangularSolver.toHasIwasawa
    (C := C.bridge) hm

/-- `HasIwasawa` from the full constructive package using `[Fact (2 ≤ m)]`. -/
def toHasIwasawaFact (C : ConstructiveCore)
    {m : Nat} [Fact (2 ≤ m)] : HasIwasawa m :=
  ConcretePipeline.FromTriangularSolver.toHasIwasawaFact
    (C := C.bridge)

/-- `HasIwasawa` packaged from a recursive pipeline builder via a
chosen checked solver recursion flavor. -/
noncomputable def toHasIwasawaFact_ofCheckedFromRecursive
    (fl : CheckedFlavor)
    (R : ConcretePipeline.RecursiveMkPipeline)
    {m : Nat} [Fact (2 ≤ m)] : HasIwasawa m :=
  (ofCheckedFromRecursive fl R).toHasIwasawaFact

/-- `HasIwasawa` packaged from a `FromTriangularSolver` bridge via a
chosen checked solver recursion flavor. -/
noncomputable def toHasIwasawaFact_ofCheckedFromFromTriangularSolver
    (fl : CheckedFlavor)
    (C : ConcretePipeline.FromTriangularSolver)
    {m : Nat} [Fact (2 ≤ m)] : HasIwasawa m :=
  (ofCheckedFromFromTriangularSolver fl C).toHasIwasawaFact

/-- `HasIwasawa` packaged from a recursive pipeline builder via
padding-checked solver recursion. -/
noncomputable def toHasIwasawaFact_ofPadCheckedFromRecursive
    (R : ConcretePipeline.RecursiveMkPipeline)
    {m : Nat} [Fact (2 ≤ m)] : HasIwasawa m :=
  toHasIwasawaFact_ofCheckedFromRecursive .pad R

/-- `HasIwasawa` packaged from a recursive pipeline builder via
principal-`nonsingInv` checked solver recursion. -/
noncomputable def toHasIwasawaFact_ofNonsingInvCheckedFromRecursive
    (R : ConcretePipeline.RecursiveMkPipeline)
    {m : Nat} [Fact (2 ≤ m)] : HasIwasawa m :=
  toHasIwasawaFact_ofCheckedFromRecursive .nonsingInv R

end ConstructiveCore

/-- Register one global constructive core for all dimensions.

This packages the remaining construction data as a single global instance;
after installing it, Iwasawa existence theorems depend only on `g`
(and the dimension side-condition `2 ≤ m`). -/
class HasConstructiveCore where
  core : ConstructiveCore

/-- Register one concrete algorithmic bridge (`FromTriangularSolver`).

From this single object we derive a global `ConstructiveCore`
via the principal `nonsingInv` checked constructor. -/
class HasFromTriangularSolver where
  bridge : ConcretePipeline.FromTriangularSolver

namespace HasFromTriangularSolver

/-- The constructive core induced by the registered bridge. -/
noncomputable def constructiveCore [HasFromTriangularSolver] :
    ConstructiveCore :=
  ConstructiveCore.ofNonsingInvCheckedFromFromTriangularSolver
    HasFromTriangularSolver.bridge

/-- Any registered bridge gives a global constructive core instance. -/
noncomputable instance toHasConstructiveCore [HasFromTriangularSolver] :
    HasConstructiveCore where
  core := constructiveCore

end HasFromTriangularSolver

namespace HasConstructiveCore

/-- Canonical `HasIwasawa` instance induced by a registered constructive core. -/
noncomputable instance hasIwasawaFact
    [HasConstructiveCore] {m : Nat} [Fact (2 ≤ m)] : HasIwasawa m :=
  (HasConstructiveCore.core).toHasIwasawaFact

/-- Raw Goldfeld-style existence from the registered constructive core. -/
theorem exists_raw_fact [HasConstructiveCore]
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ z : Hn.H m, ∃ k : O m, ∃ d : RUnits,
      z.toMat * (k : Mat m) * centerMat (m := m) d = (g : Mat m) :=
  (HasConstructiveCore.core).exists_raw_fact g

/-- Structured factorization existence from the registered constructive core. -/
theorem exists_factorization_fact [HasConstructiveCore]
    {m : Nat} [Fact (2 ≤ m)] (g : GLn m) :
    ∃ fac : IwasawaFactorization m,
      fac.toMat = (g : Mat m) :=
  (HasConstructiveCore.core).exists_factorization_fact g

end HasConstructiveCore

end Iwasawa

end MatrixTactics
