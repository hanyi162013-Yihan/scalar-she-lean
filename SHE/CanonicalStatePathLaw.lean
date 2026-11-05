module
public import SHE.CanonicalHeatResidual
public import SHE.NativePathLawComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.CanonicalStatePathLaw
open MeasureTheory Set FiniteHaar DyadicApproximation AddCircle
open scoped NNReal
local instance canonicalPath_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance canonicalPath_circleSecond:SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance canonicalPath_realSecond:SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance canonicalPath_realSigma:MeasurableSpace RealL2:=borel _
local instance canonicalPath_realBorel:BorelSpace RealL2:=⟨rfl⟩
variable (H:ℝ≥0)

/-- The continuous trajectory of the actual canonical state process is
exactly the state-path projection, including both endpoints. -/
theorem path_eq : NativeContinuousPath.path H
    (CanonicalStateDriverFiltration.state (E:=RealL2) (ι:=HaarNode) H)
    (CanonicalStateDriverFiltration.state_continuous H)=Prod.fst := by
  funext r
  exact congrArg Prod.fst (CanonicalHeatResidual.bundle_identity H r)

theorem measure_eq (ν:Measure (CanonicalContinuousStateDriver.Space (E:=RealL2) (ι:=HaarNode) H))
    [IsProbabilityMeasure ν] :
    (NativePathLawComparison.law H ν (CanonicalStateDriverFiltration.state H)
      (CanonicalStateDriverFiltration.state_continuous H):Measure _)=ν.map Prod.fst := by
  change ν.map (NativeContinuousPath.path H (CanonicalStateDriverFiltration.state H)
    (CanonicalStateDriverFiltration.state_continuous H))=ν.map Prod.fst
  rw [path_eq H]

/-- Equality of the local canonical state process laws is exactly
equality of the future STATE projections of the joint model measures. -/
theorem projected_eq
    (ν η:Measure (CanonicalContinuousStateDriver.Space (E:=RealL2) (ι:=HaarNode) H))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (he:NativePathLawComparison.law H ν (CanonicalStateDriverFiltration.state H)
        (CanonicalStateDriverFiltration.state_continuous H)=
      NativePathLawComparison.law H η (CanonicalStateDriverFiltration.state H)
        (CanonicalStateDriverFiltration.state_continuous H)) :
    ν.map Prod.fst=η.map Prod.fst := by
  have hm := congrArg (fun p:ProbabilityMeasure C(Icc (0:ℝ) (H:ℝ),RealL2)=>p.toMeasure) he
  simpa only [measure_eq H] using hm
end SHE.CanonicalStatePathLaw
