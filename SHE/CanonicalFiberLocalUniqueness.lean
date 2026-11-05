module
public import SHE.GivenSingleNativeArbitraryLocalUniqueness
public import SHE.CanonicalStatePathLaw
public import SHE.NativeWhiteToPhysicalEquation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
namespace SHE.CanonicalFiberLocalUniqueness
open MeasureTheory PredictableL2 FiniteHaar DyadicApproximation
open scoped NNReal ENNReal
local instance fiberLocal_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance fiberLocal_circleSecond:SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance fiberLocal_realSecond:SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance fiberLocal_realSigma:MeasurableSpace RealL2:=borel _
local instance fiberLocal_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance fiberLocal_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance fiberLocal_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
abbrev Space(H:ℝ≥0):=CanonicalContinuousStateDriver.Space (E:=RealL2) (ι:=HaarNode) H
abbrev filtration(H:ℝ≥0):=CanonicalStateDriverFiltration.filtration (E:=RealL2) (ι:=HaarNode) H
abbrev state(H:ℝ≥0):=CanonicalStateDriverFiltration.state (E:=RealL2) (ι:=HaarNode) H
variable{ι:Type}[Fintype ι]
variable(H:ℝ≥0)(D:SmoothApproximation.ScalarData)
variable(ν:ι→Measure (Space H))[∀i,IsProbabilityMeasure (ν i)]
variable(K:∀i,StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) (filtration H) (ν i) H)
variable(u₀:RealL2)
variable(M:∀i,SingleNativeHeatEquation.Data (filtration H) (ν i) H D
  (NativeWhiteToPhysicalEquation.physical (filtration H) (ν i) H (K i)) u₀)

/-- Actual local uniqueness for the canonical state models implies
equality of the future STATE marginals. The joint driver measures may
differ; the proof uses the supplied physical models and ordinary inputs
rather than a weak-uniqueness premise. -/
theorem state_laws_eq(hH:0<H)(hH1:(H:ℝ)≤1)
    (hM:∀i,(M i).value=state H)
    (A:GivenSingleNativeArbitraryLocalUniqueness.Inputs (fun _ : ι=>Space H)
      (fun _=>filtration H) ν H D
      (fun i=>NativeWhiteToPhysicalEquation.physical (filtration H) (ν i) H (K i)) u₀ M):
    ∀i j:ι,(ν i).map Prod.fst=(ν j).map Prod.fst:=by
  have he:=GivenSingleNativeArbitraryLocalUniqueness.laws_eq
    (fun _ : ι=>Space H) (fun _=>filtration H) ν H D
    (fun i=>NativeWhiteToPhysicalEquation.physical (filtration H) (ν i) H (K i)) u₀ M hH hH1 A
  intro i j
  apply CanonicalStatePathLaw.projected_eq H (ν i) (ν j)
  simpa only [hM i,hM j] using he i j
end SHE.CanonicalFiberLocalUniqueness
