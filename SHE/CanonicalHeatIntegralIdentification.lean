module
public import SHE.CanonicalOriginalHeatSums
public import SHE.ConditionalCanonicalItoLimit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
namespace SHE.CanonicalHeatIntegralIdentification
open MeasureTheory Set FiniteHaar DyadicApproximation AddCircle PredictableL2 Filter
open scoped NNReal ENNReal Topology
local instance heatIdentification_unit : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance heatIdentification_circleSecond : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance heatIdentification_realSecond : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance heatIdentification_realSigma : MeasurableSpace RealL2 := borel _
local instance heatIdentification_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance heatIdentification_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance heatIdentification_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable (H : ℝ≥0) (D : SmoothApproximation.ScalarData)
variable (ν : Measure (CanonicalContinuousStateDriver.Space (E:=RealL2) (ι:=HaarNode) H)) [IsProbabilityMeasure ν]
variable (J : StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) (CanonicalStateDriverFiltration.filtration (E:=RealL2) (ι:=HaarNode) H) ν H)
variable (hlocal : StandardTerminalPastLocality J)
variable (hBasis : ∀i (t:ℝ≥0),t≤H→
    (J.integral (StoppedItoInputs.stop (CanonicalStateDriverFiltration.filtration (E:=RealL2) (ι:=HaarNode) H) ν H t
      (RawCylindricalCoordinates.row (CanonicalStateDriverFiltration.filtration (E:=RealL2) (ι:=HaarNode) H) ν H (NativeSingleNoiseBasis.basis: HaarNode→RealHaarInput) i)))=ᵐ[ν] (CanonicalStateDriverFiltration.coordinate (E:=RealL2) (ι:=HaarNode) H) i t)

include hlocal hBasis in
theorem integral_eq (q : ℝ≥0) (hq : q≤H) (ε : ℝ) (hε : 0<ε)
    (x : StoppedFourier.HeatCircle) (n : ℕ) :
    J.integral (OriginalSingleHaarApproximation.approximation (CanonicalStateDriverFiltration.filtration (E:=RealL2) (ι:=HaarNode) H) ν H D (CanonicalStateDriverFiltration.state (E:=RealL2) (ι:=HaarNode) H) (CanonicalStateDriverFiltration.state_predictable (E:=RealL2) (ι:=HaarNode) H) q ε hε x n)=ᵐ[ν]
      CanonicalOriginalHeatSums.value H D q hq ε x n := by
  have hw (i:HaarNode) (t:ℝ≥0) (ht:t≤H) : (CanonicalStateDriverFiltration.coordinate (E:=RealL2) (ι:=HaarNode) H) i t=ᵐ[ν]
      CanonicalScalarItoCells.coordinate H i (CanonicalStateDriverFiltration.filtration (E:=RealL2) (ι:=HaarNode) H) ν J t := by
    filter_upwards [(hBasis i t ht).symm] with r hr
    change _=(J.integral (StoppedItoInputs.stop _ ν H (t:ℝ)
      (RotatedCylindricalCoordinates.constant _ ν H (lp.single 2 i (1:ℝ))))) r
    simpa only [RawCylindricalCoordinates.row,NativeSingleNoiseBasis.basis_apply] using hr
  have he := CanonicalOriginalHeatSums.integral_eq H D q hq ε x (CanonicalStateDriverFiltration.filtration (E:=RealL2) (ι:=HaarNode) H) ν (CanonicalStateDriverFiltration.state (E:=RealL2) (ι:=HaarNode) H)
    (CanonicalStateDriverFiltration.state_continuous H) (CanonicalStateDriverFiltration.state_predictable (E:=RealL2) (ι:=HaarNode) H) J (CanonicalStateDriverFiltration.coordinate (E:=RealL2) (ι:=HaarNode) H)
    (CanonicalStateDriverFiltration.coordinate_continuous H) hε hlocal hw n
  simpa only [CanonicalHeatResidual.bundle_identity] using he

include hlocal hBasis in
/-- A genuine pointwise canonical-sum limit is the SAME actual scalar
Ito integral of the original rough nonlinear row under this measure.
This works on a conditional probability fiber without any SPDE premise. -/
theorem identify (q : ℝ≥0) (hq : q≤H) (ε : ℝ) (hε : 0<ε)
    (x : StoppedFourier.HeatCircle) (ns : ℕ→ℕ) (hns : StrictMono ns)
    (hlim : ∀ᵐr∂ν,Tendsto (fun n=>CanonicalOriginalHeatSums.value H D q hq ε x (ns n) r)
      atTop (𝓝 (CanonicalHeatResidual.value H q ε x r))) :
    CanonicalHeatResidual.value H q ε x=ᵐ[ν]
      J.integral (OriginalNativeWhiteHeatRows.input D (CanonicalStateDriverFiltration.state (E:=RealL2) (ι:=HaarNode) H) (CanonicalStateDriverFiltration.filtration (E:=RealL2) (ι:=HaarNode) H) (CanonicalStateDriverFiltration.state_predictable (E:=RealL2) (ι:=HaarNode) H) ν H q ε hε x) := by
  apply ConditionalCanonicalItoLimit.identify (CanonicalStateDriverFiltration.filtration (E:=RealL2) (ι:=HaarNode) H) ν H J
    (OriginalNativeWhiteHeatRows.input D (CanonicalStateDriverFiltration.state (E:=RealL2) (ι:=HaarNode) H) (CanonicalStateDriverFiltration.filtration (E:=RealL2) (ι:=HaarNode) H) (CanonicalStateDriverFiltration.state_predictable (E:=RealL2) (ι:=HaarNode) H) ν H q ε hε x)
    (fun n=>OriginalSingleHaarApproximation.approximation (CanonicalStateDriverFiltration.filtration (E:=RealL2) (ι:=HaarNode) H) ν H D (CanonicalStateDriverFiltration.state (E:=RealL2) (ι:=HaarNode) H) (CanonicalStateDriverFiltration.state_predictable (E:=RealL2) (ι:=HaarNode) H) q ε hε x (ns n))
    (fun n=>CanonicalOriginalHeatSums.value H D q hq ε x (ns n))
    (CanonicalHeatResidual.value H q ε x)
  · exact (OriginalSingleHaarApproximation.approximation_tendsto (CanonicalStateDriverFiltration.filtration (E:=RealL2) (ι:=HaarNode) H) ν H D (CanonicalStateDriverFiltration.state (E:=RealL2) (ι:=HaarNode) H) (CanonicalStateDriverFiltration.state_predictable (E:=RealL2) (ι:=HaarNode) H) q ε hε x
      (CanonicalStateDriverFiltration.state_continuous H)).comp hns.tendsto_atTop
  · intro n
    exact integral_eq H D ν J hlocal hBasis q hq ε hε x (ns n)
  · exact hlim
end SHE.CanonicalHeatIntegralIdentification
