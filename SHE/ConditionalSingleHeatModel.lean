module
public import SHE.RandomInitialSingleWhiteEquation
public import SHE.ConditionalOriginalHeatEquations
public import SHE.ConditionalInitialState
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
namespace SHE.ConditionalSingleHeatModel
open MeasureTheory ProbabilityTheory Set PredictableL2 FiniteHaar DyadicApproximation
open OriginalNativeCountableEquationCompletion
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory
local instance conditionalSingle_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance conditionalSingle_circleSecond:SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=1)).repr.toHomeomorph.secondCountableTopology
local instance conditionalSingle_realSecond:SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance conditionalSingle_realSigma:MeasurableSpace RealL2:=borel _
local instance conditionalSingle_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance conditionalSingle_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance conditionalSingle_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
abbrev Space(H:ℝ≥0):=CanonicalContinuousStateDriver.Space (E:=RealL2) (ι:=HaarNode) H
abbrev filtration(H:ℝ≥0):=CanonicalStateDriverFiltration.filtration (E:=RealL2) (ι:=HaarNode) H
abbrev state(H:ℝ≥0):=CanonicalStateDriverFiltration.state (E:=RealL2) (ι:=HaarNode) H
variable {Ω P:Type*}[MeasurableSpace Ω][MeasurableSpace P]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(D:SmoothApproximation.ScalarData)(J:StandardTerminalIto (C:=RealL2) (E:=ℝ) 𝓕 μ H)
variable(ξ:Ω→RealL2)(S:RandomInitialSingleHeatEquation.Data 𝓕 μ H D J ξ)
variable(W:HaarNode→ℝ≥0→Ω→ℝ)(hd:∀i ω,Continuous (fun t=>W i t ω))
variable(Z:Ω→P)

def bundle:Ω→Space H:=CanonicalContinuousStateDriver.bundle H S.value S.continuous W hd

def kernel:Kernel P (Space H):=condDistrib (bundle 𝓕 μ H D J ξ S W hd) Z μ

instance kernel_probability(p:P):IsProbabilityMeasure (kernel 𝓕 μ H D J ξ S W hd Z p):=by
  unfold kernel
  infer_instance

/-- On one genuine prefix event, every actual recognized conditional
white integral yields the supplied deterministic-initial single-noise
heat-observed model. The original equations, random initial-state
identity, full conditional heat equation and white/physical conversion
are ALL derived internally. No conditional SPDE/mild or law premise is
introduced. The prefix contains only state information. -/
theorem models(hZ:Measurable Z)(known:P→RealL2)(hk:Measurable known)
    (hknown:ξ=ᵐ[μ] fun ω=>known (Z ω))
    (hWm:∀i,Measurable (Function.uncurry (W i)))(hlocal:StandardTerminalPastLocality J)
    (hW:∀i t,t≤H→W i t=ᵐ[μ] CanonicalScalarItoCells.coordinate H i 𝓕 μ
      (OriginalSingleHaarInputs.integral 𝓕 μ H J) t):
    ∀ᵐp∂μ.map Z,∀K:StandardTerminalIto (C:=RealHaarInput) (E:=ℝ)
      (filtration H) (kernel 𝓕 μ H D J ξ S W hd Z p) H,
      StandardTerminalPastLocality K→
      (∀i (t:ℝ≥0),t≤H→
        (K.integral (StoppedItoInputs.stop (filtration H) _ H t
          (RawCylindricalCoordinates.row (filtration H) _ H
            (NativeSingleNoiseBasis.basis:HaarNode→RealHaarInput) i)))=ᵐ[kernel 𝓕 μ H D J ξ S W hd Z p]
              CanonicalStateDriverFiltration.coordinate H i t)→
      ∃R:SingleNativeHeatEquation.Data (filtration H) (kernel 𝓕 μ H D J ξ S W hd Z p) H D
        (NativeWhiteToPhysicalEquation.physical (filtration H) (kernel 𝓕 μ H D J ξ S W hd Z p) H K) (known p),
        R.value=state H:=by
  let Y:=bundle 𝓕 μ H D J ξ S W hd
  have hY:Measurable Y:=CanonicalContinuousStateDriver.measurable_bundle H S.value S.continuous W hd
    (S.predictable.mono (predictable_le_product 𝓕)).measurable hWm
  have he:=ConditionalOriginalHeatEquations.conditional 𝓕 μ H D S.value S.continuous S.predictable
    (OriginalSingleHaarInputs.integral 𝓕 μ H J) W hd Z hZ hWm
    (OriginalSingleHaarApproximation.locality 𝓕 μ H J hlocal) hW
    (fun a=>RandomInitialSingleWhiteEquation.residual 𝓕 μ H D J ξ S
      (time a) (time_le a) (gap a) (gap_pos a) (site a))
  have hs:Measurable (state H 0):=
    (CanonicalStateDriverFiltration.state_adapted (E:=RealL2) (ι:=HaarNode) H 0).mono
      ((filtration H).le 0) le_rfl
  have hi:(fun ω=>state H 0 (Y ω))=ᵐ[μ] fun ω=>known (Z ω):=by
    filter_upwards [hknown] with ω hω
    change S.value ((min (0:ℝ) (H:ℝ)).toNNReal) ω=known (Z ω)
    simp only [min_eq_left H.coe_nonneg,Real.toNNReal_zero]
    rw [congrFun S.initial ω]
    exact hω
  have hc:=ConditionalInitialState.known_state μ Z Y hZ hY (state H 0) known hs hk hi
  filter_upwards [he,hc] with p hp hinit
  intro K hK hBasis
  have hres:NativeWhiteToPhysicalEquation.ResidualEquation (filtration H)
      (kernel 𝓕 μ H D J ξ S W hd Z p) H K D (state H)
      (CanonicalStateDriverFiltration.state_predictable H):=hp K hK hBasis
  let R:=NativeWhiteToPhysicalEquation.of_white (filtration H) (kernel 𝓕 μ H D J ξ S W hd Z p) H K D
    (state H) (CanonicalStateDriverFiltration.state_predictable H)
    (CanonicalStateDriverFiltration.state_continuous H) hres (known p) hinit
  exact ⟨R,rfl⟩
end SHE.ConditionalSingleHeatModel
