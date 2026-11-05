module
public import SHE.CanonicalHeatIntegralIdentification
public import SHE.OriginalNativeCountableEquationCompletion
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
set_option linter.unusedSectionVars false
namespace SHE.ConditionalOriginalHeatEquations
open MeasureTheory ProbabilityTheory Set FiniteHaar DyadicApproximation AddCircle PredictableL2 Filter
open OriginalNativeCountableEquationCompletion
open scoped NNReal ENNReal Topology
local instance conditionalHeat_unit : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance conditionalHeat_circleSecond : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance conditionalHeat_realSecond : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance conditionalHeat_realSigma : MeasurableSpace RealL2 := borel _
local instance conditionalHeat_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance conditionalHeat_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance conditionalHeat_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
abbrev Space (H:ℝ≥0) := CanonicalContinuousStateDriver.Space (E:=RealL2) (ι:=HaarNode) H
abbrev filtration (H:ℝ≥0) := CanonicalStateDriverFiltration.filtration (E:=RealL2) (ι:=HaarNode) H
abbrev state (H:ℝ≥0) := CanonicalStateDriverFiltration.state (E:=RealL2) (ι:=HaarNode) H

variable {Ω P : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H : ℝ≥0) (D : SmoothApproximation.ScalarData)
variable (U : ℝ≥0→Ω→RealL2) (hc : ∀ω,Continuous (fun t=>U t ω)) (hU : IsStronglyPredictable 𝓕 U)
variable (J : StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (W : HaarNode→ℝ≥0→Ω→ℝ) (hd : ∀i ω,Continuous (fun t=>W i t ω))

/-- The actual original equations pass through true conditional laws.
One prefix event works for ALL positive heat tests. Conditional input
convergence, canonical finite-cell identities and dense-parameter
completion are all proved internally. The supplied fiber integral is
only required to be the ordinary integral of its recognized coordinates. -/
theorem conditional (Z:Ω→P) (hZ:Measurable Z)
    (hWm:∀i,Measurable (Function.uncurry (W i))) (hlocal:StandardTerminalPastLocality J)
    (hW:∀i t,t≤H→W i t=ᵐ[μ] CanonicalScalarItoCells.coordinate H i 𝓕 μ J t)
    (heq:∀a:Tests H,OriginalNativeDenseObservationCompletion.residual U (time a) (gap a) (site a)=ᵐ[μ]
      J.integral (OriginalNativeWhiteHeatRows.input D U 𝓕 hU μ H (time a) (gap a) (gap_pos a) (site a))) :
    ∀ᵐp∂μ.map Z,∀K:StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) (filtration H)
      (condDistrib (CanonicalContinuousStateDriver.bundle H U hc W hd) Z μ p) H,
      StandardTerminalPastLocality K→
      (∀i (t:ℝ≥0),t≤H→
        (K.integral (StoppedItoInputs.stop (filtration H) _ H t
          (RawCylindricalCoordinates.row (filtration H) _ H
            (NativeSingleNoiseBasis.basis:HaarNode→RealHaarInput) i)))=ᵐ[condDistrib
              (CanonicalContinuousStateDriver.bundle H U hc W hd) Z μ p]
                CanonicalStateDriverFiltration.coordinate H i t)→
      ∀(q:ℝ≥0),q≤H→∀(ε:ℝ)(hε:0<ε)(x:StoppedFourier.HeatCircle),
        OriginalNativeDenseObservationCompletion.residual (state H) q ε x=ᵐ[condDistrib
          (CanonicalContinuousStateDriver.bundle H U hc W hd) Z μ p]
            K.integral (OriginalNativeWhiteHeatRows.input D (state H) (filtration H)
              (CanonicalStateDriverFiltration.state_predictable H)
              (condDistrib (CanonicalContinuousStateDriver.bundle H U hc W hd) Z μ p) H q ε hε x) := by
  let Y := CanonicalContinuousStateDriver.bundle H U hc W hd
  have hY : Measurable Y := CanonicalContinuousStateDriver.measurable_bundle H U hc W hd
    (hU.mono (predictable_le_product 𝓕)).measurable hWm
  have hex (a:Tests H) := CanonicalOriginalHeatSums.exists_observed_limit H D
    (time a) (time_le a) (gap a) (site a) 𝓕 μ U hc hU J W hd (gap_pos a) hlocal hW
    (by
      filter_upwards [heq a] with ω hω
      rw [CanonicalHeatResidual.value_bundle H U hc W hd (time a) (time_le a)]
      exact hω)
  choose ns hns hlim using hex
  have hcond := ConditionalCanonicalItoLimit.ae_limits μ Z Y hZ hY
    (fun a n=>CanonicalOriginalHeatSums.value H D (time a) (time_le a) (gap a) (site a) (ns a n))
    (fun a=>CanonicalHeatResidual.value H (time a) (gap a) (site a))
    (fun a n=>CanonicalOriginalHeatSums.measurable_value H D (time a) (time_le a)
      (gap a) (site a) (gap_pos a) (ns a n))
    (fun a=>CanonicalHeatResidual.measurable_value H (time a) (gap a) (site a)) hlim
  filter_upwards [hcond] with p hp
  intro K hK hBasis q hq ε hε x
  apply equation_of_countable D (state H) (filtration H)
    (CanonicalStateDriverFiltration.state_predictable H)
    (condDistrib Y Z μ p) H K (CanonicalStateDriverFiltration.state_continuous H)
  · intro a
    exact CanonicalHeatIntegralIdentification.identify H D (condDistrib Y Z μ p) K hK hBasis
      (time a) (time_le a) (gap a) (gap_pos a) (site a) (ns a) (hns a) (hp a)
  · exact hq
end SHE.ConditionalOriginalHeatEquations
