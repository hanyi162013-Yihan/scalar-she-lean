module

public import SHE.MixedPastDerivativeRMS
public import SHE.RelativeAgeSections
public import SHE.MixedPastProfileDerivative
public import SHE.ScalarFibreRMS
public import SHE.ForestLeafL2
public import SHE.MixedCurrentInputMoments
public import SHE.MixedPastJointData
public import SHE.MixedNativePastProfileCentering
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastBaselineEnergySections
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastBaselineEnergySections_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedPastBaselineEnergySections_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastBaselineEnergySections_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastBaselineEnergySections_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastBaselineEnergySections_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastBaselineEnergySections_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastBaselineEnergySections_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

local instance mixedPastBaselineEnergySections_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastBaselineEnergySections_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩

open ControlledProfile

include hIJ₀ hIJ₁ in
/-- ONE theta event carries the actual random-past derivative RMS gain
at EVERY original old native-leaf age of every finite level. Original
time disintegration is proved before selecting the zero spatial anchor. -/
theorem time_sections (P : CanonicalCovariance.ProfileParameters) (hΛ : 0≤Λ)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hinit : v₀=u₀) (v : ℝ≥0) (hvH : v≤H) (hv1 : (v:ℝ)≤1)
    (p : ℕ) (hp : 0<p) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B) :
    ∀ᵐ θ ∂volume,∀ (R : CutoffWordLevel.ReferenceData) (n : ℕ)
      (L : CutoffWordLevel.Level R HeatCircle n) (T : ℝ),(∀ x,L.terminal x=T)→
      (v:ℝ)≤R.base→∀ k:ℕ,
      ∀ᵐ t:Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Set.Ioc R.base R.horizon)),
        let a:=HistoryProductMeasure.separated k ((0:HeatCircle),t,fun _=>(0:HeatCircle))
        PhysicalParentGeometry.StrictHistory L k a→∀ j:Fin k,
        let age:=CoveredControlledLaw.targets L k a (PhysicalChainArrays.leafIndex k (fun i=>i) j)-(v:ℝ)
        let e:=MixedPastDerivativeRMS.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v age θ
        Integrable (fun z : Ω×HeatCircle=>|e z|^2) (μ.prod AddCircle.haarAddCircle) ∧
          (∫ z : Ω×HeatCircle,|e z|^2 ∂μ.prod AddCircle.haarAddCircle)≤
            (ControlledProfile.sharpUnit P*age^((P.exponent-1)/4))^2*
              (∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ) := by
  filter_upwards [MixedPastProfileEnergy.derivative_spatial_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ P hΛ hsmallPoint hsmallL2
    hinit v hvH hv1 p hp B hBDG] with θ hθ
  intro R n L T hT hv k
  exact BaselineSharpHistory.relative_time_sections_of_ae L T hT k v hv _ hθ

end SHE.MixedPastBaselineEnergySections

