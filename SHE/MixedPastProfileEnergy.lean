module

public import SHE.RandomProfileEnergy
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

namespace SHE.MixedPastProfileEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastProfileDerivative_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativePastProfileFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativePastProfileFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativePastProfileFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativePastProfileFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativePastProfileFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativePastProfileFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

local instance mixedNativePastProfileFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativePastProfileFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩

open ControlledProfile

include hIJ₀ hIJ₁ in
/-- Genuine sample/spatial energy of the actual canonical derivative
based on U_v and V_v-U_v. The only moment input is ordinary BDG; finite
past Hilbert energy is derived for the actual common-initial pair. -/
theorem derivative_spatial_energy (P : CanonicalCovariance.ProfileParameters) (hΛ : 0≤Λ)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hinit : v₀=u₀) (v : ℝ≥0) (hvH : v≤H) (hv1 : (v:ℝ)≤1)
    (n : ℕ) (hn : 0<n) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower n J B) :
    ∀ᵐ θ ∂MeasureTheory.volume,∀ᵐ r ∂MeasureTheory.volume.restrict (Set.Ici (0:ℝ)),
      Integrable (fun z : Ω×HeatCircle=>|ControlledProfile.derivative P Λ (embed (S.first v z.1))
        (embed (S.second v z.1-S.first v z.1)) ((r,z.2),θ)|^2) (μ.prod AddCircle.haarAddCircle) ∧
      (∫ z : Ω×HeatCircle,|ControlledProfile.derivative P Λ (embed (S.first v z.1))
        (embed (S.second v z.1-S.first v z.1)) ((r,z.2),θ)|^2 ∂μ.prod AddCircle.haarAddCircle)≤
        (ControlledProfile.sharpUnit P*r^((P.exponent-1)/4))^2*
          (∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ) := by
  subst v₀
  have hu := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hd := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have he := MixedHeatedDifferenceMoments.current_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ v hvH hv1 n hn B hBDG
  have hdi : Integrable (fun ω=>‖embed (S.second v ω-S.first v ω)‖^2) μ := by
    simpa only [NativeHeatObservation.embed_norm] using he.1
  have hs := ControlledProfile.random_derivative_spatial_energy P hΛ _ _ hu hd hsmallPoint hsmallL2 μ hdi
  simpa only [MixedPastJointData.pastU,MixedPastJointData.pastD,NativeHeatObservation.embed_norm] using hs

end SHE.MixedPastProfileEnergy
