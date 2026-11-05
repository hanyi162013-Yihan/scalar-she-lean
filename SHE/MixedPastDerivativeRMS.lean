module

public import SHE.MixedPastProfileEnergy
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

namespace SHE.MixedPastDerivativeRMS
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastDerivativeRMS_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedPastDerivativeRMS_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastDerivativeRMS_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastDerivativeRMS_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastDerivativeRMS_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastDerivativeRMS_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastDerivativeRMS_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

local instance mixedPastDerivativeRMS_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastDerivativeRMS_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩

open ControlledProfile

def field (P : CanonicalCovariance.ProfileParameters) (v : ℝ≥0) (r θ : ℝ) (z : Ω×HeatCircle) : ℝ :=
  ControlledProfile.derivative P Λ (embed (S.first v z.1)) (embed (S.second v z.1-S.first v z.1)) ((r,z.2),θ)

theorem field_measurable (P : CanonicalCovariance.ProfileParameters) (hΛ : 0≤Λ)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (v : ℝ≥0) (r θ : ℝ) :
    Measurable (field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v r θ) := by
  have hu:=(MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hd:=(MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hh:=ControlledProfile.random_derivative_measurable P hΛ _ _ hu hd hsmallPoint
  convert! hh.comp ((measurable_fst.prodMk (measurable_const.prodMk measurable_snd)).prodMk measurable_const) using 1

include hIJ₀ hIJ₁ in
/-- The actual baseline derivative RMS has the sharp spatial energy
gain, with original relative age and actual past difference energy.
All stochastic and random-reference applicability is derived. -/
theorem rms_energy (P : CanonicalCovariance.ProfileParameters) (hΛ : 0≤Λ)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hinit : v₀=u₀) (v : ℝ≥0) (hvH : v≤H) (hv1 : (v:ℝ)≤1)
    (p : ℕ) (hp : 0<p) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B) :
    ∀ᵐ θ ∂volume,∀ᵐ r ∂volume.restrict (Set.Ici (0:ℝ)),
      let e:=field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v r θ
      MemLp (ScalarFibreRMS.rms μ e) 2 AddCircle.haarAddCircle ∧
        (ProfileL2.normTwo AddCircle.haarAddCircle (ScalarFibreRMS.rms μ e))^2≤
          (ControlledProfile.sharpUnit P*r^((P.exponent-1)/4))^2*
            (∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ) := by
  filter_upwards [MixedPastProfileEnergy.derivative_spatial_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ P hΛ hsmallPoint hsmallL2
    hinit v hvH hv1 p hp B hBDG] with θ hθ
  filter_upwards [hθ] with r hr
  let e:=field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v r θ
  have hm:=field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hΛ hsmallPoint v r θ
  have hh:=ScalarFibreRMS.memLp_energy μ AddCircle.haarAddCircle e hm hr.1
  exact ⟨hh.1,hh.2.trans_le hr.2⟩

end SHE.MixedPastDerivativeRMS

