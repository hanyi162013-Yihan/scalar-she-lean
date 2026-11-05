module

public import SHE.RandomProfileDerivative
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

namespace SHE.MixedPastProfileDerivative
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

variable (P : CanonicalCovariance.ProfileParameters)
variable (hΛ : 0≤Λ)
variable (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)

def derivative (v : ℝ≥0) (ω : Ω) (r : Domain) (θ : ℝ) : ℝ :=
  ControlledProfile.derivative P Λ (embed (S.first v ω))
    (embed (S.second v ω-S.first v ω)) (r,θ)

include hΛ hsmallPoint in
/-- Actual random-past derivatives are jointly Borel already for the
past sigma algebra, so their pointwise energies are legitimate past weights. -/
theorem derivative_past_measurable (v : ℝ≥0) :
    @Measurable ((Ω×Domain)×ℝ) ℝ (((𝓕 v).prod inferInstance).prod inferInstance) inferInstance
      (fun z=>derivative 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v z.1.1 z.1.2 z.2) := by
  have hu := MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  have hd := MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  letI : MeasurableSpace Ω := 𝓕 v
  convert! ControlledProfile.random_derivative_measurable P hΛ _ _ hu hd hsmallPoint using 1

include hΛ hsmallPoint hsmallL2 in
/-- Genuine joint Rademacher/Fubini applicability for the reference based
on the ACTUAL U_v and V_v-U_v. Norm dependence on the random past remains
inside the inequality, with the original relative profile age. -/
theorem ae_derivative_sharp_power (v : ℝ≥0) :
    ∀ᵐ θ ∂MeasureTheory.volume,∀ᵐ ω ∂μ,∀ᵐ r ∂MeasureTheory.volume.restrict (Set.Ici (0:ℝ)),
      MemLp (fun x=>derivative 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v ω (r,x) θ)
          2 AddCircle.haarAddCircle ∧
      ProfileL2.normTwo AddCircle.haarAddCircle
          (fun x=>derivative 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v ω (r,x) θ)≤
        ControlledScoreRates.sharpConstant P (embed (S.second v ω-S.first v ω))*r^((P.exponent-1)/4) := by
  have hu := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hd := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  convert! ControlledProfile.random_ae_derivative_sharp_power P hΛ _ _ hu hd hsmallPoint hsmallL2 μ using 1

end SHE.MixedPastProfileDerivative
