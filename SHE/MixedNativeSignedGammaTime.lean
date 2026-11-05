module
public import SHE.HeatBandMovingSignedEnergy
public import SHE.MixedNativeCoefficientField

public import SHE.MixedActualEnergyBridge
public import SHE.PredictableScalarField

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedNativeSignedGammaTime
open MeasureTheory AddCircle GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaReferenceEnergy_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance firstGammaFrozenValues_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaFrozenValues_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaFrozenValues_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaFrozenValues_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaFrozenValues_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaFrozenValues_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

variable (hΛ:0≤Λ) (hH:(H:ℝ)≤1)
local notation "hM"=>(hell.le.trans ((hbU 0).1.trans (hbU 0).2))
local notation "fU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "fV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second



local instance mixedNativeSignedGammaTime_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance mixedNativeSignedGammaTime_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance mixedNativeSignedGammaTime_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance mixedNativeSignedGammaTime_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance mixedNativeSignedGammaTime_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology


def realInputMass {ρ:ℝ} (hL:1≤Λ) (hρ:0≤ρ) (r:ℝ):ℝ≥0∞:=
  (Set.Ioc (0:ℝ) (H:ℝ)).indicator (fun r=>∫⁻ω,
    ENNReal.ofReal (‖OneInputOperator.besselHalf Λ ρ hL hρ
      (MixedNativeCoefficientField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (r.toNNReal,ω))‖^2) ∂μ) r

theorem mass_eq {ρ:ℝ} (hL:1≤Λ) (hρ:0≤ρ) :
    (∫⁻r,realInputMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hL hρ r)=
      MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ:=by
  unfold realInputMass
  rw [lintegral_indicator measurableSet_Ioc,
    MixedNativeCoefficientField.negative_product 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hL hρ]
  have hm:=(((OneInputOperator.besselHalf Λ ρ hL hρ).continuous.measurable.comp
    ((MixedNativeCoefficientField.field_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S).mono
      (predictable_le_product 𝓕)).measurable).norm.pow_const 2).ennreal_ofReal
  rw [show (∫⁻p:ℝ≥0×Ω,ENNReal.ofReal (‖OneInputOperator.besselHalf Λ ρ hL hρ
      (MixedNativeCoefficientField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S p)‖^2) ∂energyMeasure μ H)=
      (∫⁻q,∫⁻ω,ENNReal.ofReal (‖OneInputOperator.besselHalf Λ ρ hL hρ
      (MixedNativeCoefficientField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (q,ω))‖^2) ∂μ ∂timeMeasure H) from
    lintegral_prod _ (by exact hm.aemeasurable),timeMeasure_lintegral]

/-- The first signed-noise Gamma band has its true ORIGINAL residual
coefficient negative-input mass and the full moving-past/time band gain.
No coefficient norm, state moment or stochastic-isometry premise is added. -/
theorem energy {ρ A β c:ℝ} (hL:1≤Λ) (hρ:0≤ρ) (hβ:β≤1) (hc:0<c) (j:ℕ) (h W:ℝ):
    (∫⁻τ in Set.Ioc (0:ℝ) h,HeatBandCausalEnergy.kernel A β c j τ*
      (∫⁻v in Set.Ioc (0:ℝ) W,realInputMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hL hρ (v+h-τ)))≤
      ENNReal.ofReal ((A*ScalarHeatBandEnvelope.constant β 0)^2*
        ScalarHeatBandTime.massConstant β 0*c⁻¹*CompactMollifier.radius (j+1)^(2*β))*
          MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ:=by
  have he:=HeatBandMovingSignedEnergy.energy (A:=A) hβ hc j
    (realInputMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hL hρ) h W
  rwa [mass_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hL hρ] at he
end SHE.MixedNativeSignedGammaTime
