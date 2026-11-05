module
public import SHE.MixedNativeSignedGammaTime
public import SHE.MixedNativeGammaEnergy
public import SHE.MixedNativeCoefficientField

public import SHE.MixedActualEnergyBridge
public import SHE.PredictableScalarField

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedNativeSignedGammaInput
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


variable (P:CanonicalCovariance.ProfileParameters)
local notation "fU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "fV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second
local notation "cU"=>MixedNativeGammaEnergy.currentFirst 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P
local notation "cV"=>MixedNativeGammaEnergy.currentSecond 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P

/-- The literal signed input in the complete stochastic Gamma estimate
is the TRUE native residual-coefficient negative energy. Widening the
ellipticity bounds changes no coefficient or norm. -/
theorem input_eq {ρ:ℝ} (hL:1≤Λ) (hρ:0≤ρ) (p:ℝ≥0×Ω):
    NativeSignedHaarProcess.inputEnergy hL hρ (cV p) (cU p)=
      ‖OneInputOperator.besselHalf Λ ρ hL hρ
        (MixedNativeCoefficientField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S p)‖^2:=by
  change ‖OneInputOperator.besselHalf Λ ρ hL hρ (CircleNormalization.push ((fU p).val-(fV p).val))‖^2=
    ‖OneInputOperator.besselHalf Λ ρ hL hρ (CircleNormalization.push ((fV p).val-(fU p).val))‖^2
  simp only [map_sub]
  rw [norm_sub_rev]

/-- Exact covered-current mass in the original moving-past clock.
The original time cutoff remains visible, rather than extending the
actual coefficient energy outside its constructed horizon. -/
theorem mass_eq {ρ:ℝ} (hL:1≤Λ) (hρ:0≤ρ) (q:ℝ≥0) (hq:0<q) (hqH:q≤H):
    (∫⁻ω,ENNReal.ofReal (NativeSignedHaarProcess.inputEnergy hL hρ (cV (q,ω)) (cU (q,ω))) ∂μ)=
      MixedNativeSignedGammaTime.realInputMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hL hρ q:=by
  rw [MixedNativeSignedGammaTime.realInputMass,Set.indicator_of_mem
    (show (q:ℝ)∈Set.Ioc (0:ℝ) (H:ℝ) from ⟨by exact_mod_cast hq,by exact_mod_cast hqH⟩)]
  simp only [Real.toNNReal_coe]
  apply lintegral_congr
  intro ω
  rw [input_eq]

theorem realInputMass_measurable {ρ:ℝ} (hL:1≤Λ) (hρ:0≤ρ):
    Measurable (MixedNativeSignedGammaTime.realInputMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hL hρ):=by
  have hm:=(((OneInputOperator.besselHalf Λ ρ hL hρ).continuous.measurable.comp
    ((MixedNativeCoefficientField.field_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S).mono
      (predictable_le_product 𝓕)).measurable).norm.pow_const 2).ennreal_ofReal
  have hc:=hm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  exact (hc.lintegral_prod_right' (ν:=μ)).indicator measurableSet_Ioc
end SHE.MixedNativeSignedGammaInput
