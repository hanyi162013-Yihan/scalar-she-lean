module

public import SHE.MixedActualEnergyBridge
public import SHE.PredictableScalarField
public import SHE.MixedNativeCoefficientField
public import SHE.MixedActualNegativeRMS
public import SHE.MixedActualNegativeConvolution
public import SHE.DefectGapMixture
public import SHE.ScalarTimeZeroExtension
public import SHE.TimeTranslationAverage

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedFirstDefectRelativeEnergy
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



local instance actualEnergyBridge_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance actualEnergyBridge_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance actualEnergyBridge_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance actualEnergyBridge_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance actualEnergyBridge_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology


local notation "Input"=>MixedNativeCoefficientField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Neg"=>MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

local notation "RMS"=>MixedActualNegativeRMS.rms 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

open Set
open scoped BigOperators
variable (P:CanonicalCovariance.ProfileParameters)(δ:ℝ)(C:ℕ→ℝ)(h A0 ν:ℝ)(k:ℕ)

def shift (k:ℕ)(p:(Fin k→ℝ)×ℝ):ℝ:=(∑i,p.1 i)+p.2

def value (ρ:ℝ)(hL:1≤Λ)(hρ:0≤ρ)(z:ℝ×Ω):ℝ:=
  ∫p,ScalarTimeZeroExtension.extend H (RMS ρ hL hρ) (z.1-shift k p,z.2)
    ∂DefectGapMixture.measure P δ C Λ ρ h A0 ν k

/-- The actual negative-input convolution over the COMPLETE positive
old/new history mixture has the original global energy times precisely
the squared explicit collision/kernel mass. -/
theorem energy (hδ:0<δ)(hh:0<h)(hC:∀j,0≤C j)(hA0:0≤A0)(hν:0≤ν)
    (ρ:ℝ)(hL:1≤Λ)(hρ:0<ρ)(hρ1:ρ≤1):
    Integrable (fun z:ℝ×Ω=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P δ C h A0 ν k ρ hL hρ.le z^2) (volume.prod μ) ∧
      (∫z:ℝ×Ω,value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P δ C h A0 ν k ρ hL hρ.le z^2 ∂volume.prod μ)≤
        (DefectGapMixture.cost P δ C Λ ρ h A0 ν k)^2*(Neg ρ).toReal:=by
  let ξ:=DefectGapMixture.measure P δ C Λ ρ h A0 ν k
  have hΛp:0<Λ:=zero_lt_one.trans_le hL
  letI:IsFiniteMeasure ξ:=DefectGapMixture.finite P hδ hΛp hρ hρ1 hh C hC k hA0 hν
  have hs:Measurable (shift k):=by
    exact (Finset.measurable_sum _ (fun i _=>(measurable_pi_apply i).comp measurable_fst)).add measurable_snd
  have he:=MixedActualNegativeConvolution.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    ρ hL hρ.le ξ (shift k) hs
  have hmass:ξ.real univ≤DefectGapMixture.cost P δ C Λ ρ h A0 ν k:=by
    have hb:=DefectGapMixture.mass P hδ hΛp hρ hρ1 hh C hC k hA0 hν
    have hr:=ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    simpa only [Measure.real,ξ,ENNReal.toReal_ofReal
      (DefectGapMixture.cost_nonneg P hδ hΛp hρ hρ1 hh C hC k hA0 hν)] using hr
  refine ⟨he.1,he.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ENNReal.toReal_nonneg hmass 2) ENNReal.toReal_nonneg

end SHE.MixedFirstDefectRelativeEnergy
