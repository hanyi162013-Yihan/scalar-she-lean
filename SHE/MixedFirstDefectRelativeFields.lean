module
public import SHE.MixedFirstDefectRelativeEnergy

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

namespace SHE.MixedFirstDefectRelativeFields
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

theorem measurable (hδ:0<δ)(hh:0<h)(hC:∀j,0≤C j)(hA0:0≤A0)(hν:0≤ν)
    (ρ:ℝ)(hL:1≤Λ)(hρ:0<ρ)(hρ1:ρ≤1):
    Measurable (MixedFirstDefectRelativeEnergy.value
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P δ C h A0 ν k ρ hL hρ.le):=by
  let ξ:=DefectGapMixture.measure P δ C Λ ρ h A0 ν k
  letI:IsFiniteMeasure ξ:=DefectGapMixture.finite P hδ (zero_lt_one.trans_le hL) hρ hρ1 hh C hC k hA0 hν
  have hf:=ScalarTimeZeroExtension.measurable H (RMS ρ hL hρ.le)
    (MixedActualNegativeRMS.measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ hL hρ.le)
  have hs:Measurable (MixedFirstDefectRelativeEnergy.shift k):=by
    exact (Finset.measurable_sum _ (fun i _=>(measurable_pi_apply i).comp measurable_fst)).add measurable_snd
  have hmap:Measurable (fun z:(ℝ×Ω)×((Fin k→ℝ)×ℝ)=>
      (z.1.1-MixedFirstDefectRelativeEnergy.shift k z.2,z.1.2)):=
    (measurable_fst.fst.sub (hs.comp measurable_snd)).prodMk measurable_fst.snd
  have hm:=hf.comp hmap
  exact (hm.stronglyMeasurable.integral_prod_right' (ν:=ξ)).measurable
end SHE.MixedFirstDefectRelativeFields
