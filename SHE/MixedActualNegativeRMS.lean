module

public import SHE.MixedActualEnergyBridge
public import SHE.PredictableScalarField
public import SHE.MixedNativeCoefficientField
public import SHE.ScalarTimeZeroExtension
public import SHE.TimeTranslationAverage

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedActualNegativeRMS
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

def rms (ρ:ℝ)(hL:1≤Λ)(hρ:0≤ρ)(p:ℝ≥0×Ω):ℝ:=
  ‖OneInputOperator.besselHalf Λ ρ hL hρ (Input p)‖
local notation "RMS"=>rms 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

theorem measurable (ρ:ℝ)(hL:1≤Λ)(hρ:0≤ρ):Measurable (RMS ρ hL hρ):=
  (((OneInputOperator.besselHalf Λ ρ hL hρ).continuous.measurable.comp
    ((MixedNativeCoefficientField.field_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S).mono
      (predictable_le_product 𝓕)).measurable).norm)

theorem sqrt_input (ρ:ℝ)(hL:1≤Λ)(hρ:0≤ρ)(p:ℝ≥0×Ω):
    Real.sqrt (StepInput.negativeEnergy 1 Λ ρ ((fU p).1-(fV p).1))=RMS ρ hL hρ p:=by
  rw [←CircleNormalization.push_bessel_energy hL hρ]
  have he:(fU p).1-(fV p).1=-((fV p).1-(fU p).1):=by abel
  rw [he,map_neg,map_neg,norm_neg,Real.sqrt_sq (norm_nonneg _)]
  rfl

/-- The exact negative-input RMS extends to the full translation clock
with precisely the original stochastic coefficient-input energy. -/
theorem extended_energy (ρ:ℝ)(hL:1≤Λ)(hρ:0≤ρ):
    Integrable (fun z:ℝ×Ω=>ScalarTimeZeroExtension.extend H (RMS ρ hL hρ) z^2) (volume.prod μ) ∧
      (∫z:ℝ×Ω,ScalarTimeZeroExtension.extend H (RMS ρ hL hρ) z^2 ∂volume.prod μ)=(Neg ρ).toReal:=by
  have hm:=measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ hL hρ
  have hn:(Neg ρ)≠∞:=ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (MixedActualEnergyBridge.negative_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      (zero_lt_one.trans_le hL) hρ)
  have he:=MixedNativeCoefficientField.negative_product 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hL hρ
  have hi:Integrable (fun p:ℝ≥0×Ω=>(RMS ρ hL hρ p)^2) (energyMeasure μ H):=by
    refine ⟨(hm.pow_const 2).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun p=>sq_nonneg (RMS ρ hL hρ p)))]
    exact lt_top_iff_ne_top.mpr (by change (∫⁻p,ENNReal.ofReal (‖OneInputOperator.besselHalf Λ ρ hL hρ (Input p)‖^2) ∂energyMeasure μ H)≠∞;rw [←he];exact hn)
  have hr:(∫p:ℝ≥0×Ω,(RMS ρ hL hρ p)^2 ∂energyMeasure μ H)=(Neg ρ).toReal:=by
    have he':ENNReal.ofReal (∫p:ℝ≥0×Ω,(RMS ρ hL hρ p)^2 ∂energyMeasure μ H)=Neg ρ:=by
      rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun p=>sq_nonneg (RMS ρ hL hρ p)))]
      exact he.symm
    exact (ENNReal.toReal_ofReal (integral_nonneg (fun p=>sq_nonneg (RMS ρ hL hρ p)))).symm.trans
      (congrArg ENNReal.toReal he')
  have hz:=ScalarTimeZeroExtension.energy μ H (RMS ρ hL hρ) hm
    (by simpa only [Real.norm_eq_abs,sq_abs,energyMeasure] using hi)
  have hz':Integrable (fun z:ℝ×Ω=>ScalarTimeZeroExtension.extend H (RMS ρ hL hρ) z^2) (volume.prod μ) ∧
      (∫z:ℝ×Ω,ScalarTimeZeroExtension.extend H (RMS ρ hL hρ) z^2 ∂volume.prod μ)=
        ∫p:ℝ≥0×Ω,(RMS ρ hL hρ p)^2 ∂energyMeasure μ H:=by
    simpa only [Real.norm_eq_abs,sq_abs,energyMeasure] using hz
  exact ⟨hz'.1,hz'.2.trans hr⟩

end SHE.MixedActualNegativeRMS
