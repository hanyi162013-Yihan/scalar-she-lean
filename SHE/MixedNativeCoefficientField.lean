module

public import SHE.MixedActualEnergyBridge
public import SHE.PredictableScalarField

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedNativeCoefficientField
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


/-- The actual native coefficient difference in the final comparison. -/
def field (p:ℝ≥0×Ω):CircleL2:=CircleNormalization.push ((fV p).1-(fU p).1)

theorem field_predictable:StronglyMeasurable[𝓕.predictable]
    (field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S):=by
  exact CircleNormalization.push.continuous.comp_stronglyMeasurable
    ((continuous_subtype_val.comp_stronglyMeasurable S.second_coefficient).sub
      (continuous_subtype_val.comp_stronglyMeasurable S.first_coefficient))

/-- Complex-valued native representative of one actual real coefficient. -/
theorem coefficient_ae {a:ℝ→ℝ} (ha:Measurable a) (hb:∀z,ell≤a z ∧ a z≤M)
    (U:ℝ≥0×Ω→RealL2) (p:ℝ≥0×Ω):
    CircleNormalization.push (CoefficientFields.coefficient a ha M (NonlinearHaarIntegrand.absBound hell hb) (U p))=ᵐ[haarAddCircle]
      fun x=>(a (PredictableScalarField.nativeField U (p,x)):ℂ):=by
  filter_upwards [PredictableScalarField.nativeField_coefficient_ae a ha M
    (NonlinearHaarIntegrand.absBound hell hb) U p,
    CircleNormalization.push_ae_property
      (CoefficientFields.coefficient a ha M (NonlinearHaarIntegrand.absBound hell hb) (U p))
      (fun z:ℂ=>z.im=0) (CoefficientFields.coefficient_real a ha M _ (U p))] with x hx hr
  exact Complex.ext hx (by simpa only [Complex.ofReal_im] using hr)

/-- Both endpoints are the original scalar fields, on the native circle;
no artificial smooth profile or Gaussian state replaces either state. -/
theorem field_ae (p:ℝ≥0×Ω):
    field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S p=ᵐ[haarAddCircle]
      fun x=>(aV (PredictableScalarField.nativeField (Function.uncurry S.second) (p,x))-
        aU (PredictableScalarField.nativeField (Function.uncurry S.first) (p,x)):ℂ):=by
  have hU:=coefficient_ae (Ω:=Ω) hell haU hbU (Function.uncurry S.first) p
  have hV:=coefficient_ae (Ω:=Ω) hell haV hbV (Function.uncurry S.second) p
  have hsub:=Lp.coeFn_sub (CircleNormalization.push (fV p).1) (CircleNormalization.push (fU p).1)
  have he:field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S p=
      CircleNormalization.push (fV p).1-CircleNormalization.push (fU p).1:=map_sub _ _ _
  rw [he]
  filter_upwards [hU,hV,hsub] with x hu hv hs
  change _=_ at hs ⊢
  rw [hs]
  change CircleNormalization.push (fV p).1 x-CircleNormalization.push (fU p).1 x=_
  change CircleNormalization.push (fV p).1 x=_ at hv
  change CircleNormalization.push (fU p).1 x=_ at hu
  rw [hv,hu,←Complex.ofReal_sub]

theorem negative_product {ρ:ℝ} (hΛ1:1≤Λ) (hρ:0≤ρ):
    MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ=
      ∫⁻p:ℝ≥0×Ω,ENNReal.ofReal (‖OneInputOperator.besselHalf Λ ρ hΛ1 hρ
        (field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S p)‖^2) ∂energyMeasure μ H:=by
  rw [MixedActualEnergyBridge.negative_bessel 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ1 hρ]
  symm
  apply lintegral_prod
  exact (((OneInputOperator.besselHalf Λ ρ hΛ1 hρ).continuous.measurable.comp
    ((field_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S).mono
      (predictable_le_product 𝓕)).measurable).norm.pow_const 2).ennreal_ofReal.aemeasurable

end SHE.MixedNativeCoefficientField
