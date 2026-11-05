module

public import SHE.MixedFirstDefectRelativeEnergy
public import SHE.MixedFirstDefectInputBounds
public import SHE.ClockSquareRestriction
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

namespace SHE.MixedFirstDefectGlobalBound
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
local notation "Rel"=>MixedFirstDefectRelativeEnergy.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P δ C h A0 ν k

/-- Positivity of the complete actual input convolution is pointwise,
including zero-extended initial clocks. -/
theorem value_nonneg (ρ:ℝ)(hL:1≤Λ)(hρ:0≤ρ)(z:ℝ×Ω):0≤Rel ρ hL hρ z:=by
  apply integral_nonneg
  intro p
  exact (MixedFirstDefectInputBounds.extended_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ hL hρ _).1

/-- An actual Borel native output dominated by the first-defect RMS
convolution has the original global negative-input energy cap. This
uses the original predictable output clock, including initial times. -/
theorem energy (hδ:0<δ)(hh:0<h)(hC:∀j,0≤C j)(hA0:0≤A0)(hν:0≤ν)
    (ρ:ℝ)(hL:1≤Λ)(hρ:0<ρ)(hρ1:ρ≤1)(Cs:ℝ)(hCs:0≤Cs)
    (G:ℝ≥0×Ω→CircleL2)(hG:Measurable G)
    (hb:∀ᵐz:ℝ≥0×Ω∂energyMeasure μ H,‖G z‖≤Cs*Rel ρ hL hρ.le ((z.1:ℝ),z.2)):
    Integrable (fun z:ℝ≥0×Ω=>‖G z‖^2) (energyMeasure μ H) ∧
      (∫z:ℝ≥0×Ω,‖G z‖^2 ∂energyMeasure μ H)≤
        Cs^2*(DefectGapMixture.cost P δ C Λ ρ h A0 ν k)^2*(Neg ρ).toReal:=by
  have he:=MixedFirstDefectRelativeEnergy.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P δ C h A0 ν k
      hδ hh hC hA0 hν ρ hL hρ hρ1
  have hclock:=ClockSquareRestriction.energy μ H (Rel ρ hL hρ.le) he.1
  have hbound:∀ᵐz:ℝ≥0×Ω∂energyMeasure μ H,
      ‖G z‖^2≤Cs^2*Rel ρ hL hρ.le ((z.1:ℝ),z.2)^2:=by
    filter_upwards [hb] with z hz
    have hh:=pow_le_pow_left₀ (norm_nonneg (G z)) hz 2
    simpa only [mul_pow] using hh
  have hdom:Integrable (fun z:ℝ≥0×Ω=>Cs^2*Rel ρ hL hρ.le ((z.1:ℝ),z.2)^2)
      (energyMeasure μ H):=hclock.1.const_mul (Cs^2)
  have hi:Integrable (fun z:ℝ≥0×Ω=>‖G z‖^2) (energyMeasure μ H):=by
    apply hdom.mono' (hG.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hbound] with z hz
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz
  refine ⟨hi,?_⟩
  calc
    _≤∫z:ℝ≥0×Ω,Cs^2*Rel ρ hL hρ.le ((z.1:ℝ),z.2)^2 ∂energyMeasure μ H:=
      integral_mono_ae hi hdom hbound
    _=Cs^2*(∫z:ℝ≥0×Ω,Rel ρ hL hρ.le ((z.1:ℝ),z.2)^2 ∂energyMeasure μ H):=
      integral_const_mul _ _
    _≤Cs^2*((DefectGapMixture.cost P δ C Λ ρ h A0 ν k)^2*(Neg ρ).toReal):=
      mul_le_mul_of_nonneg_left (hclock.2.trans he.2) (sq_nonneg Cs)
    _=_:=by ring

end SHE.MixedFirstDefectGlobalBound
