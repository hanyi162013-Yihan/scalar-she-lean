module
public import SHE.MixedNativeSignedGammaTime
public import SHE.MixedNativeCoefficientField

public import SHE.MixedActualEnergyBridge
public import SHE.PredictableScalarField

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.InitialSignedGammaTime
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


local notation "Mass"=>MixedNativeSignedGammaTime.realInputMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

theorem mass_measurable {ρ:ℝ}(hL:1≤Λ)(hρ:0≤ρ):Measurable (Mass hL hρ):=by
  have hf:=((MixedNativeCoefficientField.field_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S).mono
    (predictable_le_product 𝓕)).measurable
  have hm:Measurable (fun z:ℝ×Ω=>ENNReal.ofReal (‖OneInputOperator.besselHalf Λ ρ hL hρ
      (MixedNativeCoefficientField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (z.1.toNNReal,z.2))‖^2)):=
    ((((OneInputOperator.besselHalf Λ ρ hL hρ).continuous.measurable.comp
      (hf.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))).norm).pow_const 2).ennreal_ofReal
  exact (hm.lintegral_prod_right).indicator measurableSet_Ioc

/-- The literal initial physical triangle of the signed first-Gamma
slot retains the true ORIGINAL negative-input energy and the sharp
Gaussian heat-band mass. -/
theorem energy {ρ A β c:ℝ}(hL:1≤Λ)(hρ:0≤ρ)(hβ:β≤1)(hc:0<c)(j:ℕ)(h:ℝ):
    (∫⁻T in Set.Ioc (0:ℝ) h,∫⁻q in Set.Ioc (0:ℝ) T,
      HeatBandCausalEnergy.kernel A β c j (T-q)*Mass hL hρ q)≤
      ENNReal.ofReal ((A*ScalarHeatBandEnvelope.constant β 0)^2*
        ScalarHeatBandTime.massConstant β 0*c⁻¹*CompactMollifier.radius (j+1)^(2*β))*
          MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ:=by
  have hb:=HeatBandCausalEnergy.causal_bound (H:=A) hβ hc j (Mass hL hρ)
    (mass_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hL hρ) h
  apply hb.trans
  apply mul_le_mul_right
  exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans_eq
    (MixedNativeSignedGammaTime.mass_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hL hρ)
end SHE.InitialSignedGammaTime
