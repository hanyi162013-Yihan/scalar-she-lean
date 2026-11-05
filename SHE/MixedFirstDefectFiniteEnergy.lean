module

public import SHE.MixedFirstDefectGlobalBound
public import Mathlib.Algebra.Order.Chebyshev
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

namespace SHE.MixedFirstDefectFiniteEnergy
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

variable (P:CanonicalCovariance.ProfileParameters)(δ:ℝ)(C:ℕ→ℝ)(h A0 ν:ℝ)(N:ℕ)
local notation "Rel"=>MixedFirstDefectRelativeEnergy.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P δ C h A0 ν

/-- All retained first-defect marks can be estimated on ONE genuine
Borel output, without demanding separately chosen moving-time versions
of the individual marks. The right side contains only finite positive
clock envelopes and the original global signed-input energy. -/
theorem energy (hδ:0<δ)(hh:0<h)(hC:∀j,0≤C j)(hA0:0≤A0)(hν:0≤ν)
    (ρ:ℝ)(hL:1≤Λ)(hρ:0<ρ)(hρ1:ρ≤1)(Cs:Fin (N+1)→ℝ)
    (G:ℝ≥0×Ω→CircleL2)(hG:Measurable G)
    (hb:∀ᵐz:ℝ≥0×Ω∂energyMeasure μ H,
      ‖G z‖≤∑i:Fin (N+1),Cs i*Rel (i:ℕ) ρ hL hρ.le ((z.1:ℝ),z.2)):
    Integrable (fun z:ℝ≥0×Ω=>‖G z‖^2) (energyMeasure μ H) ∧
      (∫z:ℝ≥0×Ω,‖G z‖^2 ∂energyMeasure μ H)≤
        ((N+1:ℕ):ℝ)*(∑i:Fin (N+1),Cs i^2*
          (DefectGapMixture.cost P δ C Λ ρ h A0 ν (i:ℕ))^2)*(Neg ρ).toReal:=by
  let D:Fin (N+1)→(ℝ≥0×Ω)→ℝ:=fun i z=>Cs i^2*Rel (i:ℕ) ρ hL hρ.le ((z.1:ℝ),z.2)^2
  have hd(i:Fin (N+1)):Integrable (D i) (energyMeasure μ H) ∧
      (∫z,D i z ∂energyMeasure μ H)≤Cs i^2*
        (DefectGapMixture.cost P δ C Λ ρ h A0 ν (i:ℕ))^2*(Neg ρ).toReal:=by
    have he:=MixedFirstDefectRelativeEnergy.energy
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P δ C h A0 ν (i:ℕ)
        hδ hh hC hA0 hν ρ hL hρ hρ1
    have hc:=ClockSquareRestriction.energy μ H (Rel (i:ℕ) ρ hL hρ.le) he.1
    refine ⟨hc.1.const_mul (Cs i^2),?_⟩
    change (∫z,Cs i^2*Rel (i:ℕ) ρ hL hρ.le ((z.1:ℝ),z.2)^2 ∂energyMeasure μ H)≤_
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left (hc.2.trans he.2) (sq_nonneg (Cs i))).trans_eq (by ring)
  let B:(ℝ≥0×Ω)→ℝ:=fun z=>((N+1:ℕ):ℝ)*∑i:Fin (N+1),D i z
  have hBi:Integrable B (energyMeasure μ H):=
    (integrable_finsetSum _ (fun i _=>(hd i).1)).const_mul ((N+1:ℕ):ℝ)
  have hbound:∀ᵐz:ℝ≥0×Ω∂energyMeasure μ H,‖G z‖^2≤B z:=by
    filter_upwards [hb] with z hz
    have hp:=pow_le_pow_left₀ (norm_nonneg (G z)) hz 2
    have hs:=sq_sum_le_card_mul_sum_sq (s:=Finset.univ)
      (f:=fun i:Fin (N+1)=>Cs i*Rel (i:ℕ) ρ hL hρ.le ((z.1:ℝ),z.2))
    apply hp.trans
    simpa only [Finset.card_univ,Fintype.card_fin,mul_pow,D,B] using hs
  have hi:Integrable (fun z:ℝ≥0×Ω=>‖G z‖^2) (energyMeasure μ H):=by
    apply hBi.mono' (hG.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hbound] with z hz
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz
  refine ⟨hi,?_⟩
  calc
    _≤∫z,B z ∂energyMeasure μ H:=integral_mono_ae hi hBi hbound
    _=((N+1:ℕ):ℝ)*∑i:Fin (N+1),∫z,D i z ∂energyMeasure μ H:=by
      change (∫z,((N+1:ℕ):ℝ)*∑i:Fin (N+1),D i z ∂energyMeasure μ H)=_
      rw [integral_const_mul,integral_finsetSum _ (fun i _=>(hd i).1)]
    _≤((N+1:ℕ):ℝ)*∑i:Fin (N+1),Cs i^2*
        (DefectGapMixture.cost P δ C Λ ρ h A0 ν (i:ℕ))^2*(Neg ρ).toReal:=by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun i _=>(hd i).2)
    _=_:=by rw [←Finset.sum_mul];ring
end SHE.MixedFirstDefectFiniteEnergy
