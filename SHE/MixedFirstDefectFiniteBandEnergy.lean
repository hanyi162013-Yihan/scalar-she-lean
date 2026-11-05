module

public import SHE.MixedFirstDefectFiniteEnergy
public import SHE.DefectGapDyadicCost
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

namespace SHE.MixedFirstDefectFiniteBandEnergy
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


variable (P:CanonicalCovariance.ProfileParameters)(δ:ℝ)(C:ℕ→ℝ)(h A β η ν:ℝ)(N:ℕ)
open Real
local notation "Rel"=>MixedFirstDefectRelativeEnergy.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P δ C h (A*ν^(-β)) ν

def coefficient (P:CanonicalCovariance.ProfileParameters)(δ:ℝ)(C:ℕ→ℝ)
    (A η Λ:ℝ)(N:ℕ)(ρ:ℝ)(Cs:Fin (N+1)→ℝ):ℝ:=
  ((N+1:ℕ):ℝ)*∑i:Fin (N+1),Cs i^2*(DefectGapDyadicCost.coefficient P δ C (i:ℕ) A η Λ ρ)^2

/-- The entire finite first-defect family keeps a strictly summable
band power whenever eta<beta. Its one Borel output may be recovered
from the finite stochastic comparison; individual moving versions are
not needed. -/
theorem energy (hδ:0<δ)(hh:0<h)(hh1:h≤1)(hC:∀j,0≤C j)(hA:0≤A)(hη:0<η)(hν:1≤ν)
    (ρ:ℝ)(hL:1≤Λ)(hρ:0<ρ)(hρ1:ρ≤1)(Cs:Fin (N+1)→ℝ)
    (G:ℝ≥0×Ω→CircleL2)(hG:Measurable G)
    (hb:∀ᵐz:ℝ≥0×Ω∂energyMeasure μ H,
      ‖G z‖≤∑i:Fin (N+1),Cs i*Rel (i:ℕ) ρ hL hρ.le ((z.1:ℝ),z.2)):
    Integrable (fun z:ℝ≥0×Ω=>‖G z‖^2) (energyMeasure μ H) ∧
      (∫z:ℝ≥0×Ω,‖G z‖^2 ∂energyMeasure μ H)≤
        coefficient P δ C A η Λ N ρ Cs*ν^(-2*(β-η))*(Neg ρ).toReal:=by
  have hνp:0<ν:=zero_lt_one.trans_le hν
  have hΛp:0<Λ:=zero_lt_one.trans_le hL
  have hAmp:0≤A*ν^(-β):=mul_nonneg hA (rpow_nonneg hνp.le _)
  have he:=MixedFirstDefectFiniteEnergy.energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P δ C h (A*ν^(-β)) ν N
      hδ hh hC hAmp (zero_le_one.trans hν) ρ hL hρ hρ1 Cs G hG hb
  have hp(i:Fin (N+1)):(DefectGapMixture.cost P δ C Λ ρ h (A*ν^(-β)) ν (i:ℕ))^2≤
      (DefectGapDyadicCost.coefficient P δ C (i:ℕ) A η Λ ρ)^2*ν^(-2*(β-η)):=by
    have hc:=DefectGapBandCost.cost_le P (Λ:=Λ) (ρ:=ρ) (h:=h) (β:=β) (η:=η) (ν:=ν)
      hδ hΛp.le hρ C hC (i:ℕ) hh.le hh1 hA hη hν
    have hc':DefectGapMixture.cost P δ C Λ ρ h (A*ν^(-β)) ν (i:ℕ)≤
        DefectGapDyadicCost.coefficient P δ C (i:ℕ) A η Λ ρ*ν^(-(β-η)):=
      hc.trans_eq (by unfold DefectGapDyadicCost.coefficient;ring)
    have hn:=DefectGapMixture.cost_nonneg P hδ hΛp hρ hρ1 hh C hC (i:ℕ) hAmp (zero_le_one.trans hν)
    have hs:=pow_le_pow_left₀ hn hc' 2
    rw [mul_pow,←rpow_mul_natCast hνp.le] at hs
    exact hs.trans_eq (by congr 1;congr 1;ring)
  refine ⟨he.1,he.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  have hs:((N+1:ℕ):ℝ)*(∑i:Fin (N+1),Cs i^2*
      (DefectGapMixture.cost P δ C Λ ρ h (A*ν^(-β)) ν (i:ℕ))^2)≤
      ((N+1:ℕ):ℝ)*(∑i:Fin (N+1),Cs i^2*
        ((DefectGapDyadicCost.coefficient P δ C (i:ℕ) A η Λ ρ)^2*ν^(-2*(β-η)))):=by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hp i) (sq_nonneg (Cs i)))
  apply hs.trans_eq
  unfold coefficient
  simp_rw [←mul_assoc]
  rw [←Finset.sum_mul]
  ring
end SHE.MixedFirstDefectFiniteBandEnergy
