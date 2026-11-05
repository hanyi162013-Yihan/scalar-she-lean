module

public import SHE.ScalarHeatLowBands
public import SHE.ScalarApproximationDiscrepancy
public import SHE.MixedMovingEnergy
public import SHE.MixedActualEnergyBridge
public import SHE.PredictableScalarField

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedNativeLowBandEnergy
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

local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable (D:SmoothApproximation.ScalarData)(n:ℕ)
local notation "a"=>D.smoothCoefficient n
local notation "ha"=>D.smooth_boundedSmooth n
local notation "hB"=>ScalarApproximationDiscrepancy.smooth_abs_bound D n
local notation "hHolder"=>D.smooth_holder n
local notation "LL"=>ScalarHeatLowBands.lip (B:=D.cap) (β:=D.beta) D.holderConstant_nonneg
local notation "Lip"=>ScalarHeatLowBands.complex_lipschitz ha hB D.holderConstant_nonneg
  D.beta_pos.le D.beta_le_one hHolder

def unit(N:ℕ)(z:ℝ≥0×Ω):CircleHeat.CircleL2:=
  ScalarHeatLowBands.comparison ha hB D.holderConstant_nonneg D.beta_pos.le D.beta_le_one hHolder
    N (S.second z.1 z.2) (S.first z.1 z.2)
local notation "Unit"=>unit 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n

theorem unit_ae(N:ℕ)(z:ℝ≥0×Ω):Unit N z=ᵐ[AddCircle.haarAddCircle]
    (fun x=>(ScalarHeatBands.smooth a N ((S.second z.1 z.2) x)-
      ScalarHeatBands.smooth a N ((S.first z.1 z.2) x):ℂ)):=
  ScalarHeatLowBands.comparison_ae ha hB D.holderConstant_nonneg D.beta_pos.le D.beta_le_one hHolder
    N (S.second z.1 z.2) (S.first z.1 z.2)

variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
def value(N:ℕ)(z:ℝ≥0×Ω):CircleL2:=OneInputOperator.besselHalf Λ ρ hL hρ (CircleNormalization.push (Unit N z))
local notation "Value"=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ

theorem unit_predictable(N:ℕ):StronglyMeasurable[𝓕.predictable] (Unit N):=by
  unfold unit ScalarHeatLowBands.comparison LowBands.comparison
  have ht(j:ℕ):StronglyMeasurable[𝓕.predictable] (fun z:ℝ≥0×Ω=>
      LowBands.composeBand (fun x=>(ScalarHeatBands.band a j x:ℂ)) (Lip j) (S.second z.1 z.2)-
        LowBands.composeBand (fun x=>(ScalarHeatBands.band a j x:ℂ)) (Lip j) (S.first z.1 z.2)):=by
    have hc:Continuous (LowBands.composeBand (fun x=>(ScalarHeatBands.band a j x:ℂ)) (Lip j)):=
      (LowBands.centered_lipschitz (Lip j)).continuous_compLp (by simp)
    exact (hc.comp_stronglyMeasurable S.second_predictable).sub (hc.comp_stronglyMeasurable S.first_predictable)
  convert! Finset.stronglyMeasurable_sum (Finset.range (N+1)) (fun j _=>ht j) using 1
  funext z
  simp only [Finset.sum_apply]

theorem value_predictable(N:ℕ):StronglyMeasurable[𝓕.predictable] (Value N):=
  (OneInputOperator.besselHalf Λ ρ hL hρ).continuous.comp_stronglyMeasurable
    (CircleNormalization.push.continuous.comp_stronglyMeasurable (unit_predictable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n N))

theorem norm_bound(hβ:D.beta<1)(N:ℕ)(z:ℝ≥0×Ω):
    ‖Value N z‖≤((ScalarHeatBandBernstein.amplitude D.cap D.holderConstant D.beta 1*
      LowBands.lowBandConstant D.beta)*Λ^(-ρ/2))*((2:ℝ)^N)^(1-D.beta)*
      ‖S.second z.1 z.2-S.first z.1 z.2‖:=by
  have he:=ScalarHeatLowBands.comparison_negative_norm (κ:=1) ha hB D.holderConstant_nonneg
    D.beta_pos.le D.beta_le_one hHolder (zero_lt_one.trans_le hL) hρ hβ N
      (S.second z.1 z.2) (S.first z.1 z.2)
  rw [←CircleNormalization.push_bessel_energy hL hρ,Real.sqrt_sq (norm_nonneg _)] at he
  exact he

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
include hIJ₀ hIJ₁ in
/-- Concrete original-clock low Gaussian-band comparison. Its one
Bernstein constant is chosen before the smooth companion index, and
its only state mass is the actual global difference energy. -/
theorem energy(hβ:D.beta<1)(hH:(H:ℝ)≤1)(B:ℝ≥0)(hBDG:StandardTerminalBDGPower 1 J B)(N:ℕ):
    let C:=ScalarHeatBandBernstein.amplitude D.cap D.holderConstant D.beta 1*LowBands.lowBandConstant D.beta
    let K:=(C*Λ^(-ρ/2))*((2:ℝ)^N)^(1-D.beta)
    Integrable (fun z=>‖Value N z‖^2) (energyMeasure μ H) ∧
      (∫z,‖Value N z‖^2 ∂energyMeasure μ H)≤K^2*
        MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S:=by
  intro C K
  have hm:=((value_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ N).mono
    (predictable_le_product 𝓕)).measurable
  have hinput:=MixedMovingEnergy.global_integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ (zero_le_one.trans hL) hH B hBDG
  have hpoint(z:ℝ≥0×Ω):‖Value N z‖^2≤K^2*‖S.second z.1 z.2-S.first z.1 z.2‖^2:=by
    have he:=pow_le_pow_left₀ (norm_nonneg _) (norm_bound
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ hβ N z) 2
    simpa only [mul_pow,mul_assoc,C,K] using he
  have hi:Integrable (fun z=>‖Value N z‖^2) (energyMeasure μ H):=
    (hinput.const_mul (K^2)).mono' (hm.norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ (fun z=>by simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hpoint z))
  refine ⟨hi,?_⟩
  have he:=integral_mono hi (hinput.const_mul (K^2)) hpoint
  simpa only [integral_const_mul,MixedMovingEnergy.globalEnergy] using he

include hIJ₀ hIJ₁ in
theorem root_energy(hβ:D.beta<1)(hH:(H:ℝ)≤1)(B:ℝ≥0)(hBDG:StandardTerminalBDGPower 1 J B)(N:ℕ):
    Real.sqrt (∫z,‖Value N z‖^2 ∂energyMeasure μ H)≤
      ((ScalarHeatBandBernstein.amplitude D.cap D.holderConstant D.beta 1*
        LowBands.lowBandConstant D.beta)*Λ^(-ρ/2))*((2:ℝ)^N)^(1-D.beta)*
      Real.sqrt (MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S):=by
  have he:=energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ J hIJ₀ hIJ₁ hβ hH B hBDG N
  let C:=ScalarHeatBandBernstein.amplitude D.cap D.holderConstant D.beta 1*LowBands.lowBandConstant D.beta
  let K:=(C*Λ^(-ρ/2))*((2:ℝ)^N)^(1-D.beta)
  have hC:0≤C:=mul_nonneg (ScalarHeatBandBernstein.amplitude_nonneg D.holderConstant_nonneg 1)
    (div_nonneg (Real.rpow_nonneg (by norm_num) _) (sub_nonneg.mpr
      (Real.one_le_rpow (by norm_num:(1:ℝ)≤2) (by linarith))))
  have hK:0≤K:=by dsimp only [K];positivity
  have hs:=Real.sqrt_le_sqrt he.2
  rw [Real.sqrt_mul (sq_nonneg K),Real.sqrt_sq hK] at hs
  exact hs

end SHE.MixedNativeLowBandEnergy
