module
public import SHE.MixedNativeSignedGammaInput
public import SHE.NativeGammaBandDensity
public import SHE.HeatBandMovingSignedOrder
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

namespace SHE.MixedNativeSignedGammaRows
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


def sectionEnergy {ρ:ℝ} (hL:1≤Λ) (hρ:0≤ρ) (A:ℝ) (j:ℕ) (v b:ℝ≥0) (τ:ℝ):ℝ≥0∞:=
  ∫⁻ω,ENNReal.ofReal ((NativeCanonicalGammaSharp.sharp (v:=v) (b:=b) (P:=P) A P.exponent j
      (((b:ℝ)-τ).toNNReal,ω))^2*
    (NativeHeatSpan.clock (NativeGammaClock.age v b (((b:ℝ)-τ).toNNReal,ω)))^(-(1/2:ℝ))*
      NativeSignedHaarProcess.inputEnergy hL hρ (cV (((b:ℝ)-τ).toNNReal,ω)) (cU (((b:ℝ)-τ).toNNReal,ω))) ∂μ
local notation "E"=>sectionEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
local notation "F"=>MixedNativeSignedGammaTime.realInputMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

theorem section_bound {ρ A:ℝ} (hL:1≤Λ) (hρ:0≤ρ) (j:ℕ) (v b:ℝ≥0)
    (hbH:b≤H) {τ:ℝ} (hτ:τ∈Set.Ioo (0:ℝ) ((b:ℝ)-(v:ℝ))):
    E hL hρ A j v b τ≤ENNReal.ofReal ((4*Real.pi^2)^(1/2:ℝ))*
      HeatBandCausalEnergy.kernel A P.exponent (ProfileVariance.lowerConstant*P.lower) j τ*
        F hL hρ ((b:ℝ)-τ):=by
  let q:ℝ≥0:=((b:ℝ)-τ).toNNReal
  have hq0:0<(b:ℝ)-τ:=by linarith [hτ.2,v.coe_nonneg]
  have hq:0<q:=Real.toNNReal_pos.mpr hq0
  have hqH:q≤H:=by
    exact_mod_cast (show (q:ℝ)≤(H:ℝ) by
      rw [Real.coe_toNNReal _ hq0.le]
      linarith [hτ.1,show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH])
  have hm:=MixedNativeCoefficientField.field_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hm':Measurable (fun ω=>ENNReal.ofReal (NativeSignedHaarProcess.inputEnergy hL hρ (cV (q,ω)) (cU (q,ω)))):=by
    have hs:=(((OneInputOperator.besselHalf Λ ρ hL hρ).continuous.measurable.comp
      ((hm.mono (predictable_le_product 𝓕)).measurable.comp ((measurable_const (a:=q)).prodMk measurable_id))).norm.pow_const 2).ennreal_ofReal
    simpa only [Function.comp_apply,id_eq,MixedNativeSignedGammaInput.input_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hL hρ] using hs
  calc
    _≤∫⁻ω,(ENNReal.ofReal ((4*Real.pi^2)^(1/2:ℝ))*
        HeatBandCausalEnergy.kernel A P.exponent (ProfileVariance.lowerConstant*P.lower) j τ)*
        ENNReal.ofReal (NativeSignedHaarProcess.inputEnergy hL hρ (cV (q,ω)) (cU (q,ω))) ∂μ:=by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [NativeGammaAgeValue.sharp P v b A P.exponent j hτ ω,NativeGammaAgeValue.age v b hτ ω]
      rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (NativeHeatSpan.clock_pos hτ.1).le _))]
      exact mul_le_mul' (NativeGammaBandDensity.signed_kernel (A:=A) P.exponent_le_one
        (mul_pos ProfileVariance.lowerConstant_pos P.lower_pos) hτ.1 j) le_rfl
    _=(ENNReal.ofReal ((4*Real.pi^2)^(1/2:ℝ))*
        HeatBandCausalEnergy.kernel A P.exponent (ProfileVariance.lowerConstant*P.lower) j τ)*
          (∫⁻ω,ENNReal.ofReal (NativeSignedHaarProcess.inputEnergy hL hρ (cV (q,ω)) (cU (q,ω))) ∂μ):=
      lintegral_const_mul _ hm'
    _=_:=by
      rw [MixedNativeSignedGammaInput.mass_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hL hρ q hq hqH]
      rw [show (q:ℝ)=(b:ℝ)-τ from Real.coe_toNNReal _ hq0.le]

/-- Full signed-factor Gamma input on the ORIGINAL past-then-age
measure, with the true residual-coefficient negative energy and the
sharp r^(2 beta) frequency power. All actual input/clock normalization
is checked before the convolution bound is applied. -/
theorem energy {ρ A h W:ℝ} (hL:1≤Λ) (hρ:0≤ρ) (hh:0<h) (hW:0≤W) (hcover:W+h≤H) (j:ℕ):
    (∫⁻v in Set.Ioc (0:ℝ) W,∫⁻τ in Set.Ioc (0:ℝ) h,E hL hρ A j v.toNNReal (v+h).toNNReal τ)≤
      ENNReal.ofReal ((4*Real.pi^2)^(1/2:ℝ))*
      ENNReal.ofReal ((A*ScalarHeatBandEnvelope.constant P.exponent 0)^2*
        ScalarHeatBandTime.massConstant P.exponent 0*(ProfileVariance.lowerConstant*P.lower)⁻¹*
          CompactMollifier.radius (j+1)^(2*P.exponent))*
            MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ:=by
  have hmem:∀ᵐτ∂volume.restrict (Set.Ioc (0:ℝ) h),τ∈Set.Ioo (0:ℝ) h:=by
    rw [←restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  calc
    _≤∫⁻v in Set.Ioc (0:ℝ) W,∫⁻τ in Set.Ioc (0:ℝ) h,
        ENNReal.ofReal ((4*Real.pi^2)^(1/2:ℝ))*
          HeatBandCausalEnergy.kernel A P.exponent (ProfileVariance.lowerConstant*P.lower) j τ*F hL hρ (v+h-τ):=by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      apply lintegral_mono_ae
      filter_upwards [hmem] with τ hτ
      have hcv:0≤v:=hv.1.le
      have hcb:0≤v+h:=by linarith
      have hb:(v+h).toNNReal≤H:=by
        exact_mod_cast (show ((v+h).toNNReal:ℝ)≤(H:ℝ) by rw [Real.coe_toNNReal _ hcb];linarith [hv.2,hcover])
      have ht:τ∈Set.Ioo (0:ℝ) (((v+h).toNNReal:ℝ)-(v.toNNReal:ℝ)):=by
        simpa only [Real.coe_toNNReal _ hcb,Real.coe_toNNReal _ hcv,add_sub_cancel_left] using hτ
      simpa only [Real.coe_toNNReal _ hcb] using section_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
        hL hρ j v.toNNReal (v+h).toNNReal hb ht
    _=ENNReal.ofReal ((4*Real.pi^2)^(1/2:ℝ))*
        (∫⁻v in Set.Ioc (0:ℝ) W,∫⁻τ in Set.Ioc (0:ℝ) h,
          HeatBandCausalEnergy.kernel A P.exponent (ProfileVariance.lowerConstant*P.lower) j τ*F hL hρ (v+h-τ)):=by
      simp_rw [mul_assoc,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _≤_:=by
      have hb:=HeatBandMovingSignedOrder.energy (A:=A) P.exponent_le_one
        (mul_pos ProfileVariance.lowerConstant_pos P.lower_pos) j (F hL hρ)
        (MixedNativeSignedGammaInput.realInputMass_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hL hρ) h W
      rw [MixedNativeSignedGammaTime.mass_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hL hρ] at hb
      have hm:=mul_le_mul' (le_refl (ENNReal.ofReal ((4*Real.pi^2)^(1/2:ℝ)))) hb
      simpa only [mul_assoc] using hm
end SHE.MixedNativeSignedGammaRows
