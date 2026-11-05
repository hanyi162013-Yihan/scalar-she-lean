module
public import SHE.MixedNativeSignedGammaInput
public import SHE.MixedNativeSignedGammaRows
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

namespace SHE.MixedNativeSignedBudget
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


local notation "F"=>MixedNativeSignedGammaTime.realInputMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

def value {ρ:ℝ}(hL:1≤Λ)(hρ:0≤ρ)(A:ℝ)(j:ℕ)(h r:ℝ):ℝ≥0∞:=
  ENNReal.ofReal ((4*Real.pi^2)^(1/2:ℝ))*(∫⁻τ in Set.Ioc (0:ℝ) h,
    HeatBandCausalEnergy.kernel A P.exponent (ProfileVariance.lowerConstant*P.lower) j τ*F hL hρ (r+h-τ))
local notation "Value"=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P

theorem measurable {ρ A h:ℝ}(hL:1≤Λ)(hρ:0≤ρ)(j:ℕ):Measurable (Value hL hρ A j h):=by
  have hf:=MixedNativeSignedGammaInput.realInputMass_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hL hρ
  have hm:Measurable (fun p:ℝ×ℝ=>HeatBandCausalEnergy.kernel A P.exponent
      (ProfileVariance.lowerConstant*P.lower) j p.2*F hL hρ (p.1+h-p.2)):=
    ((HeatBandCausalEnergy.kernel_measurable A P.exponent (ProfileVariance.lowerConstant*P.lower) j).comp measurable_snd).mul
      (hf.comp ((measurable_fst.add_const h).sub measurable_snd))
  exact hm.lintegral_prod_right.const_mul _

/-- A genuinely jointly Borel signed-input budget dominates the actual
native signed factor at each original moving past. -/
theorem native_le {ρ A h r:ℝ}(hL:1≤Λ)(hρ:0≤ρ)(j:ℕ)(hr:0<r)(hh:0<h)(hcover:r+h≤H):
    (∫⁻τ in Set.Ioc (0:ℝ) h,MixedNativeSignedGammaRows.sectionEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ S P hL hρ A j r.toNNReal (r+h).toNNReal τ)≤Value hL hρ A j h r:=by
  have hb:(r+h).toNNReal≤H:=by
    exact_mod_cast (show ((r+h).toNNReal:ℝ)≤(H:ℝ) by rw [Real.coe_toNNReal _ (by linarith:0≤r+h)];exact hcover)
  calc
    _≤∫⁻τ in Set.Ioc (0:ℝ) h,ENNReal.ofReal ((4*Real.pi^2)^(1/2:ℝ))*
        HeatBandCausalEnergy.kernel A P.exponent (ProfileVariance.lowerConstant*P.lower) j τ*F hL hρ (r+h-τ):=by
      apply lintegral_mono_ae
      have hm:∀ᵐτ∂volume.restrict (Set.Ioc (0:ℝ) h),τ∈Set.Ioo (0:ℝ) h:=by
        rw [←restrict_Ioo_eq_restrict_Ioc]
        exact ae_restrict_mem measurableSet_Ioo
      filter_upwards [hm] with τ ht
      have ht':τ∈Set.Ioo (0:ℝ) (((r+h).toNNReal:ℝ)-(r.toNNReal:ℝ)):=by
        simpa only [Real.coe_toNNReal _ hr.le,Real.coe_toNNReal _ (by linarith:0≤r+h),add_sub_cancel_left] using ht
      simpa only [Real.coe_toNNReal _ (by linarith:0≤r+h)] using
        MixedNativeSignedGammaRows.section_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
          hL hρ j r.toNNReal (r+h).toNNReal hb ht'
    _=_:=by
      simp_rw [value,mul_assoc]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Actual measurable signed budget, with full band gain and the TRUE
same-driver negative input energy. -/
theorem energy {ρ A h W:ℝ}(hL:1≤Λ)(hρ:0≤ρ)(j:ℕ):
    (∫⁻r in Set.Ioc (0:ℝ) W,Value hL hρ A j h r)≤
      ENNReal.ofReal ((4*Real.pi^2)^(1/2:ℝ))*
      ENNReal.ofReal ((A*ScalarHeatBandEnvelope.constant P.exponent 0)^2*
        ScalarHeatBandTime.massConstant P.exponent 0*(ProfileVariance.lowerConstant*P.lower)⁻¹*
          CompactMollifier.radius (j+1)^(2*P.exponent))*
            MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ:=by
  rw [show (fun r=>Value hL hρ A j h r)=(fun r=>ENNReal.ofReal ((4*Real.pi^2)^(1/2:ℝ))*
      (∫⁻τ in Set.Ioc (0:ℝ) h,HeatBandCausalEnergy.kernel A P.exponent (ProfileVariance.lowerConstant*P.lower) j τ*
        F hL hρ (r+h-τ))) from rfl,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hb:=HeatBandMovingSignedOrder.energy (A:=A) P.exponent_le_one
    (mul_pos ProfileVariance.lowerConstant_pos P.lower_pos) j (F hL hρ)
    (MixedNativeSignedGammaInput.realInputMass_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hL hρ) h W
  rw [MixedNativeSignedGammaTime.mass_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hL hρ] at hb
  have hm:=mul_le_mul' (le_refl (ENNReal.ofReal ((4*Real.pi^2)^(1/2:ℝ)))) hb
  simpa only [mul_assoc] using hm
end SHE.MixedNativeSignedBudget
