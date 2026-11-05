module

public import SHE.MixedNativePastEnergy
public import SHE.ClippedPastEnergy
public import SHE.MixedMovingEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.MixedNativePastBudget
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance mixedNativeMovingCurrentGamma_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedNativeMovingCurrentGamma_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance mixedNativeMovingCurrentGamma_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedNativeMovingCurrentGamma_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedNativeMovingCurrentGamma_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_blockSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedNativeMovingCurrentGamma_blockBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance mixedNativeMovingCurrentGamma_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance mixedNativeMovingCurrentGamma_unitPos : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance mixedNativeMovingCurrentGamma_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance mixedNativeMovingCurrentGamma_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hΛ : 0≤Λ) (hH : (H:ℝ)≤1) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower 1 J B)local notation "E"=>MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

include hIJ₀ hIJ₁ hΛ hH hBDG in
/-- Section budgets linear in actual past energy integrate into the
true global energy even when parameterwise stochastic versions have
not yet been identified on one joint event. -/
theorem linear {W C:ℝ} (hW:W≤H) (hC:0≤C) (G:ℝ→ℝ≥0∞)
    (hG:∀v∈Ioc (0:ℝ) W,G v≤ENNReal.ofReal (C*E v.toNNReal)):
    (∫⁻v in Ioc (0:ℝ) W,G v)≤ENNReal.ofReal (C*Global):=by
  calc
    _≤∫⁻v in Ioc (0:ℝ) W,ENNReal.ofReal (C*E v.toNNReal):=by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      exact hG v hv
    _=ENNReal.ofReal C*(∫⁻v in Ioc (0:ℝ) W,ENNReal.ofReal (E v.toNNReal)):=by
      simp_rw [ENNReal.ofReal_mul hC]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _≤ENNReal.ofReal C*ENNReal.ofReal Global:=
      mul_le_mul' le_rfl (MixedNativePastEnergy.mass_le 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG hW)
    _=_:=(ENNReal.ofReal_mul hC).symm

include hIJ₀ hIJ₁ hΛ hH hBDG in
/-- Frozen-root clipping is performed AFTER the actual moving-past
average. The only mass is the same-driver global solution energy. -/
theorem clipped {W C K r:ℝ} (hW0:0≤W) (hW:W≤H) (hC:0≤C) (hK:0≤K) (hr:0<r)
    (G:ℝ→ℝ≥0∞) (hG:∀v∈Ioc (0:ℝ) W,G v≤ENNReal.ofReal (C*min 1 (K*E v.toNNReal/r^2))):
    (∫⁻v in Ioc (0:ℝ) W,G v)≤ENNReal.ofReal (C*min 1 (K*Global/r^2)):=by
  let ν:=volume.restrict (Ioc (0:ℝ) W)
  have hmass:ν.real univ≤1:=by
    have he:ν.real univ=W:=by
      simp [ν,measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioc,hW0]
    rw [he]
    exact hW.trans hH
  have hm:Measurable (fun v:ℝ=>E v.toNNReal):=
    (MixedMovingEnergy.energy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S).comp measurable_real_toNNReal
  have hi:=MixedNativePastEnergy.integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG hW
  have hn(v:ℝ):0≤E v.toNNReal:=MixedMovingEnergy.energy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S _
  have hL:=MixedNativePastEnergy.integral_le 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG hW
  calc
    _≤(∫⁻v,ENNReal.ofReal (C*min 1 (K*E v.toNNReal/r^2)) ∂ν):=by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      exact hG v hv
    _≤ENNReal.ofReal (C*min 1 (K*(∫v,E v.toNNReal ∂ν)/r^2)):=
      ClippedPastEnergy.iterated_bound ν hmass (fun v=>E v.toNNReal) hm hi hn hK hr hC _ (fun _=>le_rfl)
    _≤_:=by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ hC
      apply min_le_min le_rfl
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL hK) (sq_nonneg r)
end SHE.MixedNativePastBudget
