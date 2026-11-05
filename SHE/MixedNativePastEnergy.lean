module

public import SHE.MixedMovingEnergy
public import SHE.ClippedPastEnergy
public import SHE.MixedMovingEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.MixedNativePastEnergy
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
variable (hΛ : 0≤Λ) (hH : (H:ℝ)≤1) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower 1 J B)
local notation "E"=>MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Ee"=>MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

include hIJ₀ hIJ₁ hΛ hH hBDG in
/-- The original moving-past energy is bounded by the TRUE global
same-driver solution energy. No uniform moment cap replaces it. -/
theorem mass_le {W:ℝ} (hW:W≤H):
    (∫⁻v in Ioc (0:ℝ) W,ENNReal.ofReal (E v.toNNReal))≤ENNReal.ofReal Global:=by
  calc
    _=(∫⁻v in Ioc (0:ℝ) W,Ee v):=by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      simp only [MixedMovingEnergy.ennEnergy,MixedMovingEnergy.realEnergy,
        indicator_of_mem (show v∈Ioc (0:ℝ) (H:ℝ) from ⟨hv.1,hv.2.trans hW⟩)]
    _≤(∫⁻v in Ioc (0:ℝ) (H:ℝ),Ee v):=
      lintegral_mono_set (Ioc_subset_Ioc_right hW)
    _=_:=MixedMovingEnergy.real_mass_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG

include hIJ₀ hIJ₁ hΛ hH hBDG in
theorem integrable {W:ℝ} (hW:W≤H):IntegrableOn (fun v:ℝ=>E v.toNNReal) (Ioc (0:ℝ) W):=by
  have hm:Measurable (fun v:ℝ=>E v.toNNReal):=
    (MixedMovingEnergy.energy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S).comp measurable_real_toNNReal
  refine ⟨hm.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>MixedMovingEnergy.energy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S _))]
  exact (mass_le 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG hW).trans_lt ENNReal.ofReal_lt_top

include hIJ₀ hIJ₁ hΛ hH hBDG in
theorem integral_le {W:ℝ} (hW:W≤H):
    (∫v in Ioc (0:ℝ) W,E v.toNNReal)≤Global:=by
  have hi:=integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG hW
  have hn(v:ℝ):0≤E v.toNNReal:=MixedMovingEnergy.energy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S _
  have he:=mass_le 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG hW
  rw [←ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hn)] at he
  have hb:=ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hn),
    ENNReal.toReal_ofReal (MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S)] using hb
end SHE.MixedNativePastEnergy
