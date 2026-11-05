module

public import SHE.MixedMovingEnergy
public import SHE.MovingMeanPhysicalField
public import SHE.TripleEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MovingPastSpatialEnergy
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance movingPastSpatialEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance movingPastSpatialEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingPastSpatialEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingPastSpatialEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingPastSpatialEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingPastSpatialEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
local instance movingPastSpatialEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingPastSpatialEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingPastSpatialEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingPastSpatialEnergy_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- Integrate a genuine moving-clock section bound against the actual
past energy, retaining any separately measured output coordinate. The result uses the original global difference energy,
with no additional horizon or probability normalization factor. -/
theorem from_spatial_sections (hΛ : 0≤Λ) (hH : (H:ℝ)≤1)
    (Bfirst : ℝ≥0) (hBDG : StandardTerminalBDGPower 1 J Bfirst)
    {W : Type*} [MeasurableSpace W] (νω : Measure W) [SFinite νω]
    (h : ℝ≥0) (F : ℝ×(ℝ×W)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (B : ℝ→ℝ) (hB : Measurable B)
    (hBint : Integrable (fun s=>B s^2) (volume.restrict (Ioc (0:ℝ) (h:ℝ))))
    (hsection : ∀ v s,MovingMeanPhysicalField.valid H h v s→
      Integrable (fun ω=>‖F (v,(s,ω))‖^2) νω ∧
        (∫ ω,‖F (v,(s,ω))‖^2 ∂νω)≤C*B s^2*
          (∫ ω,‖S.second v.toNNReal ω-S.first v.toNNReal ω‖^2 ∂μ))
    (hzero : ∀ v s,¬MovingMeanPhysicalField.valid H h v s→∀ ω,F (v,(s,ω))=0) :
    let Mglobal:=MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    let νv:=volume.restrict (Ioc (0:ℝ) (H:ℝ))
    let νs:=volume.restrict (Ioc (0:ℝ) (h:ℝ))
    Integrable (fun z=>‖F z‖^2) (νv.prod (νs.prod νω)) ∧
      (∫ z,‖F z‖^2 ∂νv.prod (νs.prod νω))≤C*(∫ s in Ioc (0:ℝ) (h:ℝ),B s^2)*Mglobal := by
  intro Mglobal νv νs
  let Ee:=MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  let Kg : ℝ→ℝ≥0∞:=fun s=>ENNReal.ofReal (C*B s^2)
  have hKg : Measurable Kg:=ENNReal.measurable_ofReal.comp ((hB.pow_const 2).const_mul C)
  have hmass : (∫⁻ s in Ioc (0:ℝ) (h:ℝ),Kg s)=
      ENNReal.ofReal (C*(∫ s in Ioc (0:ℝ) (h:ℝ),B s^2)) := by
    rw [←integral_const_mul]
    exact (ofReal_integral_eq_lintegral_ofReal (hBint.const_mul C)
      (ae_of_all _ (fun s=>mul_nonneg hC (sq_nonneg (B s))))).symm
  have hb:=MixedMovingEnergy.past_window_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hΛ hH Bfirst hBDG Kg hKg (h:ℝ) (χ:=1) (by norm_num) (by norm_num)
  have hbound : (∫⁻ v in Ioc (0:ℝ) (H:ℝ),∫⁻ s in Ioc (0:ℝ) (h:ℝ),∫⁻ ω,
      ENNReal.ofReal (‖F (v,(s,ω))‖^2) ∂νω)≤
      ENNReal.ofReal (C*(∫ s in Ioc (0:ℝ) (h:ℝ),B s^2)*Mglobal) := by
    calc
      _≤∫⁻ v in Ioc (0:ℝ) (H:ℝ),∫⁻ s in Ioc (0:ℝ) (h:ℝ),Kg s*(Ee v)^1 := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hvI
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s _
        by_cases hv : MovingMeanPhysicalField.valid H h v s
        · have hs:=hsection v s hv
          rw [←ofReal_integral_eq_lintegral_ofReal hs.1 (ae_of_all _ (fun _=>sq_nonneg _))]
          have he : Ee v=ENNReal.ofReal (∫ ω,‖S.second v.toNNReal ω-S.first v.toNNReal ω‖^2 ∂μ) := by
            simp only [Ee,MixedMovingEnergy.ennEnergy,MixedMovingEnergy.realEnergy,
              indicator_of_mem hvI,MixedMovingEnergy.energy]
          refine (ENNReal.ofReal_le_ofReal hs.2).trans_eq ?_
          rw [ENNReal.rpow_one,he]
          exact ENNReal.ofReal_mul (mul_nonneg hC (sq_nonneg (B s)))
        · simp_rw [hzero v s hv]
          simp only [norm_zero,zero_pow (by decide : (2:ℕ)≠0),ENNReal.ofReal_zero,lintegral_zero]
          exact bot_le
      _≤_:=hb.trans_eq ?_
    rw [hmass,ENNReal.rpow_one,sub_self,ENNReal.rpow_zero,mul_one]
    exact (ENNReal.ofReal_mul (mul_nonneg hC (integral_nonneg (fun _=>sq_nonneg _)))).symm
  exact TripleEnergy.from_bound νv νs νω F hF
    (mul_nonneg (mul_nonneg hC (integral_nonneg (fun _=>sq_nonneg _)))
      (MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S)) hbound

end SHE.MovingPastSpatialEnergy
