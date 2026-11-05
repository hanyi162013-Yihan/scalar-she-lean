module

public import SHE.HeatedCurrentInput
public import SHE.MixedNativePairFuture

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HeatedCurrentInput
open Set MeasureTheory ProbabilityTheory Real
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

theorem difference_even_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y Z : Ω→ℝ) (hY : Measurable Y) (hZ : Measurable Z) (n : ℕ)
    (hiY : Integrable (fun ω=>|Y ω|^(2*n)) μ)
    (hiZ : Integrable (fun ω=>|Z ω|^(2*n)) μ)
    {C : ℝ} (hbY : (∫ ω,|Y ω|^(2*n) ∂μ)≤C) (hbZ : (∫ ω,|Z ω|^(2*n) ∂μ)≤C) :
    Integrable (fun ω=>|Y ω-Z ω|^(2*n)) μ ∧
      (∫ ω,|Y ω-Z ω|^(2*n) ∂μ)≤2^(2*n)*C := by
  have hdom (ω : Ω) : |Y ω-Z ω|^(2*n)≤2^(2*n-1)*(|Y ω|^(2*n)+|Z ω|^(2*n)) :=
    (pow_le_pow_left₀ (abs_nonneg _) (by simpa only [Real.norm_eq_abs] using norm_sub_le (Y ω) (Z ω)) _).trans
      (add_pow_le (abs_nonneg _) (abs_nonneg _) _)
  have hi : Integrable (fun ω=>|Y ω-Z ω|^(2*n)) μ := by
    apply ((hiY.add hiZ).const_mul (2^(2*n-1))).mono'
      ((hY.sub hZ).norm.pow_const _).aestronglyMeasurable
    exact ae_of_all _ (fun ω=>by
      change ‖|Y ω-Z ω|^(2*n)‖≤_
      rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact hdom ω)
  refine ⟨hi,?_⟩
  have hb : (∫ ω,|Y ω-Z ω|^(2*n) ∂μ)≤2^(2*n-1)*(C+C) := by
    calc
      _≤∫ ω,2^(2*n-1)*(|Y ω|^(2*n)+|Z ω|^(2*n)) ∂μ :=
        integral_mono hi ((hiY.add hiZ).const_mul _) hdom
      _=2^(2*n-1)*((∫ ω,|Y ω|^(2*n) ∂μ)+(∫ ω,|Z ω|^(2*n) ∂μ)) := by
        rw [integral_const_mul,integral_add hiY hiZ]
      _≤_ := mul_le_mul_of_nonneg_left (add_le_add hbY hbZ) (by positivity)
  by_cases hn : n=0
  · subst n
    have hc : 1≤C := by simpa only [mul_zero,pow_zero,integral_const,probReal_univ,smul_eq_mul,mul_one] using hbY
    simpa only [mul_zero,pow_zero,integral_const,probReal_univ,smul_eq_mul,mul_one,one_mul] using hc
  · have he : (2:ℝ)^(2*n-1)*2=2^(2*n) := by
      rw [←pow_succ]
      congr 1
      omega
    exact hb.trans_eq (by rw [←two_mul,←mul_assoc,he])

end SHE.HeatedCurrentInput

namespace SHE.MixedHeatedDifferenceMoments
open Set MeasureTheory ProbabilityTheory Real PredictableL2 NativeHeatObservation
  NativeObservationNaturality FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance mixedHeatedDifference_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
local instance mixedHeatedDifference_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedHeatedDifference_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedHeatedDifference_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedHeatedDifference_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedHeatedDifference_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedHeatedDifference_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedHeatedDifference_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

def momentConstant (n : ℕ) (B : ℝ≥0) (κ M : ℝ) : ℝ :=
  2^(2*n)*NativeHybridMoments.momentConstant n B κ M

include hIJ₀ hIJ₁ in
/-- Genuine higher moments of the quarter-smoothed current difference
of the actual mixed pair with the same initial input. This uses bounded
raw noise and the universal BDG package, never Gaussianity of the state. -/
theorem even_moment (hΛ : 0≤Λ) (q : ℝ≥0) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    {τ : ℝ} (hτ : 0<τ) (x : HeatCircle) (n : ℕ) (B : ℝ≥0)
    (hBDG : StandardTerminalBDGPower n J B) :
    Integrable (fun ω=>|functional τ x (S.second q ω-S.first q ω)|^(2*n)) μ ∧
      (∫ ω,|functional τ x (S.second q ω-S.first q ω)|^(2*n) ∂μ)≤momentConstant n B κ M := by
  have hM : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hC : 0≤NativeHybridMoments.momentConstant n B κ M := by
    unfold NativeHybridMoments.momentConstant
    have hU := ProfileVariance.upperConstant_pos
    positivity
  have hU : Measurable (S.first q) :=
    ((S.first_predictable.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id)
  have hV : Measurable (S.second q) :=
    ((S.second_predictable.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id)
  let Y : ℝ→Ω→ℝ := fun θ ω=>functional τ x (S.first q ω+θ • (S.second q ω-S.first q ω))-
    functional ((q:ℝ)+τ) x u₀
  have hYm (θ : ℝ) : Measurable (Y θ) :=
    ((functional τ x).continuous.measurable.comp (hU.add ((hV.sub hU).const_smul θ))).sub_const _
  have hy (θ : ℝ) (hθ : |θ|≤1) : Integrable (fun ω=>|Y θ ω|^(2*n)) μ ∧
      (∫ ω,|Y θ ω|^(2*n) ∂μ)≤NativeHybridMoments.momentConstant n B κ M := by
    have ht : (q:ℝ)<(q:ℝ)+τ := by linarith
    have hid := MixedNativePairHybridIdentity.centered_current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hΛ q hqH ht x hθ
    have hh := NativeHybridMoments.fractional_moment 𝓕 μ H hκ hκ.le
      (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
      hell hM (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
      (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
      S.first_coefficient S.second_coefficient q ht x hΛ hθ J hqH hq1 n B hBDG
      (by norm_num : (0:ℝ)≤1) le_rfl
    have he : (fun ω=>|Y θ ω|^(2*n))=ᵐ[μ]
        fun ω=>|J.integral (MixedNativePairHybridIdentity.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
          I₀ I₁ u₀ u₀ S q ht x hΛ hθ) ω|^(2*n) := by
      filter_upwards [hid] with ω hω
      apply congrArg (fun z : ℝ=>|z|^(2*n))
      simpa only [Y,sub_self,map_zero,mul_zero,add_zero,add_sub_cancel_left] using hω
    dsimp only [NativeHybridMoments.value] at hh
    dsimp only [MixedNativePairHybridIdentity.input] at he
    have hi : Integrable (fun ω=>|Y θ ω|^(2*n)) μ := by
      apply (hh.1.congr ?_)
      simpa only [mul_one,Real.rpow_natCast] using he.symm
    have hb : (∫ ω,|Y θ ω|^(2*n) ∂μ)≤NativeHybridMoments.momentConstant n B κ M*(q:ℝ)^((n:ℝ)/2) := by
      rw [integral_congr_ae he]
      simpa only [Real.rpow_one,mul_one,Real.rpow_natCast] using hh.2
    exact ⟨hi,hb.trans (mul_le_of_le_one_right hC
      (Real.rpow_le_one q.2 hq1 (by positivity)))⟩
  have hh := HeatedCurrentInput.difference_even_moment μ (Y 1) (Y 0) (hYm 1) (hYm 0) n
    (hy 1 (by norm_num)).1 (hy 0 (by norm_num)).1 (hy 1 (by norm_num)).2 (hy 0 (by norm_num)).2
  have he (ω : Ω) : Y 1 ω-Y 0 ω=functional τ x (S.second q ω-S.first q ω) := by
    simp only [Y,one_smul,zero_smul,add_zero,map_add,map_sub,map_zero]
    ring
  simpa only [he,momentConstant] using hh

end SHE.MixedHeatedDifferenceMoments
