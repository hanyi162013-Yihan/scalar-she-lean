module

public import SHE.StandardTerminalBDG
public import SHE.DampedFixedIntegral
public import SHE.DampedIncrementBracket

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.DampedTerminalMoments
open MeasureTheory Set PredictableL2 CircleHeat FiniteHaar
open scoped NNReal ENNReal

def momentConstant (B : ℝ≥0) (Λ M : ℝ) : ℝ := (B:ℝ)*(DampedIncrementEnergy.incrementConstant Λ M)^8

theorem momentConstant_nonneg (B : ℝ≥0) (Λ M : ℝ) : 0 ≤ momentConstant B Λ M := by
  unfold momentConstant
  positivity

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Actual sixteen-moment time-increment estimate. The only moment
premise is universal Hilbert BDG; all physical heat, column, pathwise
bracket, singular time and stopping bounds are proved. -/
theorem increment_moment16 (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := LowBands.StateL2) 𝓕 μ h)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
    (s t : ℝ≥0) (hst : s ≤ t) (hth : t ≤ h) :
    (∫⁻ ω,ENNReal.ofReal
      (‖DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I t hth ω-
        DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I s (hst.trans hth) ω‖^16) ∂μ) ≤
      ENNReal.ofReal (momentConstant B Λ M*((t:ℝ)-(s:ℝ))^2) := by
  let V : Process (E := RealHaarIntegrand.Columns) 𝓕 μ h :=
    DampedFixedIntegral.input 𝓕 μ h hh hΛ hell hM f hf t hth-
      DampedFixedIntegral.input 𝓕 μ h hh hΛ hell hM f hf s (hst.trans hth)
  have hδ : 0 ≤ (t:ℝ)-(s:ℝ) := sub_nonneg.mpr (by exact_mod_cast hst)
  have hCδ : 0 ≤ DampedIncrementEnergy.incrementConstant Λ M*((t:ℝ)-(s:ℝ))^(1/4:ℝ) :=
    mul_nonneg (DampedIncrementEnergy.incrementConstant_nonneg hM) (Real.rpow_nonneg hδ _)
  have hlin : I.integral V=DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I t hth-
      DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I s (hst.trans hth) := map_sub _ _ _
  have hleft : (∫⁻ ω,ENNReal.ofReal
      (‖DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I t hth ω-
        DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I s (hst.trans hth) ω‖^16) ∂μ)=
      ∫⁻ ω,ENNReal.ofReal (‖I.integral V ω‖^16) ∂μ := by
    rw [hlin]
    apply lintegral_congr_ae
    filter_upwards [Lp.coeFn_sub
      (DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I t hth)
      (DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I s (hst.trans hth))] with ω hω
    rw [hω]
    rfl
  have hbr := DampedIncrementBracket.bracket_bound 𝓕 μ h hh hΛ hell hM f hf s t hst hth
  have hpower : (∫⁻ ω,(∫⁻ r,ENNReal.ofReal (‖V (r,ω)‖^2) ∂timeMeasure h)^8 ∂μ) ≤
      (ENNReal.ofReal (DampedIncrementEnergy.incrementConstant Λ M*((t:ℝ)-(s:ℝ))^(1/4:ℝ)))^8 := by
    have hb := lintegral_mono_ae (hbr.mono (fun ω hω => pow_le_pow_left₀ (by simp) hω 8))
    simpa only [lintegral_const,measure_univ,mul_one] using hb
  calc
    _ = ∫⁻ ω,ENNReal.ofReal (‖I.integral V ω‖^16) ∂μ := hleft
    _ ≤ _ := hBDG V
    _ ≤ (B:ℝ≥0∞)*(ENNReal.ofReal (DampedIncrementEnergy.incrementConstant Λ M*((t:ℝ)-(s:ℝ))^(1/4:ℝ)))^8 :=
      mul_le_mul_right hpower (B:ℝ≥0∞)
    _ = _ := by
      rw [← ENNReal.ofReal_pow hCδ,show (B:ℝ≥0∞)=ENNReal.ofReal (B:ℝ) by simp]
      have hmul : ENNReal.ofReal (B:ℝ)*
          ENNReal.ofReal ((DampedIncrementEnergy.incrementConstant Λ M*((t:ℝ)-(s:ℝ))^(1/4:ℝ))^8)=
          ENNReal.ofReal ((B:ℝ)*(DampedIncrementEnergy.incrementConstant Λ M*((t:ℝ)-(s:ℝ))^(1/4:ℝ))^8) :=
        (ENNReal.ofReal_mul B.2).symm
      rw [hmul]
      congr 1
      rw [mul_pow,← Real.rpow_mul_natCast hδ]
      norm_num only [Nat.cast_ofNat,show (1/4:ℝ)*8=2 by norm_num,Real.rpow_two]
      unfold momentConstant
      ring

theorem symmetric_increment_moment16 (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := LowBands.StateL2) 𝓕 μ h)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
    (s t : ℝ≥0) (hsh : s ≤ h) (hth : t ≤ h) :
    (∫⁻ ω,ENNReal.ofReal
      (‖DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I s hsh ω-
        DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I t hth ω‖^16) ∂μ) ≤
      ENNReal.ofReal (momentConstant B Λ M*((s:ℝ)-(t:ℝ))^2) := by
  rcases le_total s t with hst | hts
  · have he : (∫⁻ ω,ENNReal.ofReal
        (‖DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I s hsh ω-
          DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I t hth ω‖^16) ∂μ)=
        ∫⁻ ω,ENNReal.ofReal
        (‖DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I t hth ω-
          DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I s hsh ω‖^16) ∂μ := by
      apply lintegral_congr
      intro ω
      rw [norm_sub_rev]
    rw [he]
    apply (increment_moment16 𝓕 μ h hh hΛ hell hM f hf I B hBDG s t hst hth).trans_eq
    congr 1
    ring
  · exact increment_moment16 𝓕 μ h hh hΛ hell hM f hf I B hBDG t s hts hsh

end SHE.DampedTerminalMoments
