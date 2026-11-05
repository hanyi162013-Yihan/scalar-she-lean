module

public import SHE.PredictableTime
public import SHE.ProcessEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.CompanionHeat
open MeasureTheory Set AddCircle CircleHeat FiniteHaar CoefficientFields LowBands PredictableL2
open scoped ENNReal NNReal
local instance companionEnergy_circlePositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance companionEnergy_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
local instance companionEnergy_stateSigma : MeasurableSpace StateL2 := borel StateL2
local instance companionEnergy_stateBorel : BorelSpace StateL2 := ⟨rfl⟩

def columnEnergy (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀ z,|a z| ≤ M)
    (u v : StateL2) (t : ℝ) : ℝ := ∑' j : HaarNode,‖heat t (nonlinearColumn a ha M hM u v j)‖^2

theorem columnEnergy_nonneg (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀ z,|a z| ≤ M)
    (u v : StateL2) (t : ℝ) : 0 ≤ columnEnergy a ha M hM u v t := tsum_nonneg (fun _ => sq_nonneg _)

def picardConstant (ell M : ℝ) (L : ℝ≥0) : ℝ := signedL2HeatConstant ell M*(L:ℝ)^2

theorem picardConstant_nonneg {ell M : ℝ} (hM : 0 ≤ M) (L : ℝ≥0) : 0 ≤ picardConstant ell M L := by
  unfold picardConstant signedL2HeatConstant
  positivity

theorem columnEnergy_bound {a : ℝ → ℝ} (ha : Measurable a) {ell M : ℝ} (hell : 0 < ell)
    (haB : ∀ z,ell ≤ a z ∧ a z ≤ M) (hM : ∀ z,|a z| ≤ M) {L : ℝ≥0}
    (hLip : LipschitzWith L (fun z => (a z:ℂ))) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (u v : StateL2) : columnEnergy a ha M hM u v t ≤ picardConstant ell M L*t^(-(1/2:ℝ))*‖u-v‖^2 :=
  (smooth_heat_columns ha hell haB hLip ht ht1 u v).2

theorem columnEnergy_kernel_bound {a : ℝ → ℝ} (ha : Measurable a) {ell M : ℝ} (hell : 0 < ell)
    (haB : ∀ z,ell ≤ a z ∧ a z ≤ M) (hM : ∀ z,|a z| ≤ M) {L : ℝ≥0}
    (hLip : LipschitzWith L (fun z => (a z:ℂ))) {h t s : ℝ≥0} (hh : (h:ℝ) ≤ 1)
    (ht : t ≤ h) (hs : s < t) (u v : StateL2) :
    ENNReal.ofReal (columnEnergy a ha M hM u v ((t:ℝ)-(s:ℝ))) ≤
      ENNReal.ofReal (picardConstant ell M L)*picardKernel (h:ℝ) ((t:ℝ)-(s:ℝ))*
        ENNReal.ofReal (‖u-v‖^2) := by
  have hτ : 0 < (t:ℝ)-(s:ℝ) := sub_pos.mpr (by exact_mod_cast hs)
  have hτh : (t:ℝ)-(s:ℝ) ≤ (h:ℝ) := by
    have hh : (t:ℝ) ≤ (h:ℝ) := by exact_mod_cast ht
    linarith [s.2]
  have hτ1 : (t:ℝ)-(s:ℝ) ≤ 1 := hτh.trans hh
  have hC : 0 ≤ picardConstant ell M L := picardConstant_nonneg ((abs_nonneg (a 0)).trans (hM 0)) L
  have hk : picardKernel (h:ℝ) ((t:ℝ)-(s:ℝ))=ENNReal.ofReal (((t:ℝ)-(s:ℝ))^(-(1/2:ℝ))) := by
    unfold picardKernel
    exact Set.indicator_of_mem (show (t:ℝ)-(s:ℝ) ∈ Ioc 0 (h:ℝ) from ⟨hτ,hτh⟩) _
  rw [hk,← ENNReal.ofReal_mul hC,← ENNReal.ofReal_mul (mul_nonneg hC (Real.rpow_nonneg hτ.le _))]
  exact ENNReal.ofReal_le_ofReal (columnEnergy_bound ha hell haB hM hLip hτ hτ1 u v)

/-- The actual same-Haar nonlinear stochastic convolution has a short-time
L² Lipschitz energy constant. All heat, causal-time and coefficient
estimates are proved here; the stochastic isometry is applied afterwards. -/
theorem expected_causal_column_energy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {a : ℝ → ℝ} (ha : Measurable a) {ell M : ℝ} (hell : 0 < ell)
    (haB : ∀ z,ell ≤ a z ∧ a z ≤ M) (hM : ∀ z,|a z| ≤ M) {L : ℝ≥0}
    (hLip : LipschitzWith L (fun z => (a z:ℂ))) (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    (u v : ℝ≥0 × Ω → StateL2) (hu : Measurable u) (hv : Measurable v) :
    (∫⁻ t,∫⁻ s,∫⁻ ω,ENNReal.ofReal (columnEnergy a ha M hM (u (s,ω)) (v (s,ω)) ((t:ℝ)-(s:ℝ)))
      ∂μ ∂timeMeasure t ∂timeMeasure h) ≤
      ENNReal.ofReal (2*picardConstant ell M L*(h:ℝ)^(1/2:ℝ))*
        (∫⁻ s,∫⁻ ω,ENNReal.ofReal (‖u (s,ω)-v (s,ω)‖^2) ∂μ ∂timeMeasure h) := by
  let F (s : ℝ≥0) : ℝ≥0∞ := ∫⁻ ω,ENNReal.ofReal (‖u (s,ω)-v (s,ω)‖^2) ∂μ
  let C := ENNReal.ofReal (picardConstant ell M L)
  have hF : Measurable F :=
    (ENNReal.continuous_ofReal.measurable.comp ((hu.sub hv).norm.pow_const 2)).lintegral_prod_right'
  have hb : (∫⁻ t,∫⁻ s,∫⁻ ω,ENNReal.ofReal (columnEnergy a ha M hM (u (s,ω)) (v (s,ω)) ((t:ℝ)-(s:ℝ)))
      ∂μ ∂timeMeasure t ∂timeMeasure h) ≤
      ∫⁻ t,∫⁻ s,C*picardKernel (h:ℝ) ((t:ℝ)-(s:ℝ))*F s ∂timeMeasure t ∂timeMeasure h := by
    apply lintegral_mono_ae
    filter_upwards [timeMeasure_ae_mem h] with t ht
    apply lintegral_mono_ae
    filter_upwards [timeMeasure_ae_mem t,(timeMeasure t).ae_ne t] with s hs hst
    have hst' : s < t := lt_of_le_of_ne hs.2 hst
    calc
      _ ≤ ∫⁻ ω,C*picardKernel (h:ℝ) ((t:ℝ)-(s:ℝ))*ENNReal.ofReal (‖u (s,ω)-v (s,ω)‖^2) ∂μ :=
        lintegral_mono (fun ω => columnEnergy_kernel_bound ha hell haB hM hLip hh ht.2 hst' _ _)
      _ = _ := by
        have hk : picardKernel (h:ℝ) ((t:ℝ)-(s:ℝ)) ≠ ∞ := by
          classical
          by_cases hx : (t:ℝ)-(s:ℝ) ∈ Ioc 0 (h:ℝ) <;> simp [picardKernel,hx]
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hk)]
  calc
    _ ≤ _ := hb
    _ = C*(∫⁻ t,∫⁻ s,picardKernel (h:ℝ) ((t:ℝ)-(s:ℝ))*F s ∂timeMeasure t ∂timeMeasure h) := by
      have hC : C ≠ ∞ := ENNReal.ofReal_ne_top
      simp_rw [mul_assoc,lintegral_const_mul' C _ hC]
    _ ≤ C*(ENNReal.ofReal (2*(h:ℝ)^(1/2:ℝ))*(∫⁻ s,F s ∂timeMeasure h)) :=
      by
        exact mul_le_mul_right (predictable_picard_causal_energy h F hF) C
    _ = _ := by
      dsimp only [C,F]
      rw [← mul_assoc,← ENNReal.ofReal_mul (picardConstant_nonneg ((abs_nonneg (a 0)).trans (hM 0)) L)]
      congr 2
      ring

theorem expected_damped_causal_column_energy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {a : ℝ → ℝ} (ha : Measurable a) {ell M : ℝ} (hell : 0 < ell)
    (haB : ∀ z,ell ≤ a z ∧ a z ≤ M) (hM : ∀ z,|a z| ≤ M) {L : ℝ≥0}
    (hLip : LipschitzWith L (fun z => (a z:ℂ))) (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    (u v : ℝ≥0 × Ω → StateL2) (hu : Measurable u) (hv : Measurable v)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    (∫⁻ t,∫⁻ s,∫⁻ ω,ENNReal.ofReal (Real.exp (-2*Λ*((t:ℝ)-(s:ℝ)))*
      columnEnergy a ha M hM (u (s,ω)) (v (s,ω)) ((t:ℝ)-(s:ℝ)))
      ∂μ ∂timeMeasure t ∂timeMeasure h) ≤
      ENNReal.ofReal (2*picardConstant ell M L*(h:ℝ)^(1/2:ℝ))*
        (∫⁻ s,∫⁻ ω,ENNReal.ofReal (‖u (s,ω)-v (s,ω)‖^2) ∂μ ∂timeMeasure h) := by
  apply le_trans _ (expected_causal_column_energy μ ha hell haB hM hLip h hh u v hu hv)
  apply lintegral_mono
  intro t
  apply lintegral_mono_ae
  filter_upwards [timeMeasure_ae_mem t] with s hs
  apply lintegral_mono
  intro ω
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_of_le_one_left (columnEnergy_nonneg a ha M hM _ _ _)
  apply Real.exp_le_one_iff.mpr
  have hst : (s:ℝ) ≤ (t:ℝ) := by exact_mod_cast hs.2
  nlinarith

end SHE.CompanionHeat
