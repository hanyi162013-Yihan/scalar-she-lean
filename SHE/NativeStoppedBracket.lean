module

public import SHE.NativeHeatPointBracket
public import SHE.StoppedItoInputs

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.NativeStoppedBracket
open Set MeasureTheory ProbabilityTheory Real PredictableL2 StoppedFourier FiniteHaar ProfileVariance
open scoped NNReal ENNReal
local instance : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- Stopping is carried out inside the same full-horizon predictable
space; no new stochastic integral is introduced at the smaller time. -/
theorem timeMeasure_before {H q : ℝ≥0} (hq : q ≤ H) :
    (timeMeasure H).restrict (Iio q) = timeMeasure q := by
  have he : Iio q =ᵐ[timeMeasure H] Ioc 0 q := by
    filter_upwards [timeMeasure_ae_mem H,(timeMeasure H).ae_ne q] with s hs hne
    simp only [mem_Iio,mem_Ioc]
    apply propext
    constructor
    · intro hsq
      exact ⟨hs.1,hsq.le⟩
    · intro hsq
      exact lt_of_le_of_ne hsq.2 hne
  rw [Measure.restrict_congr_set he,timeMeasure_restrict hq]

/-- The actual stopped observation row has the sharp small-time bracket
in the full horizon H. Its original target T may be smaller than H. -/
theorem bracket_bound {Ω : Type*} [MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H q : ℝ≥0) (hqH : q ≤ H) (hq1 : (q : ℝ) ≤ 1)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    {T : ℝ} (hT : (q : ℝ) < T) (x : HeatCircle) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖NativeObservationProcess.process 𝓕 μ H hell hM f hf hT x (s,ω)‖^2) ∂timeMeasure H) ≤
        ENNReal.ofReal (upperConstant*M*(q : ℝ)^(1/2 : ℝ)) := by
  have he := NativeObservationProcess.process_ae 𝓕 μ H hell hM f hf hT x
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  let K := M*(1+heatConstant)
  have hK : 0 ≤ K := mul_nonneg hM (by linarith [heatConstant_pos])
  calc
    _ ≤ ∫⁻ s, ENNReal.ofReal K *
        (Iio q).indicator (fun r : ℝ≥0 => ENNReal.ofReal (((q : ℝ)-(r : ℝ))^(-(1/2 : ℝ)))) s ∂timeMeasure H := by
      apply lintegral_mono_ae
      filter_upwards [hω] with s hrow
      simp only [Prod.swap] at hrow
      rw [hrow,NativeObservationProcess.integrand_eq hell f hT]
      by_cases hsq : s < q
      · have hsq' : (s : ℝ) < (q : ℝ) := by exact_mod_cast hsq
        rw [ite_eq_left hsq',Set.indicator_of_mem (show s ∈ Iio q from hsq),← ENNReal.ofReal_mul hK]
        apply ENNReal.ofReal_le_ofReal
        have hbefore : (s : ℝ)+T-(q : ℝ) < T := by linarith
        have hafter : (s : ℝ) ≤ (s : ℝ)+T-(q : ℝ) := by linarith
        have hb := NativeObservationProcess.row_norm_sq_bound hell (f (s,ω)) hbefore hafter x
        rw [show T-((s : ℝ)+T-(q : ℝ)) = (q : ℝ)-(s : ℝ) by ring] at hb
        have hage : (q : ℝ)-(s : ℝ) ≤ 1 := by linarith [s.2]
        have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos (sub_pos.mpr hsq') hage
          (by norm_num : -(1/2 : ℝ) ≤ 0)
        have hm := mul_le_mul_of_nonneg_left hp hM
        dsimp [K]
        nlinarith
      · have hsq' : ¬ (s : ℝ) < (q : ℝ) := by exact_mod_cast hsq
        rw [ite_eq_right hsq',Set.indicator_of_notMem (show s ∉ Iio q from hsq)]
        simp
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_indicator measurableSet_Iio,
        timeMeasure_before hqH,causal_rpow_mass (by norm_num : (-1 : ℝ) < -(1/2 : ℝ))]
      norm_num only [show -(1/2 : ℝ)+1 = 1/2 by norm_num]
      rw [← ENNReal.ofReal_mul hK]
      congr 1
      unfold K ProfileVariance.upperConstant
      ring

end SHE.NativeStoppedBracket
