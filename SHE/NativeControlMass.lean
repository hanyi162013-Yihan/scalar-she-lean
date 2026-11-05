module

public import SHE.ExponentialStopMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.NativeControlMass
open MeasureTheory Set PredictableL2
open scoped NNReal ENNReal

theorem continuous_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℝ≥0) {f : ℝ≥0→E} (hf : Continuous f) : Integrable f (timeMeasure q) := by
  have hi : Integrable (fun r : ℝ => f r.toNNReal) (volume.restrict (Ioc 0 (q:ℝ))) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (show 0≤(q:ℝ) from q.2)).mp
      ((hf.comp continuous_real_toNNReal).intervalIntegrable _ _)
  simpa only [Function.comp_def,Real.toNNReal_coe] using
    ((timeMeasurePreserving q).integrable_comp_emb nonnegative_coe_measurableEmbedding).mpr hi

theorem exponential_mass (Λ : ℝ) (q : ℝ≥0) :
    Λ*(∫ s,Real.exp (-Λ*((q:ℝ)-(s:ℝ))) ∂timeMeasure q)=1-Real.exp (-Λ*(q:ℝ)) := by
  rw [timeMeasure_integral]
  have he : (∫ s in Ioc (0:ℝ) (q:ℝ),Real.exp (-Λ*((q:ℝ)-(s.toNNReal:ℝ))))=
      ∫ s in (0:ℝ)..(q:ℝ),Real.exp (-Λ*((q:ℝ)-s)) := by
    rw [intervalIntegral.integral_of_le (show 0≤(q:ℝ) from q.2)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    change Real.exp (-Λ*((q:ℝ)-(s.toNNReal:ℝ)))=Real.exp (-Λ*((q:ℝ)-s))
    rw [Real.coe_toNNReal _ hs.1.le]
  rw [he,ExponentialStopMass.exponential_tail]
  simp only [sub_zero]

theorem centered_integral (Λ c : ℝ) (q : ℝ≥0) {f : ℝ≥0→ℝ} (hf : Integrable
    (fun s : ℝ≥0 => Real.exp (-Λ*((q:ℝ)-(s:ℝ)))*f s) (timeMeasure q)) :
    Λ*(∫ s,Real.exp (-Λ*((q:ℝ)-(s:ℝ)))*(f s-c) ∂timeMeasure q)=
      Λ*(∫ s,Real.exp (-Λ*((q:ℝ)-(s:ℝ)))*f s ∂timeMeasure q)-
        (1-Real.exp (-Λ*(q:ℝ)))*c := by
  have he : Integrable (fun s : ℝ≥0 => Real.exp (-Λ*((q:ℝ)-(s:ℝ)))) (timeMeasure q) :=
    continuous_integrable q (by fun_prop)
  have hh : (∫ s,Real.exp (-Λ*((q:ℝ)-(s:ℝ)))*(f s-c) ∂timeMeasure q)=
      (∫ s,Real.exp (-Λ*((q:ℝ)-(s:ℝ)))*f s ∂timeMeasure q)-
        (∫ s,Real.exp (-Λ*((q:ℝ)-(s:ℝ))) ∂timeMeasure q)*c := by
    rw [← integral_mul_const,← integral_sub hf (he.mul_const c)]
    apply integral_congr_ae
    filter_upwards with s
    ring
  rw [hh]
  calc
    _=Λ*(∫ s,Real.exp (-Λ*((q:ℝ)-(s:ℝ)))*f s ∂timeMeasure q)-
      (Λ*(∫ s,Real.exp (-Λ*((q:ℝ)-(s:ℝ))) ∂timeMeasure q))*c := by ring
    _=_ := by rw [exponential_mass]

end SHE.NativeControlMass
