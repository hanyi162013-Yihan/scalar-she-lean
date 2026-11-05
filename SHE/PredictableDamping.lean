module

public import SHE.PredictableContraction
public import SHE.PredictableClock

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.PredictableDamping
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The clipped extension is globally bounded and agrees with the actual
exponential damping at every physical time before the terminal stop. -/
def weight (Λ T : ℝ) (p : ℝ≥0 × Ω) : ℝ :=
  Real.exp (-Λ * max (T - (p.1 : ℝ)) 0)

theorem weight_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (Λ T : ℝ) :
    StronglyMeasurable[𝓕.predictable] (weight (Ω := Ω) Λ T) := by
  have ht := PredictableClock.real_time_measurable 𝓕
  have hm := ((((measurable_const (a := T)).sub ht).max
    (measurable_const (a := (0 : ℝ)))).const_mul (-Λ)).exp
  exact hm.stronglyMeasurable

theorem weight_bound {Λ : ℝ} (hΛ : 0 ≤ Λ) (T : ℝ) (p : ℝ≥0 × Ω) :
    |weight Λ T p| ≤ 1 := by
  rw [weight, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΛ) (le_max_right _ _)

theorem weight_eq {Λ T : ℝ} {p : ℝ≥0 × Ω} (ht : (p.1 : ℝ) ≤ T) :
    weight Λ T p = Real.exp (-Λ * (T - (p.1 : ℝ))) := by
  rw [weight, max_eq_left (sub_nonneg.mpr ht)]

end SHE.PredictableDamping
