module

public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.SubGaussianFourthMoment
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

private theorem fourth_le_exp (x : ℝ) :
    x ^ 4 ≤ 24 * (Real.exp x + Real.exp (-x)) := by
  by_cases hx : 0 ≤ x
  · have hh := Real.pow_div_factorial_le_exp x hx 4
    norm_num [Nat.factorial] at hh
    nlinarith [Real.exp_pos (-x)]
  · have hh := Real.pow_div_factorial_le_exp (-x) (neg_nonneg.mpr (le_of_not_ge hx)) 4
    norm_num [Nat.factorial, neg_pow] at hh
    nlinarith [Real.exp_pos x]

/-- A dimension-free fourth moment estimate with the square of the
sub-Gaussian variance parameter. The constant is deliberately inessential. -/
theorem integral_fourth_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) :
    (∫ ω, X ω ^ 4 ∂μ) ≤ 48 * Real.exp (1 / 2 : ℝ) * (c : ℝ) ^ 2 := by
  have hLp : MemLp X (4 : ℝ≥0∞) μ := by simpa using h.memLp (4 : ℝ≥0)
  have hi : Integrable (fun ω ↦ X ω ^ 4) μ :=
    (hLp.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)).mono'
      (h.aestronglyMeasurable.pow 4) (Filter.Eventually.of_forall fun ω ↦ by rw [norm_pow])
  by_cases hc : c = 0
  · subst c
    have hz : (∫ ω, X ω ^ 4 ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [h.ae_eq_zero_of_hasSubgaussianMGF_zero] with ω hω
      change X ω = 0 at hω
      change X ω ^ 4 = 0
      simp only [hω, zero_pow (by norm_num : 4 ≠ 0)]
    simp only [hz, NNReal.coe_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl]
  have hc0 : (c : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hc
  let a : ℝ := (Real.sqrt (c : ℝ))⁻¹
  have ha2 : a ^ 2 * (c : ℝ) = 1 := by
    dsimp [a]
    have hs0 : Real.sqrt (c : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne c.property hc0.symm))
    field_simp
    exact (Real.sq_sqrt c.property).symm
  have ha4 : a ^ 4 * (c : ℝ) ^ 2 = 1 := by
    nlinarith [congrArg (fun x : ℝ ↦ x ^ 2) ha2]
  have he : (c : ℝ) * a ^ 2 / 2 = (1 / 2 : ℝ) := by nlinarith [ha2]
  have hne : (c : ℝ) * (-a) ^ 2 / 2 = (1 / 2 : ℝ) := by rw [neg_sq, he]
  have hia := h.integrable_exp_mul a
  have hina := h.integrable_exp_mul (-a)
  have hb : a ^ 4 * (∫ ω, X ω ^ 4 ∂μ) ≤ 48 * Real.exp (1 / 2 : ℝ) := by
    calc
      _ = ∫ ω, (a * X ω) ^ 4 ∂μ := by simp only [mul_pow, integral_const_mul]
      _ ≤ ∫ ω, 24 * (Real.exp (a * X ω) + Real.exp (-a * X ω)) ∂μ := by
        apply integral_mono (by simpa only [mul_pow] using hi.const_mul (a ^ 4))
          ((hia.add hina).const_mul 24)
        intro ω
        change (a * X ω) ^ 4 ≤ 24 * (Real.exp (a * X ω) + Real.exp (-a * X ω))
        simpa only [neg_mul] using fourth_le_exp (a * X ω)
      _ = 24 * (mgf X μ a + mgf X μ (-a)) := by
        rw [integral_const_mul, integral_add hia hina]
        rfl
      _ ≤ _ := by
        have hh := h.mgf_le a
        have hn := h.mgf_le (-a)
        rw [he] at hh
        rw [hne] at hn
        linarith
  calc
    _ = (a ^ 4 * (∫ ω, X ω ^ 4 ∂μ)) * (c : ℝ) ^ 2 := by
      nlinarith [congrArg (fun x : ℝ ↦ x * (∫ ω, X ω ^ 4 ∂μ)) ha4]
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (sq_nonneg _)

end SHEStochastic.SubGaussianFourthMoment
