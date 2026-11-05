module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.GaussianMomentScaling
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

def moment (n : ℕ) : ℝ := ∫ x : ℝ, ‖x‖^(2*n) ∂gaussianReal 0 1

theorem moment_nonneg (n : ℕ) : 0 ≤ moment n := integral_nonneg fun _ ↦ by positivity

/-- Gaussian scaling gives all even moments with their exact variance
power. The numerical value of the universal standard-normal moment is
irrelevant for continuity and is deliberately left unevaluated. -/
theorem integral_even (v : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, ‖x‖^(2*n) ∂gaussianReal 0 v) = (v : ℝ)^n * moment n := by
  have hv : (NNReal.mk ((Real.sqrt (v : ℝ))^2) (sq_nonneg _)) * 1 = v := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one]
    exact Real.sq_sqrt v.coe_nonneg
  have hmap : (gaussianReal (0 : ℝ) 1).map (fun x : ℝ ↦ Real.sqrt (v : ℝ)*x) = gaussianReal 0 v := by
    simpa only [mul_zero, hv] using (gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := 1) (Real.sqrt (v : ℝ)))
  have hs : ‖Real.sqrt (v : ℝ)‖^(2*n) = (v : ℝ)^n := by
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), pow_mul]
    exact congrArg (fun r : ℝ ↦ r^n) (Real.sq_sqrt v.coe_nonneg)
  calc
    _ = ∫ x : ℝ, ‖Real.sqrt (v : ℝ)*x‖^(2*n) ∂gaussianReal 0 1 := by
      rw [← hmap]
      exact integral_map (by fun_prop) (by fun_prop)
    _ = ‖Real.sqrt (v : ℝ)‖^(2*n) * moment n := by
      simp only [norm_mul, mul_pow, integral_const_mul, moment]
    _ = _ := by rw [hs]

theorem law_even {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) μ) (n : ℕ) :
    (∫ sample, ‖X sample‖^(2*n) ∂μ) = (v : ℝ)^n * moment n :=
  (hX.integral_comp (by fun_prop)).trans (integral_even v n)

theorem law_sixteenth {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) μ) :
    (∫⁻ sample, ENNReal.ofReal (‖X sample‖^16) ∂μ) = ENNReal.ofReal ((v : ℝ)^8 * moment 8) := by
  have hp : MemLp X (16 : ℝ≥0∞) μ := hX.memLp (memLp_id_gaussianReal' 16 (by norm_num))
  rw [← ofReal_integral_eq_lintegral_ofReal (hp.integrable_norm_pow (by norm_num : (16 : ℕ) ≠ 0))
    (Filter.Eventually.of_forall fun _ ↦ by positivity)]
  exact congrArg ENNReal.ofReal (law_even hX 8)

end SHEStochastic.GaussianMomentScaling
