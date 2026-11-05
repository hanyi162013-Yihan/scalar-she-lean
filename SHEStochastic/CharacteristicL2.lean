module

public import SHEStochastic.GaussianCharacteristicDefect
public import MathFin.Foundations.FiniteMeasureCauchySchwarz
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.CharacteristicL2
open MeasureTheory ProbabilityTheory

theorem phase_lipschitz (x y : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ ≤ |x - y| := by
  have he : Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I) =
      (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) *
        Complex.exp ((y : ℂ) * Complex.I) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def expectation (x : Lp ℝ 2 μ) : ℂ := ∫ ω, Complex.exp ((x ω : ℂ) * Complex.I) ∂μ

theorem phase_integrable (z : Lp ℝ 2 μ) :
    Integrable (fun ω ↦ Complex.exp ((z ω : ℂ) * Complex.I)) μ :=
  Integrable.of_bound
    (Complex.continuous_exp.comp_aestronglyMeasurable
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable (Lp.aestronglyMeasurable z)).mul
        aestronglyMeasurable_const)) 1
    (Filter.Eventually.of_forall fun ω ↦ by simp)

/-- Characteristic expectations are contractions from L2 into C on a
probability space. This makes the limiting Gaussian-step argument a
direct consequence of convergence of the original integral classes. -/
theorem expectation_sub_le (x y : Lp ℝ 2 μ) :
    ‖expectation x - expectation y‖ ≤ ‖x - y‖ := by
  have hi := phase_integrable (μ := μ)
  have hs := MathFin.integral_abs_le_sqrt_integral_sq (Lp.memLp (x - y))
  rw [← MathFin.ItoIntegralL2.lp_two_norm_sq, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] at hs
  unfold expectation
  rw [← integral_sub (hi x) (hi y)]
  calc
    _ ≤ ∫ ω, |(x - y) ω| ∂μ :=
      norm_integral_le_of_norm_le ((Lp.memLp (x - y)).integrable (by norm_num)).abs
        (by
          filter_upwards [Lp.coeFn_sub x y] with ω hω
          rw [hω]
          exact phase_lipschitz (x ω) (y ω))
    _ ≤ _ := hs

theorem expectation_lipschitz : LipschitzWith 1 (expectation (μ := μ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using expectation_sub_le x y

theorem expectation_continuous : Continuous (expectation (μ := μ)) := expectation_lipschitz.continuous

def setExpectation (A : Set Ω) (x : Lp ℝ 2 μ) : ℂ :=
  ∫ ω in A, Complex.exp ((x ω : ℂ) * Complex.I) ∂μ

/-- The same contraction holds after testing against any past event.
This passes conditional Gaussian identities to the L2 limit. -/
theorem setExpectation_sub_le (A : Set Ω) (x y : Lp ℝ 2 μ) :
    ‖setExpectation A x - setExpectation A y‖ ≤ ‖x - y‖ := by
  have hi := ((Lp.memLp (x - y)).integrable (by norm_num)).abs
  have hs := MathFin.integral_abs_le_sqrt_integral_sq (Lp.memLp (x - y))
  rw [← MathFin.ItoIntegralL2.lp_two_norm_sq, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] at hs
  unfold setExpectation
  rw [← integral_sub (phase_integrable x).integrableOn (phase_integrable y).integrableOn]
  calc
    _ ≤ ∫ ω in A, |(x - y) ω| ∂μ := norm_integral_le_of_norm_le hi.integrableOn (by
      filter_upwards [(Lp.coeFn_sub x y).filter_mono ae_restrict_le] with ω hω
      rw [hω]
      exact phase_lipschitz (x ω) (y ω))
    _ ≤ ∫ ω, |(x - y) ω| ∂μ := integral_mono_measure μ.restrict_le_self
      (Filter.Eventually.of_forall fun ω ↦ abs_nonneg _) hi
    _ ≤ _ := hs

theorem setExpectation_continuous (A : Set Ω) : Continuous (setExpectation (μ := μ) A) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using setExpectation_sub_le A x y

def weightedExpectation (φ : Ω → ℂ) (x : Lp ℝ 2 μ) : ℂ :=
  ∫ ω, φ ω * Complex.exp ((x ω : ℂ) * Complex.I) ∂μ

theorem weightedExpectation_indicator {A : Set Ω} (hA : MeasurableSet A) (x : Lp ℝ 2 μ) :
    weightedExpectation (A.indicator (fun _ ↦ (1 : ℂ))) x = setExpectation A x := by
  unfold weightedExpectation setExpectation
  rw [← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards with ω
  by_cases hω : ω ∈ A
  · simp [Set.indicator_of_mem hω]
  · simp [Set.indicator_of_notMem hω]

theorem weighted_phase_integrable (φ : Ω → ℂ) (hφ : AEStronglyMeasurable φ μ)
    (hφbound : ∀ ω, ‖φ ω‖ ≤ 1) (x : Lp ℝ 2 μ) :
    Integrable (fun ω ↦ φ ω * Complex.exp ((x ω : ℂ) * Complex.I)) μ :=
  Integrable.of_bound (hφ.mul (phase_integrable x).aestronglyMeasurable) 1
    (Filter.Eventually.of_forall fun ω ↦ by simpa [norm_mul] using hφbound ω)

/-- Bounded past weights retain the same L2 contraction. -/
theorem weightedExpectation_sub_le (φ : Ω → ℂ) (hφ : AEStronglyMeasurable φ μ)
    (hφbound : ∀ ω, ‖φ ω‖ ≤ 1) (x y : Lp ℝ 2 μ) :
    ‖weightedExpectation φ x - weightedExpectation φ y‖ ≤ ‖x - y‖ := by
  have hs := MathFin.integral_abs_le_sqrt_integral_sq (Lp.memLp (x - y))
  rw [← MathFin.ItoIntegralL2.lp_two_norm_sq, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] at hs
  unfold weightedExpectation
  rw [← integral_sub (weighted_phase_integrable φ hφ hφbound x)
    (weighted_phase_integrable φ hφ hφbound y)]
  calc
    _ ≤ ∫ ω, |(x - y) ω| ∂μ :=
      norm_integral_le_of_norm_le ((Lp.memLp (x - y)).integrable (by norm_num)).abs (by
        filter_upwards [Lp.coeFn_sub x y] with ω hω
        rw [hω, ← mul_sub, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hφbound ω)).trans (phase_lipschitz _ _))
    _ ≤ _ := hs

theorem weightedExpectation_continuous (φ : Ω → ℂ) (hφ : AEStronglyMeasurable φ μ)
    (hφbound : ∀ ω, ‖φ ω‖ ≤ 1) : Continuous (weightedExpectation (μ := μ) φ) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
    weightedExpectation_sub_le φ hφ hφbound x y

end SHEStochastic.CharacteristicL2
