module

public import SHEStochastic.FiniteScalarIto
public import SHEStochastic.ConditionalGaussian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.FiniteScalarIto
open MeasureTheory ProbabilityTheory SHE Matrix
open scoped NNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {H : ℝ≥0}

/-- One predictable Gaussian step, in the full supplied filtration, with
random vector coefficients and repeated noise coordinates allowed.
This is the conditional characteristic-function identity used before
passing from predictable steps to general integral rows. -/
theorem condExp_gaussian_step (P : Family F μ H ι) {n : ℕ} (a : Fin n → ι)
    (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H)
    {R : Ω → WordRecursion.State n} (hR : Measurable[F s] R) :
    μ[fun ω ↦ Complex.exp ((inner ℝ
      (WithLp.toLp 2 (fun i ↦ P.W (a i) t ω - P.W (a i) s ω)) (R ω) : ℂ) * Complex.I)
      | F s] =ᵐ[μ]
    (fun ω ↦ Complex.exp (-((R ω ⬝ᵥ
      BrownianFiniteCovariance.matrix a (fun _ ↦ t - s) *ᵥ R ω : ℝ) : ℂ) / 2)) := by
  have hZ : Measurable (fun ω ↦ WithLp.toLp 2
      (fun i ↦ P.W (a i) t ω - P.W (a i) s ω)) :=
    (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
      (measurable_pi_iff.mpr fun i ↦ (measurable_coordinate P.toCoordinates (a i) t).sub
        (measurable_coordinate P.toCoordinates (a i) s))
  have hi := (P.law n a).2 s t hst htH
  have hl := BrownianShiftedFiniteLaw.law F μ H P.W P.law s (t - s)
    (by simpa only [add_tsub_cancel_of_le hst] using htH) a (fun _ ↦ t - s)
    (fun _ ↦ le_rfl)
  simp only [add_tsub_cancel_of_le hst] at hl
  exact ConditionalFreezing.condExp_multivariateGaussian (F s) (F.le s) hR hZ hi
    (BrownianFiniteCovariance.posSemidef a (fun _ ↦ t - s)) hl

theorem covariance_form_injective {n : ℕ} (a : Fin n → ι) (ha : Function.Injective a)
    (d : ℝ≥0) (r : WordRecursion.State n) :
    r ⬝ᵥ BrownianFiniteCovariance.matrix a (fun _ ↦ d) *ᵥ r =
      (d : ℝ) * ∑ i : Fin n, (r i) ^ 2 := by
  simp [BrownianFiniteCovariance.matrix, Matrix.mulVec, dotProduct, ha.eq_iff,
    Finset.mul_sum, pow_two, mul_comm, mul_left_comm, mul_assoc]

/-- Distinct original noise coordinates give the exact squared-row
variance. The row coefficient is random and known only at the left end. -/
theorem condExp_gaussian_step_injective (P : Family F μ H ι) {n : ℕ} (a : Fin n → ι)
    (ha : Function.Injective a) (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H)
    {R : Ω → WordRecursion.State n} (hR : Measurable[F s] R) :
    μ[fun ω ↦ Complex.exp ((inner ℝ
      (WithLp.toLp 2 (fun i ↦ P.W (a i) t ω - P.W (a i) s ω)) (R ω) : ℂ) * Complex.I)
      | F s] =ᵐ[μ]
    (fun ω ↦ Complex.exp (-(((t - s : ℝ≥0) : ℝ) * ∑ i : Fin n, (R ω i) ^ 2 : ℝ) / 2)) := by
  simpa only [covariance_form_injective a ha] using condExp_gaussian_step P a s t hst htH hR

end SHEStochastic.FiniteScalarIto
