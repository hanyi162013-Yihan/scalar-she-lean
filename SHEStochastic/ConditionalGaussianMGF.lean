module

public import SHEStochastic.ConditionalFreezing
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.ConditionalGaussianMGF
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem integrable_exp_abs (v : ℝ≥0) (K : ℝ) :
    Integrable (fun z : ℝ ↦ Real.exp (K * |z|)) (gaussianReal 0 v) := by
  apply ((integrable_exp_mul_gaussianReal (μ := 0) (v := v) K).add
    (integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-K))).mono' (by fun_prop)
  filter_upwards with z
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos hz, mul_neg, ← neg_mul]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Exponential freezing for any bounded real parameter in the full
past and an independent centered Gaussian variable. Integrability is
proved, rather than made an additional input. -/
theorem freeze (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {X Z : Ω → ℝ} (hX : Measurable[m] X) (hZ : @Measurable Ω ℝ mΩ _ Z)
    {v : ℝ≥0} (hlaw : letI : MeasurableSpace Ω := mΩ; HasLaw Z (gaussianReal 0 v) μ)
    (hindep : @Indep Ω (MeasurableSpace.comap Z (borel ℝ)) m mΩ μ)
    (K : ℝ) (hK : ∀ ω, |X ω| ≤ K) :
    letI : MeasurableSpace Ω := mΩ
    Integrable (fun ω ↦ Real.exp (X ω * Z ω)) μ ∧
      μ[fun ω ↦ Real.exp (X ω * Z ω) | m] =ᵐ[μ]
        (fun ω ↦ Real.exp ((v : ℝ) * X ω ^ 2 / 2)) := by
  letI : MeasurableSpace Ω := mΩ
  have hXm : Measurable X := hX.mono hm le_rfl
  have hd : Integrable (fun ω ↦ Real.exp (K * |Z ω|)) μ :=
    hlaw.integrable_comp (integrable_exp_abs v K)
  have hi : Integrable (fun ω ↦ Real.exp (X ω * Z ω)) μ := by
    apply hd.mono' (by fun_prop)
    filter_upwards with ω
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    have hb : |X ω * Z ω| ≤ K * |Z ω| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hK ω) (abs_nonneg _)
    exact (le_abs_self _).trans hb
  refine ⟨hi, ?_⟩
  have hc := ConditionalFreezing.condExp_kernel_of_integrable m hm hX hZ hindep
    (Ψ := fun p : ℝ × ℝ ↦ Real.exp (p.1 * p.2)) (by fun_prop) hi
  have he (r : ℝ) : (∫ z : ℝ, Real.exp (r * z) ∂gaussianReal 0 v) =
      Real.exp ((v : ℝ) * r ^ 2 / 2) := by
    change mgf id (gaussianReal 0 v) r = _
    rw [mgf_id_gaussianReal]
    simp
  simpa only [hlaw.map_eq, he] using hc

/-- Conditional exponential compensation. Only an integrable exponential
and its exact conditional expectation are needed; the correction may be
unbounded as long as it is nonnegative and known in the past. -/
theorem compensate (m : MeasurableSpace Ω) (hm : m ≤ mΩ) {Y A : Ω → ℝ}
    (hi : letI : MeasurableSpace Ω := mΩ; Integrable (fun ω ↦ Real.exp (Y ω)) μ)
    (hA : StronglyMeasurable[m] A) (hA0 : ∀ ω, 0 ≤ A ω)
    (hCE : letI : MeasurableSpace Ω := mΩ
      μ[fun ω ↦ Real.exp (Y ω) | m] =ᵐ[μ] (fun ω ↦ Real.exp (A ω))) :
    letI : MeasurableSpace Ω := mΩ
    Integrable (fun ω ↦ Real.exp (Y ω - A ω)) μ ∧
      μ[fun ω ↦ Real.exp (Y ω - A ω) | m] =ᵐ[μ] fun _ ↦ 1 := by
  letI : MeasurableSpace Ω := mΩ
  let φ (ω : Ω) := Real.exp (-A ω)
  let f (ω : Ω) := Real.exp (Y ω)
  have hφ : StronglyMeasurable[m] φ := Real.continuous_exp.comp_stronglyMeasurable hA.neg
  have hφbound (ω : Ω) : ‖φ ω‖ ≤ 1 := by
    change ‖Real.exp (-A ω)‖ ≤ 1
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hA0 ω))
  have hprod : Integrable (fun ω ↦ φ ω * f ω) μ := by
    apply hi.mono' ((hφ.mono hm).aestronglyMeasurable.mul hi.aestronglyMeasurable)
    filter_upwards with ω
    change ‖φ ω * Real.exp (Y ω)‖ ≤ Real.exp (Y ω)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos (Y ω)).le]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (hφbound ω)
  have he : (fun ω ↦ φ ω * f ω) = (fun ω ↦ Real.exp (Y ω - A ω)) := by
    funext ω
    dsimp [φ, f]
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨by simpa only [← he] using hprod, ?_⟩
  rw [← he]
  have hp := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℝ) hφ hprod hi
  change μ[fun ω ↦ φ ω * f ω | m] =ᵐ[μ] (fun ω ↦ φ ω * μ[f | m] ω) at hp
  filter_upwards [hp, hCE] with ω hω hc
  rw [hω]
  change φ ω * μ[fun ω ↦ Real.exp (Y ω) | m] ω = 1
  rw [hc]
  dsimp [φ]
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- One normalized Gaussian exponential step has conditional mean one
in the original past, with its integrability proved from the bounded
past coefficient. -/
theorem density (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {X Z : Ω → ℝ} (hX : Measurable[m] X) (hZ : @Measurable Ω ℝ mΩ _ Z)
    {v : ℝ≥0} (hlaw : letI : MeasurableSpace Ω := mΩ; HasLaw Z (gaussianReal 0 v) μ)
    (hindep : @Indep Ω (MeasurableSpace.comap Z (borel ℝ)) m mΩ μ)
    (K : ℝ) (hK : ∀ ω, |X ω| ≤ K) :
    letI : MeasurableSpace Ω := mΩ
    Integrable (fun ω ↦ Real.exp (X ω * Z ω - (v : ℝ) * X ω ^ 2 / 2)) μ ∧
      μ[fun ω ↦ Real.exp (X ω * Z ω - (v : ℝ) * X ω ^ 2 / 2) | m] =ᵐ[μ] fun _ ↦ 1 := by
  letI : MeasurableSpace Ω := mΩ
  obtain ⟨hi, hCE⟩ := freeze m hm hX hZ hlaw hindep K hK
  have hA : StronglyMeasurable[m] (fun ω ↦ (v : ℝ) * X ω ^ 2 / 2) := by
    letI : MeasurableSpace Ω := m
    fun_prop
  exact compensate m hm hi hA (fun ω ↦
    div_nonneg (mul_nonneg v.coe_nonneg (sq_nonneg _)) (by norm_num)) hCE

end SHEStochastic.ConditionalGaussianMGF
