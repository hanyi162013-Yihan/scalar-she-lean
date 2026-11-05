module

public import SHE.GaussianExponentialNorm

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! Smooth vector Laplace transforms with bounded rough weights. The proof
uses actual Gaussian exponential integrability and differentiates the
displayed integrals; no regularity of the weight is assumed. -/
namespace SHE.GaussianLaplaceSmooth
open Set MeasureTheory ProbabilityTheory Real Filter
open scoped Topology InnerProductSpace

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def transform {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (μ : Measure E) (T : E → G) (a : E) : G :=
  ∫ y, exp (inner ℝ a y) • T y ∂μ

def step {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : E → G) (y : E) : E →L[ℝ] G := (innerSL ℝ y).smulRight (T y)

variable {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [CompleteSpace G]

omit [CompleteSpace G] in
theorem stronglyMeasurable_step {T : E → G} (hT : StronglyMeasurable T) :
    StronglyMeasurable (step T) := by
  have hL : StronglyMeasurable (fun y : E => innerSL ℝ y) :=
    (InnerProductSpace.toDual ℝ E).continuous.stronglyMeasurable
  exact (ContinuousLinearMap.smulRightL ℝ E G).continuous₂.comp_stronglyMeasurable
    (hL.prodMk hT)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace G] in
theorem step_growth {T : E → G} {C b : ℝ} (hC : 0 ≤ C)
    (hT : ∀ y, ‖T y‖ ≤ C * exp (b * ‖y‖)) (y : E) :
    ‖step T y‖ ≤ C * exp ((b + 1) * ‖y‖) := by
  rw [step, ContinuousLinearMap.norm_smulRight_apply]
  change ‖(InnerProductSpace.toDual ℝ E) y‖ * ‖T y‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    ‖y‖ * ‖T y‖ ≤ ‖y‖ * (C * exp (b * ‖y‖)) :=
      mul_le_mul_of_nonneg_left (hT y) (norm_nonneg _)
    _ ≤ exp ‖y‖ * (C * exp (b * ‖y‖)) :=
      mul_le_mul_of_nonneg_right (le_trans (le_add_of_nonneg_right zero_le_one) (add_one_le_exp _))
        (mul_nonneg hC (exp_pos _).le)
    _ = C * exp ((b + 1) * ‖y‖) := by rw [show (b + 1) * ‖y‖ = ‖y‖ + b * ‖y‖ by ring, exp_add]; ring

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace G] in
theorem weighted_norm_bound {T : E → G} {C b R : ℝ} (_hC : 0 ≤ C)
    (hT : ∀ y, ‖T y‖ ≤ C * exp (b * ‖y‖)) {a : E} (ha : ‖a‖ ≤ R) (y : E) :
    ‖exp (inner ℝ a y) • T y‖ ≤ C * exp ((b + R) * ‖y‖) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  have he : exp (inner ℝ a y) ≤ exp (R * ‖y‖) := by
    apply exp_le_exp.mpr
    exact (real_inner_le_norm a y).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
  calc
    _ ≤ exp (R * ‖y‖) * (C * exp (b * ‖y‖)) :=
      mul_le_mul he (hT y) (norm_nonneg _) (exp_pos _).le
    _ = _ := by rw [show (b + R) * ‖y‖ = R * ‖y‖ + b * ‖y‖ by ring, exp_add]; ring

omit [CompleteSpace G] in
theorem integrable_weighted (μ : Measure E) [IsGaussian μ] {T : E → G}
    (hT : StronglyMeasurable T) {C b : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ y, ‖T y‖ ≤ C * exp (b * ‖y‖)) (a : E) :
    Integrable (fun y => exp (inner ℝ a y) • T y) μ := by
  apply ((GaussianExponentialNorm.integrable_exp_norm μ (b + ‖a‖)).const_mul C).mono'
    (((continuous_const.inner continuous_id).rexp.stronglyMeasurable.smul hT).aestronglyMeasurable)
  exact ae_of_all _ (weighted_norm_bound hC hbound le_rfl)

omit [CompleteSpace G] in
theorem hasFDerivAt_transform (μ : Measure E) [IsGaussian μ] {T : E → G}
    (hT : StronglyMeasurable T) {C b : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ y, ‖T y‖ ≤ C * exp (b * ‖y‖)) (a₀ : E) :
    HasFDerivAt (transform μ T) (transform μ (step T) a₀) a₀ := by
  have hstep := stronglyMeasurable_step hT
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball a₀ 1)
    (F := fun a y => exp (inner ℝ a y) • T y)
    (F' := fun a y => exp (inner ℝ a y) • step T y)
    (bound := fun y => C * exp ((b + 1 + (‖a₀‖ + 1)) * ‖y‖))
    (Metric.ball_mem_nhds _ (by norm_num))
  · exact Eventually.of_forall (fun a =>
      ((continuous_const.inner continuous_id).rexp.stronglyMeasurable.smul hT).aestronglyMeasurable)
  · exact integrable_weighted μ hT hC hbound a₀
  · exact ((continuous_const.inner continuous_id).rexp.stronglyMeasurable.smul hstep).aestronglyMeasurable
  · apply ae_of_all
    intro y a ha
    apply weighted_norm_bound hC (step_growth hC hbound) _ y
    have hd : ‖a - a₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using ha
    exact (norm_le_norm_sub_add a a₀).trans (by linarith)
  · exact (GaussianExponentialNorm.integrable_exp_norm μ _).const_mul C
  · apply ae_of_all
    intro y a _
    have hl : HasFDerivAt (fun x : E => inner ℝ x y) (innerSL ℝ y) a := by
      convert! (innerSL ℝ y).hasFDerivAt (x := a) using 1
      funext x
      exact (real_inner_comm x y).symm
    convert! (hl.exp.smul_const (T y)) using 1
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply,
      step, smul_smul, innerSL_apply_apply, smul_eq_mul]

/-- Every finite order of actual Fréchet smoothness follows from the
Gaussian exponential envelope, even for a merely measurable weight. -/
theorem contDiff_transform (k : ℕ) (μ : Measure E) [IsGaussian μ] {T : E → G}
    (hT : StronglyMeasurable T) {C b : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ y, ‖T y‖ ≤ C * exp (b * ‖y‖)) :
    ContDiff ℝ k (transform μ T) := by
  induction k generalizing G b with
  | zero =>
      change ContDiff ℝ 0 (transform μ T)
      rw [contDiff_zero]
      exact continuous_iff_continuousAt.mpr
        (fun a => (hasFDerivAt_transform μ hT hC hbound a).continuousAt)
  | succ k ih =>
      change ContDiff ℝ ((k : WithTop ℕ∞) + 1) (transform μ T)
      rw [contDiff_succ_iff_fderiv]
      refine ⟨fun a => (hasFDerivAt_transform μ hT hC hbound a).differentiableAt, by simp, ?_⟩
      have he : fderiv ℝ (transform μ T) = transform μ (step T) :=
        funext (fun a => (hasFDerivAt_transform μ hT hC hbound a).fderiv)
      rw [he]
      exact ih (stronglyMeasurable_step hT) (step_growth hC hbound)

end SHE.GaussianLaplaceSmooth
