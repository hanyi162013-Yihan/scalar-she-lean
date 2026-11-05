module

public import SHE.WordRecursion

@[expose] public section
set_option autoImplicit false

/-! Differentiation of actual Gaussian averages of bounded smooth cylinders.
All derivatives below are derivatives of the displayed integrals. -/
noncomputable section
namespace SHE.GaussianSmooth
open Set MeasureTheory ProbabilityTheory Filter

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def average (μ : Measure E) (F : E → G) (z : E) : G := ∫ y, F (z + y) ∂μ

omit [NormedSpace ℝ G] in
theorem integrable_translate (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → G} (hF : Continuous F) {M : ℝ} (hB : ∀ z, ‖F z‖ ≤ M) (z : E) :
    Integrable (fun y => F (z + y)) μ := by
  exact (integrable_const M).mono' (hF.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    (Eventually.of_forall (fun y => hB (z + y)))

theorem continuous_average (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → G} (hF : Continuous F) {M : ℝ} (hB : ∀ z, ‖F z‖ ≤ M) :
    Continuous (average μ F) := by
  exact continuous_of_dominated
    (fun z => (hF.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    (fun z => Eventually.of_forall (fun y => hB (z + y))) (integrable_const M)
    (Eventually.of_forall (fun y => hF.comp (continuous_id.add continuous_const)))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
theorem average_norm_bound (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → G} {M : ℝ} (hB : ∀ z, ‖F z‖ ≤ M) (z : E) : ‖average μ F z‖ ≤ M := by
  simpa only [average, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall (fun y => hB (z + y)))

/-- A genuine Fréchet derivative under a probability integral, with the
constant domination supplied by the actual bounded derivative of the test. -/
theorem hasFDerivAt_average (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → G} (hF : ContDiff ℝ 1 F) {M L : ℝ}
    (hB : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L) (z : E) :
    HasFDerivAt (average μ F) (∫ y, fderiv ℝ F (z + y) ∂μ) z := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (F := fun z y => F (z + y)) (F' := fun z y => fderiv ℝ F (z + y))
    (bound := fun _ => L) (by simp)
  · exact Eventually.of_forall (fun z => (hF.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
  · exact integrable_translate μ hF.continuous hB z
  · exact ((hF.continuous_fderiv (by norm_num)).comp
      (continuous_const.add continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall (fun y z _ => hD (z + y))
  · exact integrable_const L
  · exact Eventually.of_forall (fun y z _ => by
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using (hF.differentiable (by norm_num) (z + y)).hasFDerivAt.comp z
        ((hasFDerivAt_id z).add_const y))

theorem fderiv_average (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → G} (hF : ContDiff ℝ 1 F) {M L : ℝ}
    (hB : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L) :
    fderiv ℝ (average μ F) = fun z => ∫ y, fderiv ℝ F (z + y) ∂μ := by
  funext z
  exact (hasFDerivAt_average μ hF hB hD z).fderiv

theorem hasFDerivAt_fderiv_average (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hB : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ B) (z : E) :
    HasFDerivAt (fderiv ℝ (average μ F))
      (∫ y, fderiv ℝ (fderiv ℝ F) (z + y) ∂μ) z := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  rw [fderiv_average μ hF1 hB hD]
  exact hasFDerivAt_average μ (hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)) hD hDD z

theorem fderiv_fderiv_average (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hB : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ B) :
    fderiv ℝ (fderiv ℝ (average μ F)) = average μ (fderiv ℝ (fderiv ℝ F)) := by
  funext z
  exact (hasFDerivAt_fderiv_average μ hF hB hD hDD z).fderiv

theorem average_fderiv_bound (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {M L : ℝ}
    (hB : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L) (z : E) :
    ‖fderiv ℝ (average μ F) z‖ ≤ L := by
  rw [fderiv_average μ hF hB hD]
  exact average_norm_bound μ hD z

theorem average_hessian_bound (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hB : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ B) (z : E) :
    ‖fderiv ℝ (fderiv ℝ (average μ F)) z‖ ≤ B := by
  rw [fderiv_fderiv_average μ hF hB hD hDD]
  exact average_norm_bound μ hDD z

theorem contDiff_average_two (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hB : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ B) : ContDiff ℝ 2 (average μ F) := by
  change ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (average μ F)
  rw [contDiff_succ_iff_fderiv]
  refine ⟨fun z => (hasFDerivAt_average μ (hF.of_le (by norm_num)) hB hD z).differentiableAt,
    by simp, ?_⟩
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun z => (hasFDerivAt_fderiv_average μ hF hB hD hDD z).differentiableAt, ?_⟩
  rw [fderiv_fderiv_average μ hF hB hD hDD]
  exact continuous_average μ ((hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv (by norm_num)) hDD

theorem average_hessian_lipschitz (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {M L B K : ℝ}
    (hB : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ B)
    (hLip : ∀ z w, ‖fderiv ℝ (fderiv ℝ F) w - fderiv ℝ (fderiv ℝ F) z‖ ≤ K * ‖w - z‖) (z w : E) :
    ‖fderiv ℝ (fderiv ℝ (average μ F)) w - fderiv ℝ (fderiv ℝ (average μ F)) z‖ ≤ K * ‖w - z‖ := by
  rw [fderiv_fderiv_average μ hF hB hD hDD]
  have hc := (hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv (by norm_num)
  have hiw := integrable_translate (F := fderiv ℝ (fderiv ℝ F)) μ hc hDD w
  have hiz := integrable_translate (F := fderiv ℝ (fderiv ℝ F)) μ hc hDD z
  change ‖(∫ y, fderiv ℝ (fderiv ℝ F) (w + y) ∂μ) - (∫ y, fderiv ℝ (fderiv ℝ F) (z + y) ∂μ)‖ ≤ _
  rw [← integral_sub hiw hiz]
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const (μ := μ)
    (Eventually.of_forall (fun y => by simpa only [add_sub_add_right_eq_sub] using hLip (z + y) (w + y)))

theorem hessian_average (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hB : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ B) (z d e : E) :
    fderiv ℝ (fderiv ℝ (average μ F)) z d e =
      ∫ y, fderiv ℝ (fderiv ℝ F) (z + y) d e ∂μ := by
  rw [(hasFDerivAt_fderiv_average μ hF hB hD hDD z).fderiv]
  have hc : Continuous (fderiv ℝ (fderiv ℝ F)) :=
    (hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv (by norm_num)
  have hi := integrable_translate (F := fderiv ℝ (fderiv ℝ F)) μ hc hDD z
  rw [ContinuousLinearMap.integral_apply hi, ContinuousLinearMap.integral_apply (hi.apply_continuousLinearMap d)]

theorem hasDerivAt_average_line (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) {M L : ℝ}
    (hB : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L) (d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => average μ F (s • d))
      (fderiv ℝ (average μ F) (t • d) d) t := by
  have hd := (hasFDerivAt_average μ hF hB hD (t • d)).comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const d)
  simpa only [Function.comp_def, id_eq, one_smul,
    (hasFDerivAt_average μ hF hB hD (t • d)).fderiv] using hd

theorem second_deriv_average_line (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hB : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ B) (d : E) :
    deriv (deriv (fun s : ℝ => average μ F (s • d))) 0 =
      ∫ y, fderiv ℝ (fderiv ℝ F) y d d ∂μ := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have he : deriv (fun s : ℝ => average μ F (s • d)) =
      fun s => fderiv ℝ (average μ F) (s • d) d := by
    funext s
    exact (hasDerivAt_average_line μ hF1 hB hD d s).deriv
  rw [he]
  have hline : HasDerivAt (fun t : ℝ => t • d) d 0 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const d
  have hg := (hasFDerivAt_fderiv_average μ hF hB hD hDD ((0 : ℝ) • d)).comp_hasDerivAt (0 : ℝ) hline
  have hd := (ContinuousLinearMap.apply ℝ ℝ d).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg
  have hh := hd.deriv
  simp only [Function.comp_def, zero_smul, zero_add, ContinuousLinearMap.apply_apply] at hh
  rw [hh]
  have hc : Continuous (fderiv ℝ (fderiv ℝ F)) :=
    (hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv (by norm_num)
  have hi := integrable_translate (F := fderiv ℝ (fderiv ℝ F)) μ hc hDD 0
  simp only [zero_add] at hi ⊢
  rw [ContinuousLinearMap.integral_apply hi, ContinuousLinearMap.integral_apply (hi.apply_continuousLinearMap d)]

/-- The rank-one Gaussian heat equation for an arbitrary fixed residual law.
The residual need not vanish along the varied direction. This is a derivative
of the actual variance-parametrized Gaussian law, with the actual Hessian. -/
theorem hasDerivAt_rankOne_variance_hessian (ν : Measure E) [IsProbabilityMeasure ν]
    (d : E) {v : ℝ} (hv : 0 < v) {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {M L B : ℝ} (hB : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ B) :
    HasDerivAt (fun w : ℝ => ∫ y, F y ∂GaussianAudit.rankOneGaussianLaw ν d w.toNNReal)
      ((1 / 2 : ℝ) * ∫ y, fderiv ℝ (fderiv ℝ F) y d d
        ∂GaussianAudit.rankOneGaussianLaw ν d v.toNNReal) v := by
  let μ := GaussianAudit.rankOneGaussianLaw ν d v.toNNReal
  have hFm : Measurable F := hF.continuous.measurable
  have hb : ∀ z, |F z| ≤ M := by simpa only [Real.norm_eq_abs] using hB
  have hAvgm := GaussianAudit.measurable_rankOneAverage ν d F hFm
  have hAvgb := GaussianAudit.rankOneAverage_bound ν d F M hb
  have hs := GaussianAudit.hasDerivAt_deriv_gaussianConvolution v.toNNReal (by positivity)
    (GaussianAudit.rankOneAverage ν d F) hAvgm M hAvgb 0
  have he : GaussianAudit.gaussianConvolution v.toNNReal (GaussianAudit.rankOneAverage ν d F) =
      fun s : ℝ => average μ F (s • d) := by
    rw [← GaussianAudit.rankOneMeanExpectation_eq_convolution ν d v.toNNReal F hFm M hb]
    funext s
    unfold GaussianAudit.rankOneMeanExpectation average
    congr 1
    funext y
    rw [add_comm]
  rw [he] at hs
  have hscore : (∫ z, GaussianAudit.rankOneAverage ν d F z * GaussianAudit.secondScore v.toNNReal z
      ∂gaussianReal 0 v.toNNReal) = ∫ y, fderiv ℝ (fderiv ℝ F) y d d ∂μ := by
    simpa only [zero_add] using hs.deriv.symm.trans (second_deriv_average_line μ hF hB hD hDD d)
  have hv' : (v.toNNReal : ℝ) = v := Real.coe_toNNReal _ hv.le
  have hh := GaussianAudit.hasDerivAt_gaussian_variance_integral v.toNNReal (by positivity)
    (GaussianAudit.rankOneAverage ν d F) hAvgm M hAvgb
  rw [hv', hscore] at hh
  apply hh.congr_of_eventuallyEq
  exact Eventually.of_forall (fun w => GaussianAudit.integral_rankOneGaussianLaw ν d w.toNNReal F hFm M hb)

end SHE.GaussianSmooth
