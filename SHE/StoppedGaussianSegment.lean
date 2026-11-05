module

public import SHE.EllipticGaussianSegment
public import SHE.StoppedUniformScoreMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.StoppedGaussianSegment
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier StoppedGaussianFeatures
  GaussianProfileMark GaussianIncrement GaussianConvolution
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

/-- Exact bounded signed-profile Gram identity at every original lower
cutoff. Zero future-age observations and singular Gram matrices are allowed. -/
theorem profileCovariance_eq (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hages : ∀ i,σ i≤target i) (q : ℝ) (c : Domain→ℝ) (hc : Measurable c)
    {M : ℝ} (hb : ∀ p,|c p|≤M) :
    profileCovariance (historyMeasure q) c (stoppedRow σ target center)=
      stoppedCovariance σ target center c q := by
  have hr := StoppedScoreLeverage.row_energy_integrable σ target center hages q
  have hi : Integrable (fun p=>|c p| *‖stoppedRow σ target center p‖^2) (historyMeasure q) := by
    apply (hr.const_mul M).mono'
      (((continuous_abs.measurable.comp hc).mul
        ((stoppedRow_measurable σ target center).norm.pow_const 2)).aestronglyMeasurable)
    apply ae_of_all
    intro p
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hb p) (sq_nonneg _)
  have hm := profileCovariance_integrable (historyMeasure q) c (stoppedRow σ target center)
    hc.aestronglyMeasurable (stoppedRow_measurable σ target center).aestronglyMeasurable hi
  ext i j
  exact profileCovariance_entries (historyMeasure q) c (stoppedRow σ target center) hm i j

/-- Literal finite stopped-covariance comparison under the true affine
coefficient law. Every original stop and target is retained, including a
newest stop=target=q. No positive final reserve or future heat gap is added. -/
theorem covariance_ftc (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hages : ∀ i,σ i≤target i) (q : ℝ) (c₀ c₁ : Domain→ℝ)
    (hc₀ : Measurable c₀) (hc₁ : Measurable c₁) {ell M : ℝ} (hell : 0<ell)
    (h₀ : ∀ p,ell≤c₀ p ∧ c₀ p≤M) (h₁ : ∀ p,ell≤c₁ p ∧ c₁ p≤M)
    (F : State n→ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ y,|F y|≤B) (mean : State n) :
    let mark:=fun t=>FiniteWordScores.covarianceMark (historyMeasure q)
      (stoppedCovariance σ target center (EllipticGaussianSegment.segment c₀ c₁ t) q)
      (fun p=>c₁ p-c₀ p) (stoppedRow σ target center) F mean
    IntervalIntegrable mark volume 0 1 ∧ (∫ t in (0:ℝ)..1,mark t)=
      gaussianAverage (stoppedCovariance σ target center c₁ q) F mean-
        gaussianAverage (stoppedCovariance σ target center c₀ q) F mean := by
  intro mark
  have hb₀ (p) : |c₀ p|≤M := by rw [abs_of_nonneg (hell.le.trans (h₀ p).1)]; exact (h₀ p).2
  have hb₁ (p) : |c₁ p|≤M := by rw [abs_of_nonneg (hell.le.trans (h₁ p).1)]; exact (h₁ p).2
  have hseg (t) : Measurable (EllipticGaussianSegment.segment c₀ c₁ t) :=
    (hc₀.const_mul (1-t)).add (hc₁.const_mul t)
  have hsegb (t p) : |EllipticGaussianSegment.segment c₀ c₁ t p|≤(|1-t|+|t|)*M := by
    calc
      _≤|(1-t)*c₀ p|+|t*c₁ p|:=by
        simpa only [EllipticGaussianSegment.segment,Real.norm_eq_abs] using
          norm_add_le ((1-t)*c₀ p) (t*c₁ p)
      _=|1-t| * |c₀ p|+|t| * |c₁ p|:=by rw [abs_mul,abs_mul]
      _≤|1-t| * M+|t| * M:=add_le_add
        (mul_le_mul_of_nonneg_left (hb₀ p) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hb₁ p) (abs_nonneg _))
      _=_:=by ring
  have he (t) := profileCovariance_eq σ target center hages q _ (hseg t) (hsegb t)
  have he₀:=profileCovariance_eq σ target center hages q c₀ hc₀ hb₀
  have he₁:=profileCovariance_eq σ target center hages q c₁ hc₁ hb₁
  have hh:=EllipticGaussianSegment.covariance_ftc (historyMeasure q) c₀ c₁ hc₀ hc₁ hell h₀ h₁
    (stoppedRow σ target center) (stoppedRow_measurable σ target center)
    (StoppedScoreLeverage.row_energy_integrable σ target center hages q) F hF B hB mean
  simpa only [he,he₀,he₁,mark] using hh

end SHE.StoppedGaussianSegment
