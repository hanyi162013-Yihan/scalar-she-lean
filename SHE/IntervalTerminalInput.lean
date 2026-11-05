module

public import SHE.IntervalMeanScore
public import SHE.GaussianScoreKernel

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.IntervalMeanScore
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  OldIntervalCovariance GaussianIncrement GaussianGramScore MeasurableGaussianScores
  HeatTorusKernel HeatProjection StoppedMeanRange StoppedGaussianScore
  RealHeatCovarianceMean PhysicalMeanRange GaussianScoreKernel
open scoped BigOperators InnerProductSpace
local instance intervalTerminalInput_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
variable {n : ℕ}

theorem covarianceField_posSemidef (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (hages : ∀ i, σ i ≤ target i) {c : UnitAddCircle × Domain → ℝ}
    (hc : Measurable c) {M : ℝ} (hb : ∀ x p, 0 ≤ c (x,p) ∧ c (x,p) ≤ M)
    (lo hi : ℝ) (x : UnitAddCircle) : (covarianceField σ target a c lo hi x).PosSemidef := by
  have hg : Matrix.gram ℝ (IntervalScoreMass.feature σ target (nativeCenter (fun i => a i+x)) hages
      (fun p => c (x,p)) (hc.comp (measurable_const.prodMk measurable_id)) M (hb x) lo hi)=
      covarianceField σ target a c lo hi x :=
    IntervalScoreMass.feature_gram σ target (nativeCenter (fun i => a i+x)) hages
      (fun p => c (x,p)) (hc.comp (measurable_const.prodMk measurable_id)) M (hb x) lo hi
  rw [← hg]
  exact Matrix.posSemidef_gram ℝ _

/-- The terminal direction is the actual native physical heat mean, hence
the signed row integral proved in `currentDirection_integral`. Its
canonical score keeps the genuine heat projection of the original input. -/
theorem native_direction_projection_bound
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    {lo hi ell M : ℝ} (hlo : 0 ≤ lo) (hgap : lo < hi)
    (hstop : ∀ i, hi ≤ σ i) (hages : ∀ i, σ i ≤ target i)
    (t : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hage : ∀ i, target i-lo=4*π^2*t i)
    (c : Domain → ℝ) (hc : Measurable c) (hell : 0 < ell)
    (hb : ∀ p, ell ≤ c p ∧ c p ≤ M) (v : StoppedFourier.CircleL2) :
    currentDirection target a lo v ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ)
      (StoppedGaussianFeatures.stoppedCovariance σ target (nativeCenter a) (intervalProfile c lo hi) 0)).range ∧
    scoreVariance
      (StoppedGaussianFeatures.stoppedCovariance σ target (nativeCenter a) (intervalProfile c lo hi) 0)
      (currentDirection target a lo v) ≤
        (ell*(hi-lo))⁻¹ * ‖(heatSpan t a).starProjection (CircleNormalization.push.symm v)‖^2 := by
  rw [currentDirection_eq σ target a lo t ht hage (fun i => hgap.trans_le (hstop i))]
  exact direction_projection_bound σ target a hlo hgap hstop hages t hage c hc hell hb _

theorem input_negative_energy (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (v : StoppedFourier.CircleL2) :
    NegativeNash.energy Λ ρ (CircleNormalization.push.symm v)=
      ‖OneInputOperator.besselHalf Λ ρ hΛ hρ v‖^2 := by
  rw [NegativeNash.energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ),
    ← CircleNormalization.push_bessel_energy hΛ hρ,LinearIsometryEquiv.apply_symm_apply]

/-- Actual varying-covariance last-interval score energy, with a separate
signed heat factor at every original target age. The exact native clock
is `target-lo=4π²t`; `CircleNormalization.push_heat` identifies every
displayed pullback heat with the native heat at age `4π²θt`. -/
theorem native_terminal_energy_age_sum (n : ℕ) :
    ∃ h C θ : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < C ∧ 0 < θ ∧
      ∀ (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
      {lo hi ell M : ℝ} (hlo : 0 ≤ lo) (hgap : lo < hi)
      (hstop : ∀ i, hi ≤ σ i) (hages : ∀ i, σ i ≤ target i)
      (t : Fin n → ℝ) (ht : ∀ i, 0 < t i), (∀ i, t i ≤ h) →
      ∀ (hage : ∀ i, target i-lo=4*π^2*t i)
      (c : UnitAddCircle × Domain → ℝ), Measurable c → 0 < ell →
      (∀ x p, ell ≤ c (x,p) ∧ c (x,p) ≤ M) → ∀ v : StoppedFourier.CircleL2,
      Integrable (fun x => scoreVariance (covarianceField σ target a c lo hi x)
        (currentDirection target (fun i => a i+x) lo v)) haarAddCircle ∧
      (∫ x, scoreVariance (covarianceField σ target a c lo hi x)
        (currentDirection target (fun i => a i+x) lo v) ∂haarAddCircle) ≤
        (C/(ell*(hi-lo))) * ∑ i, sqrt (t i)*
          ‖CircleHeat.heat (θ*t i) (CircleNormalization.push.symm v)‖^2 := by
  obtain ⟨h,C,θ,hh,hh1,hC,hθ,he⟩ := terminal_energy_age_sum n
  refine ⟨h,C,θ,hh,hh1,hC,hθ,?_⟩
  intro σ target a lo hi ell M hlo hgap hstop hages t ht hth hage c hc hell hb v
  have h := he σ target a hlo hgap hstop hages t ht hth hage c hc hell hb (CircleNormalization.push.symm v)
  have hd (x : UnitAddCircle) : meanDirection
      (currentSynthesis σ target (fun i => a i+x) lo t hage
        (fun i => hgap.trans_le (hstop i))) (CircleNormalization.push.symm v)=
      currentDirection target (fun i => a i+x) lo v :=
    (currentDirection_eq σ target (fun i => a i+x) lo t ht hage _ v).symm
  simpa only [hd] using h

/-- Genuine massive negative-input control for the terminal signed heat
row integral. No absolute value is taken on the input before smoothing,
and no estimate on an unspecified score field is assumed. -/
theorem native_terminal_negative_input (n : ℕ) :
    ∃ h C θ : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < C ∧ 0 < θ ∧
      ∀ (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
      {lo hi ell M : ℝ} (hlo : 0 ≤ lo) (hgap : lo < hi)
      (hstop : ∀ i, hi ≤ σ i) (hages : ∀ i, σ i ≤ target i)
      (t : Fin n → ℝ) (ht : ∀ i, 0 < t i), (∀ i, t i ≤ h) →
      ∀ (hage : ∀ i, target i-lo=4*π^2*t i)
      (c : UnitAddCircle × Domain → ℝ), Measurable c → 0 < ell →
      (∀ x p, ell ≤ c (x,p) ∧ c (x,p) ≤ M) →
      ∀ {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ), ρ ≤ 1 → ∀ v : StoppedFourier.CircleL2,
      (∫ x, scoreVariance (covarianceField σ target a c lo hi x)
        (currentDirection target (fun i => a i+x) lo v) ∂haarAddCircle) ≤
        (C/(ell*(hi-lo))) *
          (∑ i, sqrt (t i)*(Λ^ρ+(θ*t i)^(-ρ))) *
            ‖OneInputOperator.besselHalf Λ ρ hΛ hρ v‖^2 := by
  obtain ⟨h,C,θ,hh,hh1,hC,hθ,he⟩ := terminal_energy_age_sum n
  refine ⟨h,C,θ,hh,hh1,hC,hθ,?_⟩
  intro σ target a lo hi ell M hlo hgap hstop hages t ht hth hage c hc hell hb Λ ρ hΛ hρ hρ1 v
  have h := (he σ target a hlo hgap hstop hages t ht hth hage c hc hell hb (CircleNormalization.push.symm v)).2
  have hd (x : UnitAddCircle) : meanDirection
      (currentSynthesis σ target (fun i => a i+x) lo t hage
        (fun i => hgap.trans_le (hstop i))) (CircleNormalization.push.symm v)=
      currentDirection target (fun i => a i+x) lo v :=
    (currentDirection_eq σ target (fun i => a i+x) lo t ht hage _ v).symm
  simp only [hd] at h
  have hs : (∑ i, sqrt (t i)*‖CircleHeat.heat (θ*t i) (CircleNormalization.push.symm v)‖^2) ≤
      (∑ i, sqrt (t i)*(Λ^ρ+(θ*t i)^(-ρ))) *
        ‖OneInputOperator.besselHalf Λ ρ hΛ hρ v‖^2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hb := NegativeL2Heat.heat_norm_sq_negative hΛ hρ hρ1 (mul_pos hθ (ht i)) (CircleNormalization.push.symm v)
    rw [input_negative_energy Λ ρ hΛ hρ v] at hb
    exact (mul_le_mul_of_nonneg_left hb (sqrt_nonneg _)).trans_eq (by ring)
  exact h.trans (mul_le_mul_of_nonneg_left hs (by positivity)) |>.trans_eq (by ring)

end SHE.IntervalMeanScore
