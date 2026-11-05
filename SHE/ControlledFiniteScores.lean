module

public import SHE.FiniteWordScores
public import SHE.StoppedCovarianceSplit

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledFiniteScores
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution GaussianRangeSmooth
  FiniteCenteredProduct ControlledProfile ControlledFutureMeans StoppedGaussianFeatures StoppedGaussianScore
  ProfilePointwise ProfileParameter ProfileStability StoppedFourier PhysicalMeanRange GaussianProfileMark
open scoped BigOperators NNReal Matrix.Norms.L2Operator
local instance controlledFiniteScores_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {ι : Type*} [DecidableEq ι] {n : ℕ}

theorem covarianceMark_expansion (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i, 0 < σ i) (hσh : ∀ i, σ i ≤ P.horizon) (hages : ∀ i, σ i ≤ target i)
    (q : ℝ) (hq : 0 ≤ q) (u d : CircleL2)
    (hsmall : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    (s : Finset ι) (R : State n → ℝ) (a : ι → State n → ℝ) (b : ι → ℝ)
    (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i))
    (B : ℝ) (M : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hRb : ∀ z, |R z| ≤ B) (hab : ∀ i ∈ s, ∀ z, |a i z| ≤ M i) (θ : ℝ) (m : State n) :
    stoppedBorelCovarianceMark P Λ σ target center u d q (test s R a b) θ m =
      ∑ t ∈ s.powerset, coefficient s t b *
        stoppedBorelCovarianceMark P Λ σ target center u d q (monomial R a t) θ m := by
  let c : ControlledProfile.Domain → ℝ := fun p => profile P Λ u d (θ, p)
  let e : ControlledProfile.Domain → ℝ := fun p => derivative P Λ u d (p, θ)
  let row := stoppedRow σ target center
  let μ := historyMeasure q
  have hc : Measurable c := (profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have he : Measurable e := (derivative_measurable P hΛ u d hsmall).comp
    (measurable_id.prodMk measurable_const)
  have hrow : Measurable row := stoppedRow_measurable σ target center
  have hσ1 : ∀ i, σ i ≤ 1 := fun i => (hσh i).trans P.horizon_le_one
  have henergy : Integrable (fun p => ‖row p‖ ^ 2) μ := by
    have hh := StoppedProfileMark.bounded_profile_frame_integrable σ target center hσ hσ1 hages hq
      (c := fun _ => 1) measurable_const (M := 1) (fun _ => by norm_num)
    simpa only [abs_one, one_mul] using hh
  have hcb (p : ControlledProfile.Domain) : |c p| ≤ P.upper := by
    rw [abs_of_nonneg (P.lower_pos.le.trans (profile_bounds P Λ u d (θ, p)).1)]
    exact (profile_bounds P Λ u d (θ, p)).2
  have hci : Integrable (fun p => |c p| * ‖row p‖ ^ 2) μ :=
    StoppedProfileMark.bounded_profile_frame_integrable σ target center hσ hσ1 hages hq hc hcb
  have hcl : ∀ᵐ p ∂μ, P.lower ≤ c p := ae_of_all _ (fun p => (profile_bounds P Λ u d (θ, p)).1)
  have hrange := GaussianWordCovarianceIntegral.ae_frame_mem_profile_range μ row
    hrow.aestronglyMeasurable henergy c hc.aestronglyMeasurable hci P.lower_pos hcl
  have heq : profileCovariance μ c row = stoppedCovariance σ target center c q :=
    StoppedProfileMark.profileCovariance_eq_stopped σ target center hσ hσ1 hages hq hc hcb
  rw [heq] at hrange
  have hA : (stoppedCovariance σ target center c q).PosSemidef :=
    StoppedCovarianceSplit.covariance_posSemidef σ target center hages q hc
      (fun p => ⟨P.lower_pos.le.trans (profile_bounds P Λ u d (θ, p)).1, (profile_bounds P Λ u d (θ, p)).2⟩)
  have hei : Integrable (fun p => |e p| * ‖row p‖ ^ 2) μ := by
    apply (P.stopped_dominator_frame_integrable σ target center hσ hσh hages d hq).mono'
      (by convert! (he.norm.mul (hrow.norm.pow_const 2)).aestronglyMeasurable using 1)
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (derivative_bound P hΛ u d hsmall p θ) (sq_nonneg _)
  exact FiniteWordScores.covarianceMark_expansion μ hA e he row hrow hrange hei s R a b hR ha B M hB hM hRb hab m

/-- Literal full-product mean/covariance marking. The finite expansion has
been recombined into one first-score integral and one continuum second-score
integral, with all explicit baseline derivatives retained. -/
theorem actual_future_word_full_mark (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (target : Fin n → ℝ) (center : Fin n → UnitAddCircle)
    (q : ℝ) (hq : 0 ≤ q) (hgap : ∀ i, q < target i)
    (hTh : ∀ i, target i ≤ P.horizon) (u d Z D : CircleL2)
    (hsmall : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    (s : Finset ι) (leaf : ι → ControlledProfile.Domain)
    (R : State n → ℝ) (a : ι → State n → ℝ)
    (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i))
    (B : ℝ) (M : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hRb : ∀ z, |R z| ≤ B) (hab : ∀ i ∈ s, ∀ z, |a i z| ≤ M i) :
    let A := fun θ => stoppedCovariance target target (nativeCenter center)
      (fun p => profile P Λ u d (θ, p)) q
    let b := ControlledFiniteWord.baselines P Λ u d leaf
    let db := ControlledFiniteWord.baselineDerivatives P Λ u d leaf
    let E := futureDirection Λ target center q hq d D
    let m := futureMeanVector Λ target center q hq u d Z D
    let F := fun θ => test s R a (fun i => b i θ)
    let W := fun θ => gaussianAverage (A θ) (F θ) (m θ)
    let mark := fun θ => stoppedBorelCovarianceMark P Λ target target (nativeCenter center) u d q (F θ) θ (m θ) +
      (∫ y, F θ (m θ + y) * MeasurableGaussianScores.firstScore (A θ) E y
        ∂multivariateGaussian 0 (A θ)) -
      ∑ i ∈ s, db i θ * gaussianAverage (A θ) (test (s.erase i) R a (fun j => b j θ)) (m θ)
    (∀ᵐ θ ∂volume, HasDerivAt W (mark θ) θ) ∧
      ∀ r t, IntervalIntegrable mark volume r t ∧ (∫ θ in r..t, mark θ) = W t - W r := by
  have hh := ControlledFiniteWord.actual_future_word_transfer P hΛ target center q hq hgap hTh
    u d Z D hsmall s leaf R a hR ha B M hB hM hRb hab
  dsimp only at hh ⊢
  have hT : ∀ i, 0 < target i := fun i => lt_of_le_of_lt hq (hgap i)
  have heq (θ : ℝ) :
      (∑ t ∈ s.powerset, coefficient s t (fun i => ControlledFiniteWord.baselines P Λ u d leaf i θ) *
        (stoppedBorelCovarianceMark P Λ target target (nativeCenter center) u d q (monomial R a t) θ
          (futureMeanVector Λ target center q hq u d Z D θ) +
          (∫ y, monomial R a t (futureMeanVector Λ target center q hq u d Z D θ + y) *
            MeasurableGaussianScores.firstScore
              (stoppedCovariance target target (nativeCenter center) (fun p => profile P Λ u d (θ, p)) q)
              (futureDirection Λ target center q hq d D) y
            ∂multivariateGaussian 0
              (stoppedCovariance target target (nativeCenter center) (fun p => profile P Λ u d (θ, p)) q)))) =
      stoppedBorelCovarianceMark P Λ target target (nativeCenter center) u d q
        (test s R a (fun i => ControlledFiniteWord.baselines P Λ u d leaf i θ)) θ
        (futureMeanVector Λ target center q hq u d Z D θ) +
      (∫ y, test s R a (fun i => ControlledFiniteWord.baselines P Λ u d leaf i θ)
          (futureMeanVector Λ target center q hq u d Z D θ + y) *
        MeasurableGaussianScores.firstScore
          (stoppedCovariance target target (nativeCenter center) (fun p => profile P Λ u d (θ, p)) q)
          (futureDirection Λ target center q hq d D) y
        ∂multivariateGaussian 0
          (stoppedCovariance target target (nativeCenter center) (fun p => profile P Λ u d (θ, p)) q)) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [← covarianceMark_expansion P hΛ target target (nativeCenter center) hT hTh (fun _ => le_rfl)
      q hq u d hsmall s R a _ hR ha B M hB hM hRb hab θ,
      ← FiniteWordScores.meanMark_expansion s _ R a _ hR ha B M hB hM hRb hab]
  simpa only [heq] using hh

end SHE.ControlledFiniteScores
