module

public import SHE.FiniteWordMarking

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledReservedWord
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution GaussianRangeSmooth
  FiniteCenteredProduct ControlledProfile ControlledFutureMeans StoppedGaussianFeatures StoppedGaussianScore
  ProfilePointwise ProfileParameter ProfileStability StoppedFourier PhysicalMeanRange
open scoped BigOperators NNReal Matrix.Norms.L2Operator
local instance controlledReservedWord_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {ι : Type*} [DecidableEq ι] {n : ℕ}

/-- Exact arbitrary-order controlled word differentiation after a fixed
positive Gaussian split. `offset` is the unchanged old Gaussian increment;
its old scores are parameters, never differentiated. Every leaf retains the
actual full consistent-profile baseline. -/
theorem actual_future_word_transfer (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (target : Fin n → ℝ) (center : Fin n → UnitAddCircle)
    (q : ℝ) (hq : 0 ≤ q) (hgap : ∀ i, q < target i)
    (hTh : ∀ i, target i ≤ P.horizon) (u d Z D : CircleL2)
    (old : ControlledProfile.Domain → ℝ) (hold : Measurable old)
    {ε : ℝ} (hε : ε < P.lower) (holdb : ∀ p, 0 ≤ old p ∧ old p ≤ ε)
    (hsmall : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    (s : Finset ι) (leaf : ι → ControlledProfile.Domain)
    (R : State n → ℝ) (a : ι → State n → ℝ)
    (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i))
    (B : ℝ) (M : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hRb : ∀ z, |R z| ≤ B) (hab : ∀ i ∈ s, ∀ z, |a i z| ≤ M i)
    (offset : State n) :
    let A := ControlledFixedReserve.covariance P Λ u d old target target (nativeCenter center) q
    let b := ControlledFiniteWord.baselines P Λ u d leaf
    let db := ControlledFiniteWord.baselineDerivatives P Λ u d leaf
    let E := futureDirection Λ target center q hq d D
    let m := fun θ => futureMeanVector Λ target center q hq u d Z D θ + offset
    let F := fun θ => test s R a (fun i => b i θ)
    let W := fun θ => gaussianAverage (A θ) (F θ) (m θ)
    let mark := fun θ => ControlledFixedReserve.mark P Λ u d old target target (nativeCenter center) q (F θ) θ (m θ) +
      (∫ y, F θ (m θ + y) * MeasurableGaussianScores.firstScore (A θ) E y
        ∂multivariateGaussian 0 (A θ)) -
      ∑ i ∈ s, db i θ * gaussianAverage (A θ) (test (s.erase i) R a (fun j => b j θ)) (m θ)
    (∀ᵐ θ ∂volume, HasDerivAt W (mark θ) θ) ∧
      ∀ r t, IntervalIntegrable mark volume r t ∧ (∫ θ in r..t, mark θ) = W t - W r := by
  dsimp only
  let A := ControlledFixedReserve.covariance P Λ u d old target target (nativeCenter center) q
  let b := ControlledFiniteWord.baselines P Λ u d leaf
  let db := ControlledFiniteWord.baselineDerivatives P Λ u d leaf
  let E := futureDirection Λ target center q hq d D
  let base := currentDirection target center q Z + offset
  let covMark := ControlledFixedReserve.mark P Λ u d old target target (nativeCenter center) q
  have hT : ∀ i, 0 < target i := fun i => lt_of_le_of_lt hq (hgap i)
  obtain ⟨Q, ⟨K, hK⟩, hc⟩ := ControlledFixedReserve.reserve_and_mark P hΛ u d old hold hε holdb
    target target (nativeCenter center) hT hTh (fun _ => le_rfl) q hq hsmall
  have hE : E ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A 0)).range :=
    ControlledFixedReserve.actual_future_direction_mem_range P hΛ u d D old hold hε holdb
      target center q hq hgap
  have hb (i : ι) (hi : i ∈ s) : ∀ᵐ θ ∂volume, HasDerivAt (b i) (db i θ) θ :=
    ControlledFiniteWord.baseline_ae_hasDerivAt P hΛ u d hsmall leaf i
  have hder := FiniteWordMarking.ae_hasDerivAt s Q hK R a b db hR ha B M hB hM hRb hab hb base E hE covMark hc
  have hftc := FiniteWordMarking.integral s Q hK R a b db hR ha B M (fun _ => P.upper)
    hB hM (fun _ _ => P.upper_nonneg) hRb hab
    (fun i => ⟨curveBound P.lower P.holder P.exponent P.horizon d (leaf i),
      curveBound_nonneg P.lower_pos.le P.holder_nonneg d (leaf i)⟩)
    (fun i _ => profile_curve_lipschitz P hΛ u d hsmall (leaf i))
    (fun i _ θ => by
      change |profile P Λ u d (θ, leaf i)| ≤ P.upper
      rw [abs_of_nonneg (P.lower_pos.le.trans (profile_bounds P Λ u d (θ, leaf i)).1)]
      exact (profile_bounds P Λ u d (θ, leaf i)).2)
    hb base E hE covMark hc
  have hmean (θ : ℝ) : base + θ • E = futureMeanVector Λ target center q hq u d Z D θ + offset := by
    rw [futureMeanVector_affine Λ target center q hq hgap u d Z D θ]
    dsimp only [base, E]
    ac_rfl
  have hword : FiniteGaussianWord.word s A R a b base E = fun θ =>
      gaussianAverage (A θ) (test s R a (fun i => b i θ))
        (futureMeanVector Λ target center q hq u d Z D θ + offset) := by
    funext θ
    exact congrArg (gaussianAverage (A θ) (test s R a (fun i => b i θ))) (hmean θ)
  have hmark : FiniteWordMarking.mark s A R a b db covMark base E = fun θ =>
      covMark (test s R a (fun i => b i θ)) θ
        (futureMeanVector Λ target center q hq u d Z D θ + offset) +
      (∫ y, test s R a (fun i => b i θ)
        (futureMeanVector Λ target center q hq u d Z D θ + offset + y) *
        MeasurableGaussianScores.firstScore (A θ) E y ∂multivariateGaussian 0 (A θ)) -
      ∑ i ∈ s, db i θ * gaussianAverage (A θ) (test (s.erase i) R a (fun j => b j θ))
        (futureMeanVector Λ target center q hq u d Z D θ + offset) := by
    funext θ
    dsimp only [FiniteWordMarking.mark, FiniteGaussianWord.baselineMark]
    rw [hmean θ]
  rw [hword] at hder
  rw [hmark] at hder
  constructor
  · simpa only [FiniteWordMarking.mark, FiniteGaussianWord.baselineMark, hmean,
      A, b, db, covMark, E] using hder
  · intro r t
    have hf := hftc r t
    rw [hmark] at hf
    simpa only [FiniteWordMarking.mark, FiniteGaussianWord.word, FiniteGaussianWord.baselineMark,
      hmean, A, b, db, covMark, E] using hf

/-- The old/residual split is the exact convolution of the actual singular
Gaussian observation laws at every interpolation parameter. -/
theorem gaussian_split (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (old : ControlledProfile.Domain → ℝ) (hold : Measurable old)
    {ε : ℝ} (hε : ε < P.lower) (holdb : ∀ p, 0 ≤ old p ∧ old p ≤ ε)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q θ : ℝ) :
    (multivariateGaussian (0 : State n) (stoppedCovariance σ target center old q)) ∗
      multivariateGaussian 0 (ControlledFixedReserve.covariance P Λ u d old σ target center q θ) =
      multivariateGaussian 0 (stoppedCovariance σ target center (fun p => profile P Λ u d (θ, p)) q) := by
  have hc : Measurable (ControlledFixedReserve.coefficient P Λ u d old θ) :=
    ((profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)).sub hold
  have hh := StoppedCovarianceSplit.gaussian_positive_split σ target center hages q hold hc holdb
    (fun p => ⟨(sub_pos.mpr hε).le.trans (ControlledFixedReserve.coefficient_bounds P Λ u d old holdb θ p).1,
      (ControlledFixedReserve.coefficient_bounds P Λ u d old holdb θ p).2⟩)
  have heq : (fun p => old p + ControlledFixedReserve.coefficient P Λ u d old θ p) =
      fun p => profile P Λ u d (θ, p) := by
    funext p
    dsimp only [ControlledFixedReserve.coefficient]
    ring
  simpa only [ControlledFixedReserve.covariance, heq] using hh

end SHE.ControlledReservedWord
