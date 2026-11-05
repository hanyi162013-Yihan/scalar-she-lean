module

public import SHE.ControlledJointWeightedWord
public import SHE.WeightedMarkedIntegral

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledJointWeightedWord
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution GaussianRangeSmooth
  FiniteCenteredProduct ControlledProfile ControlledFutureMeans StoppedGaussianFeatures StoppedGaussianScore
  ProfilePointwise ProfileParameter ProfileStability StoppedFourier PhysicalMeanRange
open scoped BigOperators NNReal Matrix.Norms.L2Operator
local instance controlledJointMarkedWord_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {X ι : Type*} [MeasurableSpace X] [DecidableEq ι] {n : ℕ}

/-- Actual stopped joint-mean endpoint FTC in its literal three marked
legs: entire centered mean and covariance marks, plus every omitted-leaf
full-profile baseline derivative. Old scores are fixed throughout. -/
theorem actual_joint_marked_transfer (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (σ target : Fin n → ℝ) (center : Fin n → UnitAddCircle)
    (q : ℝ) (hq : 0 ≤ q) (hgap : ∀ i, q < σ i)
    (hTh : ∀ i, σ i ≤ P.horizon) (hages : ∀ i,σ i ≤ target i) (u d Z D : CircleL2)
    (old : ControlledProfile.Domain → ℝ) (hold : Measurable old)
    {ε : ℝ} (hε : ε < P.lower) (holdb : ∀ p, 0 ≤ old p ∧ old p ≤ ε)
    (hsmall : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent - 2) / 4) * P.horizon ^ (P.exponent / 4) ≤ 1 / 2)
    (μ : Measure X) [SFinite μ] (w : X → ℝ) (hw : Integrable w μ) (hwmeas : Measurable w)
    (shift : X → State n) (hs : Measurable shift)
    (s : Finset ι) (leaf : ι → ControlledProfile.Domain)
    (R : State n → ℝ) (a : ι → State n → ℝ)
    (hR : Measurable R) (ha : ∀ i ∈ s, Measurable (a i))
    (B : ℝ) (M : ι → ℝ) (hB : 0 ≤ B) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hRb : ∀ z, |R z| ≤ B) (hab : ∀ i ∈ s, ∀ z, |a i z| ≤ M i) :
    let A := ControlledFixedReserve.covariance P Λ u d old σ target (nativeCenter center) q
    let b := ControlledFiniteWord.baselines P Λ u d leaf
    let db := ControlledFiniteWord.baselineDerivatives P Λ u d leaf
    let E := dampedDirection σ target center q Λ D
    let base := currentDirection target center q Z
    let covMark := ControlledFixedReserve.mark P Λ u d old σ target (nativeCenter center) q
    let W := fun θ => gaussianAverage (A θ)
      (WeightedBorelAverage.average μ w shift (test s R a (fun i => b i θ)))
      (jointMeanVector σ target center q Λ Z D θ)
    let mark := WeightedWordMarking.mark s μ w shift A R a b db covMark base E
    (∀ᵐ θ ∂volume, HasDerivAt W (mark θ) θ) ∧
      ∀ r t, IntervalIntegrable mark volume r t ∧ (∫ θ in r..t, mark θ) = W t - W r := by
  dsimp only
  let A := ControlledFixedReserve.covariance P Λ u d old σ target (nativeCenter center) q
  let b := ControlledFiniteWord.baselines P Λ u d leaf
  let db := ControlledFiniteWord.baselineDerivatives P Λ u d leaf
  let E := dampedDirection σ target center q Λ D
  let base := currentDirection target center q Z
  let covMark := ControlledFixedReserve.mark P Λ u d old σ target (nativeCenter center) q
  have hT : ∀ i, 0 < σ i := fun i => lt_of_le_of_lt hq (hgap i)
  obtain ⟨Q, ⟨K, hK⟩, hc⟩ := ControlledFixedReserve.reserve_and_mark P hΛ u d old hold hε holdb
    σ target (nativeCenter center) hT hTh hages q hq hsmall
  have hE : E ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A 0)).range :=
    jointDirection_mem_range P hΛ u d D old hold hε holdb
      σ target center q hgap hages
  have hb (i : ι) (_hi : i ∈ s) : ∀ᵐ θ ∂volume, HasDerivAt (b i) (db i θ) θ :=
    ControlledFiniteWord.baseline_ae_hasDerivAt P hΛ u d hsmall leaf i
  have hd := WeightedWordMarking.ae_hasDerivAt s μ w hw hwmeas shift hs Q hK R a b db
    hR ha B M hB hM hRb hab hb base E hE covMark hc
  have hf := WeightedWordMarking.integral s μ w hw hwmeas shift hs Q hK R a b db
    hR ha B M (fun _ => P.upper) hB hM (fun _ _ => P.upper_nonneg) hRb hab
    (fun i => ⟨curveBound P.lower P.holder P.exponent P.horizon d (leaf i),
      curveBound_nonneg P.lower_pos.le P.holder_nonneg d (leaf i)⟩)
    (fun i _ => profile_curve_lipschitz P hΛ u d hsmall (leaf i))
    (fun i _ θ => by
      change |profile P Λ u d (θ, leaf i)| ≤ P.upper
      rw [abs_of_nonneg (P.lower_pos.le.trans (profile_bounds P Λ u d (θ, leaf i)).1)]
      exact (profile_bounds P Λ u d (θ, leaf i)).2)
    hb base E hE covMark hc
  have he : WeightedGaussianWord.word s μ w shift A R a b base E = fun θ =>
      gaussianAverage (A θ) (WeightedBorelAverage.average μ w shift (test s R a (fun i => b i θ)))
        (jointMeanVector σ target center q Λ Z D θ) := by
    funext θ
    rfl
  rw [he] at hd
  refine ⟨hd, fun r t => ?_⟩
  have hh := hf r t
  change IntervalIntegrable (WeightedWordMarking.mark s μ w shift A R a b db covMark base E) volume r t ∧ _ at hh
  rw [he] at hh
  exact hh

end SHE.ControlledJointWeightedWord
