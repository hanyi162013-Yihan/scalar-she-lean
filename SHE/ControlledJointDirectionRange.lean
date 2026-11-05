module

public import SHE.ControlledJointWeightedWord

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace SHE.ControlledJointWeightedWord
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution GaussianRangeSmooth
  FiniteCenteredProduct ControlledProfile ControlledFutureMeans StoppedGaussianFeatures StoppedGaussianScore
  ProfilePointwise ProfileParameter ProfileStability StoppedFourier PhysicalMeanRange
open scoped BigOperators NNReal Matrix.Norms.L2Operator
local instance controlledJointDirectionRange_periodPos : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {n : ℕ}
/-- The actual original-stop damped direction belongs to the full
remaining covariance range at EVERY interpolation value, including
singular/colliding observation configurations. -/
theorem jointDirection_mem_range_at (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (u d D : CircleL2)
    (old : ControlledProfile.Domain → ℝ) (hold : Measurable old)
    {ε : ℝ} (hε : ε < P.lower) (hb : ∀ p,0 ≤ old p ∧ old p ≤ ε)
    (σ target : Fin n → ℝ) (center : Fin n → UnitAddCircle) (q : ℝ)
    (hgap : ∀ i,q < σ i) (hages : ∀ i,σ i ≤ target i) (θ : ℝ) :
    dampedDirection σ target center q Λ D ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ)
      (ControlledFixedReserve.covariance P Λ u d old σ target (nativeCenter center) q θ)).range := by
  obtain ⟨δ,hδ,hs⟩ := exists_positive_gap (fun i => σ i-q) (fun i => sub_pos.mpr (hgap i))
  apply dampedDirection_mem_range σ target center q Λ hΛ hages δ hδ (fun i => by linarith [hs i])
    (ControlledFixedReserve.coefficient P Λ u d old θ)
    (((profile_measurable P Λ u d).comp ((measurable_const (a:=θ)).prodMk measurable_id)).sub hold)
    P.upper (P.lower-ε)
  · intro p
    exact ⟨(sub_pos.mpr hε).le.trans (ControlledFixedReserve.coefficient_bounds P Λ u d old hb θ p).1,
      (ControlledFixedReserve.coefficient_bounds P Λ u d old hb θ p).2⟩
  · exact sub_pos.mpr hε
  · intro p
    exact (ControlledFixedReserve.coefficient_bounds P Λ u d old hb θ p).1


end SHE.ControlledJointWeightedWord
