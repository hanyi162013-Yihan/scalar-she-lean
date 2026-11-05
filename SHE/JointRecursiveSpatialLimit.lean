module

public import SHE.RecursiveHeatBounds
public import SHE.HeatFieldMovingWeight
public import SHE.JointStateSpatialLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.JointRecursiveSpatialLimit
open Set MeasureTheory AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open CutoffWordAnalytic NativeHeatObservation SmoothWords GaussianTaylor Filter Topology
open DyadicApproximation JointStateSpatialLimit
open scoped NNReal ENNReal
local instance recursiveHeatSpatialLimit_periodPositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance recursiveHeatSpatialLimit_realSigma : MeasurableSpace RealL2 := borel _
local instance recursiveHeatSpatialLimit_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance recursiveHeatSpatialLimit_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance recursiveHeatSpatialLimit_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R P n)
variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {τ : Measure Ω} [IsProbabilityMeasure τ]
variable {h : ℝ≥0} (dU dV : PredictableWordState.Data 𝓕 τ h) (Λ : ℝ)
variable (δ : ℝ) (hδ : 0 < δ)

theorem recursive_weight_bounded (k : ℕ) : ∃ C : ℝ,0 ≤ C ∧ ∀ ε : ℝ≥0,∀ q,
    |JointStateSpatialLimit.weight (RecursiveHeatBounds.level L δ hδ ε k) dU dV Λ δ q| ≤ C := by
  obtain ⟨B,hB,hH⟩ := (RecursiveHeatBounds.averagedTest_uniform L δ hδ k).fderiv.fderiv.norm_bound
  let Q : ℝ := Real.sqrt ((n+k:ℕ):ℝ)*CovarianceMatrix.heatRowBound δ
  have hQ : 0 ≤ Q := mul_nonneg (Real.sqrt_nonneg _) (CovarianceMatrix.heatRowBound_pos hδ).le
  refine ⟨(1/2:ℝ)*B*Q^2,by positivity,fun ε q => ?_⟩
  let Le := RecursiveHeatBounds.level L δ hδ ε k
  let H := GaussianTaylor.hessian (Le.averagedTest (historyPoint q)) (oldState Le dU dV Λ q.1)
  let r := Le.cutoffRow δ (historyPoint q)
  have hr : ‖r‖ ≤ Q := Le.cutoffRow_bound hδ _
  have hHb : ‖H‖ ≤ B := hH (ε,historyPoint q) (oldState Le dU dV Λ q.1)
  have hb : ‖H r r‖ ≤ B*Q^2 := by
    have hh := (GaussianTaylor.bilinear_norm_le H r r).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hHb (norm_nonneg r)) (norm_nonneg r))
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg r) hr 2) hB
    exact hh.trans (by nlinarith only [hs])
  change |(1/2:ℝ)*H r r| ≤ _
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  exact (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 1/2)).trans_eq (by ring)

theorem nodeState_eq (ε η : ℝ≥0) (k : ℕ) :
    JointStateSpatialLimit.nodeState (RecursiveHeatBounds.level L δ hδ ε k) dV=
      JointStateSpatialLimit.nodeState (RecursiveHeatBounds.level L δ hδ η k) dV := by
  funext q
  change dV.state ((ClippedCovariance.clip R.base
    ((RecursiveHeatBounds.level L δ hδ ε k).terminal q.1.1) q.2).toNNReal,q.1.2)=_
  rw [RecursiveHeatBounds.terminal_eq L δ hδ ε η k q.1.1]
  rfl

/-- The additional spatial correction vanishes along the actual moving
recursive levels Lε, for each fixed finite depth and fixed δ. Its Hessian
weight is allowed to vary with ε; its uniform bound is proved recursively.
This is stronger than a limit with a fixed history level. -/
theorem integrated_recursive_child_difference_tendsto_zero
    (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    Tendsto (fun ε : ℝ => ∫ q : (History P k × Ω) × ℝ,
      ∫ x : HeatCircle,|JointCutoffStep.heatChildLeaf (RecursiveHeatBounds.level L δ hδ ε.toNNReal k) Λ δ dU.physicalState dV.physicalState dU.physicalField dV.physicalField ε (q.1.1,(q.2,x)) q.1.2-
      JointCutoffStep.childLeaf (RecursiveHeatBounds.level L δ hδ ε.toNNReal k) Λ δ dU.physicalState dV.physicalState dU.physicalField dV.physicalField (q.1.1,(q.2,x)) q.1.2| ∂haarAddCircle
      ∂((historyMeasure R μ k).prod τ).prod (volume.restrict (Ioc R.base R.horizon)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,hC,hCb⟩ := recursive_weight_bounded L dU dV Λ δ hδ k
  obtain ⟨M,hM⟩ := R.totalVariance_smooth.norm_bound
  obtain ⟨B,hB⟩ := R.totalVariance_smooth.fderiv.norm_bound
  have hBn : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hLip (z w : ℝ) : |R.totalVariance z-R.totalVariance w| ≤ B*|z-w| := by
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => R.totalVariance_smooth.smooth.differentiable (by simp) y)
      (fun y _ => hB y) convex_univ (mem_univ w) (mem_univ z)
  let L₀ := RecursiveHeatBounds.level L δ hδ 0 k
  have ht := HeatFieldMovingWeight.integrated_mass_tendsto_zero
    (nodeState L₀ dV) (nodeState_measurable L₀ dV) R.totalVariance
    R.totalVariance_smooth.smooth.continuous.measurable
    (fun ε => weight (RecursiveHeatBounds.level L δ hδ ε.toNNReal k) dU dV Λ δ)
    (fun ε => weight_measurable _ dU dV Λ δ)
    (((historyMeasure R μ k).prod τ).prod (volume.restrict (Ioc R.base R.horizon)))
    (fun z => by simpa only [Real.norm_eq_abs] using hM z) hC (fun ε => hCb ε.toNNReal) hBn hLip
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply integral_congr_ae
  filter_upwards with q
  rw [child_difference_mass _ dU dV Λ δ ε hε,nodeState_eq L dV δ hδ ε.toNNReal 0 k]

end SHE.JointRecursiveSpatialLimit
