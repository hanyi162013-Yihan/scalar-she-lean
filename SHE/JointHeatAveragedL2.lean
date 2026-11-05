module

public import SHE.WeightedHistoryL2Limit
public import SHE.JointHeatLeafLimit
public import SHE.JointRecursiveReferenceLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.JointHeatAveragedL2
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open RecursiveHeatBounds JointWordAnalytic Topology
open scoped NNReal
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
variable {P Ω:Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable {R:ReferenceData} {n:ℕ} (L:Level R P n) (δ:ℝ) (hδ:0<δ)
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›} {τ:Measure Ω} [IsProbabilityMeasure τ]
variable {h:ℝ≥0} (dU dV:PredictableWordState.Data 𝓕 τ h) (Λ:ℝ)

/-- At fixed depth and time cutoff, the literal heat-regularized
recursive leaves converge in sample L2 AFTER their original histories
have been averaged. The same actual physical states are retained. -/
theorem leaf_limit (ν:Measure P) [IsFiniteMeasure ν] (k:ℕ):
    let E:=fun ε:ℝ=>fun ω=>∫p,JointHeatLeafLimit.leaf L δ hδ dU dV Λ ε.toNNReal k p ω-
      JointHeatLeafLimit.leaf L δ hδ dU dV Λ 0 k p ω ∂historyMeasure R ν k
    (∀ε,Integrable (fun ω=>‖E ε ω‖^2) τ) ∧
      Tendsto (fun ε=>∫ω,‖E ε ω‖^2 ∂τ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
  obtain ⟨C,hC,hCb⟩:=(test_uniform L δ hδ k).norm_bound
  have hb(ε:ℝ≥0)(p:History P k)(ω:Ω):
      ‖JointHeatLeafLimit.leaf L δ hδ dU dV Λ ε k p ω‖≤C:=by
    exact hCb (ε,p) _
  have ht:=WeightedHistoryL2Limit.averaged_limit (historyMeasure R ν k) τ
    (fun ε:ℝ=>fun z:History P k×Ω=>JointHeatLeafLimit.leaf L δ hδ dU dV Λ ε.toNNReal k z.1 z.2)
    (fun z=>JointHeatLeafLimit.leaf L δ hδ dU dV Λ 0 k z.1 z.2)
    (fun ε=>JointHeatLeafLimit.leaf_measurable L δ hδ dU dV Λ ε.toNNReal k)
    (JointHeatLeafLimit.leaf_measurable L δ hδ dU dV Λ 0 k)
    (fun _=>1) (integrable_const 1) (fun _=>by norm_num) hC
    (fun ε p ω=>by simpa only [mul_one] using hb ε.toNNReal p ω)
    (fun p ω=>by simpa only [mul_one] using hb 0 p ω)
    (𝓝[>] (0:ℝ)) (by
      simpa only [Real.norm_eq_abs] using
        JointHeatLeafLimit.integrated_leaf_difference_tendsto_zero L δ hδ dU dV Λ ν k)
  exact ht

/-- The corresponding actual Gaussian reference terms converge in the
same sample L2 space; no current-state Gaussianity is used. -/
theorem reference_limit (ν:Measure P) [IsFiniteMeasure ν] (k:ℕ):
    let E:=fun ε:ℝ=>fun ω=>∫p,reference (level L δ hδ ε.toNNReal k) Λ
      dU.physicalState dV.physicalState dU.physicalField dV.physicalField p ω-
      reference (level L δ hδ 0 k) Λ
        dU.physicalState dV.physicalState dU.physicalField dV.physicalField p ω ∂historyMeasure R ν k
    (∀ε,Integrable (fun ω=>‖E ε ω‖^2) τ) ∧
      Tendsto (fun ε=>∫ω,‖E ε ω‖^2 ∂τ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
  obtain ⟨C,hC,hCb⟩:=(test_uniform L δ hδ k).norm_bound
  let F:=fun ε:ℝ≥0=>fun z:History P k×Ω=>reference (level L δ hδ ε k) Λ
    dU.physicalState dV.physicalState dU.physicalField dV.physicalField z.1 z.2
  have hm(ε:ℝ≥0):Measurable (F ε):=reference_measurable _ Λ
    dU.physicalState_measurable dV.physicalState_measurable
    dU.physicalField_measurable dV.physicalField_measurable
  have hb(ε:ℝ≥0)(p:History P k)(ω:Ω):‖F ε (p,ω)‖≤C:=by
    dsimp only [F]
    rw [JointRecursiveReferenceLimit.reference_eq_average]
    exact GaussianSmooth.average_norm_bound _ (hCb (ε,p)) _
  have ht:=WeightedHistoryL2Limit.averaged_limit (historyMeasure R ν k) τ
    (fun ε:ℝ=>F ε.toNNReal) (F 0) (fun ε=>hm ε.toNNReal) (hm 0)
    (fun _=>1) (integrable_const 1) (fun _=>by norm_num) hC
    (fun ε p ω=>by simpa only [mul_one] using hb ε.toNNReal p ω)
    (fun p ω=>by simpa only [mul_one] using hb 0 p ω)
    (𝓝[>] (0:ℝ)) (by
      simpa only [Real.norm_eq_abs,F] using
        JointRecursiveReferenceLimit.integrated_reference_difference_tendsto_zero L δ hδ Λ
          dU.physicalState dV.physicalState dU.physicalField dV.physicalField
          dU.physicalState_measurable dV.physicalState_measurable
          dU.physicalField_measurable dV.physicalField_measurable ν τ k)
  exact ht

end SHE.JointHeatAveragedL2
