module

public import SHE.JointHeatAveragedL2
public import SHE.JointRecursiveRemainderConvergence
public import SHE.JointRecursiveReferenceLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.JointHeatAveragedRemainder
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


/-- The actual local recursive remainder has a strong zero-heat limit
at fixed delta and finite depth, after original-history averaging. -/
theorem remainder_limit (ν:Measure P) [IsFiniteMeasure ν] (k:ℕ):
    let E:=fun ε:ℝ=>fun ω=>∫p,JointWordAnalytic.remainder (level L δ hδ ε.toNNReal k) Λ
      dU.physicalState dV.physicalState dU.physicalField dV.physicalField p ω-
      JointWordAnalytic.remainder (level L δ hδ 0 k) Λ
      dU.physicalState dV.physicalState dU.physicalField dV.physicalField p ω ∂historyMeasure R ν k
    (∀ε,Integrable (fun ω=>‖E ε ω‖^2) τ) ∧
      Tendsto (fun ε=>∫ω,‖E ε ω‖^2 ∂τ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
  let F:=fun ε:ℝ≥0=>fun z:History P k×Ω=>JointWordAnalytic.remainder (level L δ hδ ε k) Λ
    dU.physicalState dV.physicalState dU.physicalField dV.physicalField z.1 z.2
  obtain ⟨C,hC,hCb⟩:=JointRecursiveRemainderConvergence.uniform_remainder_bound L δ hδ Λ
    dU.physicalState dV.physicalState dU.physicalField dV.physicalField k
  have hm(ε:ℝ≥0):Measurable (F ε):=JointWordAnalytic.remainder_measurable _ Λ
    dU.physicalState_measurable dV.physicalState_measurable dU.physicalField_measurable dV.physicalField_measurable
  exact WeightedHistoryL2Limit.averaged_limit (historyMeasure R ν k) τ
    (fun ε:ℝ=>F ε.toNNReal) (F 0) (fun ε=>hm ε.toNNReal) (hm 0)
    (fun _=>1) (integrable_const 1) (fun _=>by norm_num) hC
    (fun ε p ω=>by simpa only [mul_one,F,JointRecursiveRemainderConvergence.remainder] using hCb ε.toNNReal p ω)
    (fun p ω=>by simpa only [mul_one,F,JointRecursiveRemainderConvergence.remainder] using hCb 0 p ω)
    (𝓝[>] (0:ℝ)) (by
      simpa only [Real.norm_eq_abs,F,JointRecursiveRemainderConvergence.remainder] using
        JointRecursiveRemainderConvergence.integrated_remainder_difference_tendsto_zero L δ hδ Λ
          dU.physicalState dV.physicalState dU.physicalField dV.physicalField
          dU.physicalState_measurable dV.physicalState_measurable
          dU.physicalField_measurable dV.physicalField_measurable ν τ k)

end SHE.JointHeatAveragedRemainder
