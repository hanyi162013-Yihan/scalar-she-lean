module
public import SHE.ActualRootRemainder
public import SHE.WeightedHistoryL2Limit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.ActualRootRemainderL2
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories Topology
open scoped NNReal
local instance actualRootRemainderL2_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance actualRootRemainderL2_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {P Ω:Type}[MeasurableSpace P][MeasurableSpace Ω]
variable {R:ReferenceData}{n:ℕ}(L:Level R P n)(δ:ℝ)(hδ:0<δ)
variable (a:ℝ→ℝ)(ha:Measurable a){A:ℝ}(hAn:0≤A)(hA:∀z,|a z|≤A)
variable (U:Ω×ℝ→CircleL2)(X:Ω×(ℝ×HeatCircle)→ℝ)(hU:Measurable U)(hX:Measurable X)
variable (ν:Measure P)[IsFiniteMeasure ν](μ:Measure Ω)[IsProbabilityMeasure μ]

include ha hAn hA hU hX in
/-- The actual rough-bracket root heat limit is strong in sample L2
after original-history averaging, retaining the fixed smooth word and
time cutoff. This is the topology needed for original Ito closure. -/
theorem averaged_limit (k:ℕ):
    let E:=fun ε:ℝ=>fun ω=>∫p,ActualRootRemainder.remainder L δ hδ a U X ε.toNNReal k p ω-
      ActualRootRemainder.remainder L δ hδ a U X 0 k p ω ∂historyMeasure R ν k
    (∀ε,Integrable (fun ω=>‖E ε ω‖^2) μ) ∧
      Tendsto (fun ε=>∫ω,‖E ε ω‖^2 ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
  obtain ⟨C,hC,hCb⟩:=ActualRootRemainder.uniform_remainder_bound L δ hδ a hAn hA U X k
  have hm(ε:ℝ≥0):Measurable (fun z:History P k×Ω=>ActualRootRemainder.remainder L δ hδ a U X ε k z.1 z.2):=
    ActualVarianceLevel.remainder_measurable (RootHeatBounds.level L δ hδ ε k) a ha
      U hU X hX (fun _ _ _=>0)
  exact WeightedHistoryL2Limit.averaged_limit (historyMeasure R ν k) μ
    (fun ε:ℝ=>fun z=>ActualRootRemainder.remainder L δ hδ a U X ε.toNNReal k z.1 z.2)
    (fun z=>ActualRootRemainder.remainder L δ hδ a U X 0 k z.1 z.2)
    (fun ε=>hm ε.toNNReal) (hm 0) (fun _=>1) (integrable_const _) (fun _=>zero_le_one) hC
    (fun ε p ω=>by simpa only [mul_one] using hCb ε.toNNReal p ω)
    (fun p ω=>by simpa only [mul_one] using hCb 0 p ω)
    (𝓝[>] (0:ℝ))
    (by simpa only [Real.norm_eq_abs] using
      ActualRootRemainder.integrated_difference_tendsto_zero L δ hδ a ha hAn hA U X hU hX ν μ k)

end SHE.ActualRootRemainderL2
