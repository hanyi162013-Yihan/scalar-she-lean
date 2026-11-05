module
public import SHE.OrdinaryLevelOriginalNoise
public import SHE.PastItoLimitWitness

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.OrdinaryOriginalAverage
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  CutoffWordLevel IntegratedPhysicalStep OrthogonalItoChannels
open scoped NNReal
local instance ordinaryOriginalAverage_realSigma:MeasurableSpace RealL2:=borel _
local instance ordinaryOriginalAverage_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance ordinaryOriginalAverage_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryOriginalAverage_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryOriginalAverage_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryOriginalAverage_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance ordinaryOriginalAverage_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryOriginalAverage_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω X:Type*}[MeasurableSpace Ω][MeasurableSpace X]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}
variable (m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable {R:ReferenceData}{n:ℕ}(L:Level R X n)

/-- Original finite-history averaging of the actual ordinary-U
martingale term, preserving the SAME full-horizon driver and post-v
support. The smooth reference coefficient need not match the bracket. -/
theorem original_post_input (hlocal:StandardTerminalPastLocality m.scalarIto)
    (v:ℝ≥0)(hbase:R.base=(v:ℝ))(hh:R.horizon≤(H:ℝ))
    {η:ℝ}(hη:0<η)(hgap:∀p i,η≤(L.observations.observations p i).target-L.terminal p)
    (ν:Measure X)[IsFiniteMeasure ν]:
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      m.scalarIto.integral (PastItoInputs.post 𝓕 μ H v input)=ᵐ[μ]
        fun ω=>∫p,(OrdinaryLevelOriginalNoise.data m L (fun _ _ _=>0)).noiseVersion p ω ∂ν:=by
  let D:=OrdinaryLevelOriginalNoise.data m L (fun _ _ _=>0)
  have hM:0≤M:=m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2)
  have ha:Measurable (fun z=>κ+a z):=measurable_const.add m.variance_measurable
  have hcap(z):|κ+a z|≤κ+M:=by
    rw [abs_of_nonneg (add_nonneg m.additive_pos.le (m.lower_pos.le.trans (m.variance_bounds z).1))]
    exact add_le_add le_rfl (m.variance_bounds z).2
  have hD:AnalyticConditions D:=ActualVarianceLevel.analyticConditions L (fun z=>κ+a z) ha
    m.physicalState m.physicalState_measurable m.physicalField m.physicalField_measurable (fun _ _ _=>0)
    (add_nonneg m.additive_pos.le hM) hcap
  obtain ⟨B,hB,hBb⟩:=uniform_level_bound D hD
  exact PastItoLimitWitness.bounded_post_average 𝓕 μ H v m.scalarIto ν
    (fun z:X×Ω=>D.noiseVersion z.1 z.2)
    ((hD.leaf_measurable.sub hD.reference_measurable).sub hD.remainder_measurable)
    hB (fun p ω=>(hBb p ω).2.2.2)
    (fun p=>OrdinaryLevelOriginalNoise.original_post_input m L hlocal v hbase hh hη hgap p)

end SHE.OrdinaryOriginalAverage
