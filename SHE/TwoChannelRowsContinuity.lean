module
public import SHE.TwoChannelItoRows
public import SHE.InterpolatedPredictableRows
public import SHE.PredictableWeightContinuity
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.TwoChannelRowsContinuity
open MeasureTheory PredictableL2 OrthogonalItoChannels Filter Topology
open scoped NNReal ENNReal
variable {Ω C ι:Type*}[MeasurableSpace Ω][NormedAddCommGroup C][InnerProductSpace ℝ C]
variable [MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)(H:ℝ≥0)
local instance : MeasurableSpace (Both C):=borel _
local instance : BorelSpace (Both C):=⟨rfl⟩

theorem block {f:Filter ι}{u v:ι→Process (E:=C) 𝓕 μ H}{a b:Process (E:=C) 𝓕 μ H}
    (hu:Tendsto u f (𝓝 a))(hv:Tendsto v f (𝓝 b)):
    Tendsto (fun i=>TwoChannelItoRows.block 𝓕 μ H (u i) (v i)) f
      (𝓝 (TwoChannelItoRows.block 𝓕 μ H a b)):=by
  exact ((PredictableItoRotation.processIsometry 𝓕 μ H (fun _=>left (C:=C)) (left_measurable 𝓕)).continuous.tendsto a |>.comp hu).add
    ((PredictableItoRotation.processIsometry 𝓕 μ H (fun _=>right (C:=C)) (right_measurable 𝓕)).continuous.tendsto b |>.comp hv)

theorem rescaled_difference {f:Filter ι}{u v:ι→Process (E:=C) 𝓕 μ H}{a b:Process (E:=C) 𝓕 μ H}
    (hu:Tendsto u f (𝓝 a))(hv:Tendsto v f (𝓝 b)){Λ:ℝ}(hΛ:0≤Λ)(T:ℝ≥0):
    Tendsto (fun i=>InterpolatedPredictableRows.rescaledDifference 𝓕 μ H hΛ T (u i) (v i)) f
      (𝓝 (InterpolatedPredictableRows.rescaledDifference 𝓕 μ H hΛ T a b)):=by
  have hw:=(PredictableWeightContinuity.lipschitz 𝓕 μ H (PredictableDamping.weight Λ T)
    (PredictableDamping.weight_predictable 𝓕 Λ T) (PredictableDamping.weight_bound hΛ T)).continuous.tendsto (b-a)
  have hs:=(hw.comp (hv.sub hu)).const_smul (Real.exp (Λ*(T:ℝ)))
  exact (PredictableItoRotation.processIsometry 𝓕 μ H (fun _=>right (C:=C)) (right_measurable 𝓕)).continuous.tendsto _ |>.comp hs

end SHE.TwoChannelRowsContinuity
