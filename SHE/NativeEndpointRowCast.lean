module
public import SHE.FullHorizonEndpointVersion
public import SHE.NativePhysicalRowCongruence
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 700000
namespace SHE.NativeObservationCovariance
open Set MeasureTheory PredictableL2 FiniteHaar NativeHeatObservation StoppedFourier
open scoped NNReal ENNReal
local instance nativeEndpointRowCast_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance nativeEndpointRowCast_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance nativeEndpointRowCast_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeEndpointRowCast_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeEndpointRowCast_circleSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeEndpointRowCast_circleBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩

/-- The actual original-horizon endpoint process has the literal
physical row in any equal-coefficient ellipticity packaging. -/
theorem endpoint_row_cast {Ω:Type*} [MeasurableSpace Ω]
    (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ]
    (H b:ℝ≥0) {ell M m U:ℝ} (hell:0<ell) (hM:0≤M) (hm:0<m)
    (f:ℝ≥0×Ω→EllipticField ell M) (hf:StronglyMeasurable[𝓕.predictable] f)
    (g:ℝ≥0×Ω→EllipticField m U) (hfg:∀p,(f p).1=(g p).1)
    (hbH:b≤H) (x:HeatCircle):
    ∀ᵐp∂energyMeasure μ H,p.1<b→
      FullHorizonEndpoint.process 𝓕 μ H b hell hM f hf (T:=(b:ℝ)) le_rfl x hbH p=
        row hm (g p) b p.1 x:=by
  filter_upwards [FullHorizonEndpoint.process_ae 𝓕 μ H b hell hM f hf
    (T:=(b:ℝ)) le_rfl x hbH] with p hp hpb
  have ht:(p.1:ℝ)<(b:ℝ):=by exact_mod_cast hpb
  rw [hp,FullHorizonEndpoint.raw,
    indicator_of_mem (show p∈StoppedItoInputs.before (Ω:=Ω) (b:ℝ) from ht),
    NativeObservationEndpoint.fullIntegrand,if_pos ht]
  exact row_congr hell hm (f p) (g p) (hfg p) b p.1 x

end SHE.NativeObservationCovariance
