module

public import SHE.NativeFrozenPrefixObservation
public import SHE.NativeFrozenPrefixSmoothing
public import SHE.NativeFrozenSpatialObservation
public import SHE.NativeScalarProductAlgebra
public import SHE.NativeFixedHaarSemigroup
public import SHE.NativeFrozenHilbertField
public import SHE.NativeFixedHaarInput
public import SHE.NativeColumnHeatSemigroup
public import SHE.HilbertItoNaturality
public import SHE.NativeHeatFunctionalEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2300000
namespace SHE.NativeFrozenPrefixCurve
open Set MeasureTheory PredictableL2 FiniteHaar NativeHeatObservation DyadicApproximation
open scoped NNReal ENNReal
local instance nativeFrozenPrefixCurve_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeFrozenPrefixCurve_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeFrozenPrefixCurve_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeFrozenPrefixCurve_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeFrozenPrefixCurve_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance nativeFrozenPrefixCurve_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance nativeFrozenPrefixCurve_circleSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeFrozenPrefixCurve_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance nativeFrozenPrefixCurve_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeFrozenPrefixCurve_realBorel : BorelSpace RealL2:=⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable {ell M : ℝ} (hell : 0<ell) (hM : 0≤M)
variable (f : ℝ≥0×Ω→EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)

variable (b c v:ℝ≥0) (hcH:c≤H) (hc1:(c:ℝ)≤1)
variable (I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
local notation "Noise"=>NativeFrozenHilbertField.noise 𝓕 μ H c v hell hM f hf hcH hc1 I

/-- A true positive-prefix scalar version, rather than an unbounded
point evaluation of the frozen Hilbert martingale. -/
def scalar (p:(ℝ≥0×Ω)×StoppedFourier.HeatCircle):ℝ:=
  functional ((b:ℝ)-(c:ℝ)) p.2 (Noise p.1.1 p.1.2)

theorem continuous_scalar (hc0:0<c) (ω:Ω) (x:StoppedFourier.HeatCircle):
    Continuous (fun t=>scalar 𝓕 μ H hell hM f hf b c v hcH hc1 I ((t,ω),x)):=
  (functional ((b:ℝ)-(c:ℝ)) x).continuous.comp
    (NativeFrozenHilbertField.noise_continuous 𝓕 μ H c v hell hM f hf hcH hc1 I hc0 ω)

attribute [local irreducible] scalar NativeFrozenHilbertField.noise functional
theorem scalar_measurable (hc0:0<c) (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B:ℝ≥0) (hBDG:StandardTerminalBDG16 I B):
    Measurable (scalar 𝓕 μ H hell hM f hf b c v hcH hc1 I):=by
  have hnp:Measurable[𝓕.predictable] (Function.uncurry Noise):=
    (NativeFrozenHilbertField.noise_predictable 𝓕 μ H c v hell hM f hf hcH hc1 I hc0 hnull B hBDG).measurable
  have hn:Measurable (Function.uncurry Noise):=hnp.mono (predictable_le_product 𝓕) le_rfl
  unfold scalar
  change Measurable (fun p:(ℝ≥0×Ω)×StoppedFourier.HeatCircle=>
    functional ((b:ℝ)-(c:ℝ)) p.2 (Function.uncurry Noise p.1))
  exact NativeHeatObservation.functional_joint_measurable.comp
    ((hn.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))

end SHE.NativeFrozenPrefixCurve
