module
public import SHE.MovingCanonicalFrozenRows
public import SHE.NativeObservableFields
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.MovingFrozenInitial
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier NativeHeatObservation
open OrthogonalItoChannels DyadicApproximation MovingCanonicalFrozenRows
open scoped NNReal ENNReal
local instance movingFrozenInitial_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance movingFrozenInitial_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingFrozenInitial_realSigma : MeasurableSpace RealL2:=borel _
local instance movingFrozenInitial_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance movingFrozenInitial_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance movingFrozenInitial_circleSigma : MeasurableSpace CircleL2:=borel _
local instance movingFrozenInitial_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)(u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (θ W h:ℝ)

def state (v:ℝ≥0)(ω:Ω):RealL2:=
  heat h (S.first v ω+(θ*Real.exp (-Λ*h)) • (S.second v ω-S.first v ω))

theorem state_adapted:StronglyAdapted 𝓕 (state 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ h):=by
  intro v
  have hu:StronglyMeasurable[𝓕 v] (S.first v):=
    (show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v
  have hv:StronglyMeasurable[𝓕 v] (S.second v):=
    (show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted v
  have hs:StronglyMeasurable[𝓕 v] (fun ω=>(θ*Real.exp (-Λ*h)) •
      (S.second v ω-S.first v ω)):=by
    exact (stronglyMeasurable_const : StronglyMeasurable[𝓕 v]
      (fun _:Ω=>(θ*Real.exp (-Λ*h):ℝ))).smul (hv.sub hu)
  exact (heat h).continuous.comp_stronglyMeasurable (hu.add hs)

theorem state_continuous (ω:Ω):
    Continuous (fun v=>state 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ h v ω):=by
  have hs:Continuous (fun v=>(θ*Real.exp (-Λ*h)) • (S.second v ω-S.first v ω)):=by
    exact (continuous_const : Continuous (fun _:ℝ≥0=>(θ*Real.exp (-Λ*h):ℝ))).smul
      ((S.second_continuous ω).sub (S.first_continuous ω))
  exact (heat h).continuous.comp ((S.first_continuous ω).add hs)

def held (z:ℝ×(ℝ≥0×Ω)):RealL2:=
  PredictablePastParameter.held (NativeMovingGammaClock.past W z.1)
    (state 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ h
      (NativeMovingGammaClock.past W z.1)) 0 z.2

/-- The moving full-target old mean has a genuine product-predictable
Hilbert realization, with correlated unbounded past states retained. -/
theorem held_predictable:
    StronglyMeasurable[((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable)]
      (held 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ W h):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hf:=JointHeldPast.stronglyMeasurable 𝓕
    (state 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ h) 0
    (state_adapted 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ h)
    (state_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ h)
  have hp:Measurable (fun z:ℝ×(ℝ≥0×Ω)=>(NativeMovingGammaClock.past W z.1,z.2)):=
    ((NativeMovingGammaClock.past_measurable W).comp measurable_fst).prodMk measurable_snd
  exact hf.comp_measurable hp

def scalar (z:(ℝ×(ℝ≥0×Ω))×HeatCircle):ℝ:=
  PredictableScalarField.nativeField
    (held 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ W h) z

theorem scalar_predictable:
    @Measurable ((ℝ×(ℝ≥0×Ω))×HeatCircle) ℝ
      (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance) _
      (scalar 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ W h):=by
  letI:MeasurableSpace (ℝ×(ℝ≥0×Ω)):=(inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable
  exact PredictableScalarField.nativeField_measurable
    (held_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ W h).measurable
end SHE.MovingFrozenInitial
