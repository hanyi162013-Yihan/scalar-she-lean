module
public import SHE.MovingFrozenInitial
public import SHE.NativeScalarProductAlgebra
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.MovingFrozenInitialIdentity
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier NativeHeatObservation
open OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance movingFrozenInitialIdentity_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance movingFrozenInitialIdentity_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingFrozenInitialIdentity_realSigma : MeasurableSpace RealL2:=borel _
local instance movingFrozenInitialIdentity_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance movingFrozenInitialIdentity_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)(u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (θ W h r:ℝ)(hh:0<h)(q:ℝ≥0)(hvq:NativeMovingGammaClock.past W r<q)
local notation "v"=>NativeMovingGammaClock.past W r
attribute [local irreducible] functional MovingFrozenInitial.scalar

include hh hvq in
/-- The genuinely product-predictable held old mean is the literal
full-target damped old heat functional after its original past. -/
theorem scalar_eq:
    ∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀ᵐω∂μ,
      MovingFrozenInitial.scalar 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ W h
        ((r,(q,ω)),x)=
      functional h x (S.first v ω+(θ*Real.exp (-Λ*h)) • (S.second v ω-S.first v ω)):=by
  have hu:Measurable (S.first v):=
    ((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted v).measurable.mono (𝓕.le v) le_rfl
  have hd:Measurable (fun ω=>S.second v ω-S.first v ω):=
    (((show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted v).measurable.mono
      (𝓕.le v) le_rfl).sub hu
  have hm:Measurable (fun ω=>S.first v ω+(θ*Real.exp (-Λ*h)) • (S.second v ω-S.first v ω)):=
    hu.add ((measurable_const : Measurable (fun _:Ω=>(θ*Real.exp (-Λ*h):ℝ))).smul hd)
  have he:=NativeScalarProductAlgebra.heat_ae μ
    (fun ω=>S.first v ω+(θ*Real.exp (-Λ*h)) • (S.second v ω-S.first v ω)) hm hh
  filter_upwards [he] with x hx
  filter_upwards [hx] with ω hω
  have hs:MovingFrozenInitial.held 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ W h
      (r,(q,ω))=heat h (S.first v ω+(θ*Real.exp (-Λ*h)) • (S.second v ω-S.first v ω)):=by
    exact PredictablePastParameter.held_eq (p:=(q,ω))
      (MovingFrozenInitial.state 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ h v) 0 hvq
  unfold MovingFrozenInitial.scalar PredictableScalarField.nativeField PredictableScalarField.unitField
  rw [hs]
  exact hω
end SHE.MovingFrozenInitialIdentity
