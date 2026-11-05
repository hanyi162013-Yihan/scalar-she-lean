module
public import SHE.JointFrozenReferenceFields
public import SHE.NativeCanonicalVarianceField
public import SHE.NativeGammaVarianceShift
public import SHE.NativeMovingGammaClock
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.MovingCanonicalVariance
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier NativeHeatObservation
open DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance movingCanonicalVariance_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance movingCanonicalVariance_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingCanonicalVariance_realSigma : MeasurableSpace RealL2:=borel _
local instance movingCanonicalVariance_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance movingCanonicalVariance_circleSigma : MeasurableSpace CircleL2:=borel _
local instance movingCanonicalVariance_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance movingCanonicalVariance_circleSecond : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance movingCanonicalVariance_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance movingCanonicalVariance_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)(u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (W:ℝ)

def heldData (z:ℝ×(ℝ≥0×Ω)):Inputs:=
  PredictablePastParameter.held (NativeMovingGammaClock.past W z.1)
    (MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (NativeMovingGammaClock.past W z.1)) (0,0) z.2

theorem data_predictable:
    StronglyMeasurable[((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable)]
      (heldData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S W):=by
  let D:ℝ≥0→Ω→Inputs:=fun v=>MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S v
  have ha:StronglyAdapted 𝓕 D:=fun v=>
    (MixedNativeFrozenPrefixIto.data_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).stronglyMeasurable
  have hc:∀ω,Continuous (fun v=>D v ω):=by
    intro ω
    exact (embed.continuous.comp (S.first_continuous ω)).prodMk
      (embed.continuous.comp ((S.second_continuous ω).sub (S.first_continuous ω)))
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hf:=JointHeldPast.stronglyMeasurable 𝓕 D (0,0) ha hc
  have hp:Measurable (fun z:ℝ×(ℝ≥0×Ω)=>(NativeMovingGammaClock.past W z.1,z.2)):=
    ((NativeMovingGammaClock.past_measurable W).comp measurable_fst).prodMk measurable_snd
  exact hf.comp_measurable hp

variable (P:CanonicalCovariance.ProfileParameters)(θ h:ℝ)
def variance (z:(ℝ×(ℝ≥0×Ω))×HeatCircle):ℝ:=
  ControlledScalarCovarianceTailEnergy.field P Λ 0 h θ
    ((heldData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S W z.1,
      (z.1.2.1:ℝ)-(NativeMovingGammaClock.past W z.1.1:ℝ)),z.2)

/-- The actual moving-past covariance has a genuinely product-predictable
version. Its future profile is deterministic given the held original
past inputs; ambient measurability is never substituted for this fact. -/
theorem variance_predictable:
    @Measurable ((ℝ×(ℝ≥0×Ω))×HeatCircle) ℝ
      (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance) _
      (variance 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S W P θ h):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hd:Measurable (heldData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S W):=
    (data_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S W).measurable
  have ht:Measurable (fun z:ℝ×(ℝ≥0×Ω)=>(z.2.1:ℝ)-(NativeMovingGammaClock.past W z.1:ℝ)):=
    ((PredictableClock.real_time_measurable 𝓕).comp measurable_snd).sub
      (NNReal.continuous_coe.measurable.comp ((NativeMovingGammaClock.past_measurable W).comp measurable_fst))
  exact (ControlledScalarCovarianceTailEnergy.field_measurable P Λ 0 h θ).comp
    (((hd.comp measurable_fst).prodMk (ht.comp measurable_fst)).prodMk measurable_snd)

theorem variance_eq (hW:0≤W)(hh:0≤h)(r:ℝ)(q:ℝ≥0)
    (hvq:NativeMovingGammaClock.past W r<q)(hqb:q≤NativeMovingGammaClock.terminal W h r)
    (ω:Ω)(x:HeatCircle):
    variance 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S W P θ h ((r,(q,ω)),x)=
      NativeCanonicalVarianceField.field P Λ θ (NativeMovingGammaClock.past W r)
        (NativeMovingGammaClock.terminal W h r) (S.first (NativeMovingGammaClock.past W r))
        (fun ω=>S.second (NativeMovingGammaClock.past W r) ω-S.first (NativeMovingGammaClock.past W r) ω)
        ((q,ω),x):=by
  have hs:=NativeMovingGammaClock.span hW hh r
  have hq':(q:ℝ)-(NativeMovingGammaClock.past W r:ℝ)≤h:=by
    have hq'':(q:ℝ)≤NativeMovingGammaClock.terminal W h r:=by exact_mod_cast hqb
    linarith
  rw [NativeCanonicalVarianceField.field_eq _ _ _ _ _ _ _ _ hvq hqb]
  rw [NativeGammaVarianceShift.tail_relative _ _ _ _ _ _ (by exact_mod_cast hqb),hs]
  unfold variance heldData ControlledScalarCovarianceTailEnergy.field
  rw [PredictablePastParameter.held_eq (p:=(q,ω)) _ _ hvq,min_eq_left hq']
  rfl
end SHE.MovingCanonicalVariance
