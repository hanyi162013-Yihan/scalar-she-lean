module
public import SHE.JointHeldPast
public import SHE.FrozenReferenceFields
public import SHE.MixedNativeFrozenPrefixIto
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.JointFrozenReferenceFields
open Set MeasureTheory Filter ControlledProfile StoppedFourier NativeHeatObservation FiniteHaar DyadicApproximation
open scoped NNReal ENNReal
local instance jointFrozenReferenceFields_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance jointFrozenReferenceFields_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance jointFrozenReferenceFields_circleSigma : MeasurableSpace CircleL2:=borel _
local instance jointFrozenReferenceFields_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance jointFrozenReferenceFields_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance jointFrozenReferenceFields_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance jointFrozenReferenceFields_realSigma : MeasurableSpace RealL2:=borel _
local instance jointFrozenReferenceFields_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance jointFrozenReferenceFields_circleSecond : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance jointFrozenReferenceFields_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance jointFrozenReferenceFields_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω:Type*}[MeasurableSpace Ω](𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)
variable (P:CanonicalCovariance.ProfileParameters)(Λ κ θ:ℝ)(hκP:κ<P.lower)
variable (data:ℝ≥0→Ω→Inputs)

/-- The ORIGINAL frozen field with moving old time, jointly predictable
in its current noise variables. No independent restart is introduced. -/
theorem field_predictable (ha:StronglyAdapted 𝓕 data)
    (hc:∀ω,Continuous (fun v=>data v ω)):
    StronglyMeasurable[((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable)]
      (fun z:ℝ≥0×(ℝ≥0×Ω)=>FrozenReferenceFields.field P Λ κ θ hκP z.1 (data z.1) z.2):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hd:Measurable (fun z:ℝ≥0×(ℝ≥0×Ω)=>
      PredictablePastParameter.held z.1 (data z.1) (0,0) z.2):=
    (JointHeldPast.stronglyMeasurable 𝓕 data (0,0) ha hc).measurable
  have ht:Measurable (fun z:ℝ≥0×(ℝ≥0×Ω)=>(z.2.1:ℝ)-(z.1:ℝ)):=
    ((PredictableClock.real_time_measurable 𝓕).comp measurable_snd).sub
      (NNReal.continuous_coe.measurable.comp measurable_fst)
  exact ((ControlledResidualField.field_measurable P Λ κ hκP).comp
    ((hd.prodMk measurable_const).prodMk ht)).stronglyMeasurable

variable (μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)(hκ:0<κ)
variable {aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

/-- Actual constructed-pair applicability of joint old-time/future-noise
predictability, including its unbounded correlated old inputs. -/
theorem actual_field_predictable:
    StronglyMeasurable[((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable)]
      (fun z:ℝ≥0×(ℝ≥0×Ω)=>FrozenReferenceFields.field P Λ κ θ hκP z.1
        (MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S z.1) z.2):=by
  let D:ℝ≥0→Ω→Inputs:=fun v=>MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S v
  have ha:StronglyAdapted 𝓕 D:=fun v=>
    (MixedNativeFrozenPrefixIto.data_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).stronglyMeasurable
  have hc:∀ω,Continuous (fun v=>D v ω):=by
    intro ω
    exact (embed.continuous.comp (S.first_continuous ω)).prodMk
      (embed.continuous.comp ((S.second_continuous ω).sub (S.first_continuous ω)))
  exact field_predictable 𝓕 P Λ κ θ hκP D ha hc
end SHE.JointFrozenReferenceFields
