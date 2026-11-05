module
public import SHE.MovingNativeKernelFields
public import SHE.JointHeldPast
public import SHE.MixedNativeFrozenPrefixIto
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.MovingNativePredictablePoint
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  Set WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalParentGeometry PhysicalProfile CoveredControlledLaw
open scoped NNReal ENNReal
local instance movingNativePredictablePoint_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingNativePredictablePoint_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance movingNativePredictablePoint_unitSigma:MeasurableSpace CircleHeat.CircleL2:=borel _
local instance movingNativePredictablePoint_unitBorel:BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance movingNativePredictablePoint_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance movingNativePredictablePoint_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance movingNativePredictablePoint_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance movingNativePredictablePoint_unitSecond:SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance movingNativePredictablePoint_realSigma:MeasurableSpace RealL2:=borel _
local instance movingNativePredictablePoint_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance movingNativePredictablePoint_realSecond:SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
local notation "Data"=>MixedNativeFrozenPrefixIto.data
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S

def heldPast(z:ℝ≥0×(ℝ≥0×Ω)):Inputs:=
  PredictablePastParameter.held z.1 (Data z.1) (0,0) z.2
local notation "Held"=>heldPast 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

/-- A countable left-known construction supplies the actual moving past,
jointly with the ORIGINAL current predictable sigma algebra. -/
theorem heldPast_predictable:
    StronglyMeasurable[((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable)] Held:=by
  have ha:StronglyAdapted 𝓕 (fun v=>Data v):=fun v=>
    (MixedNativeFrozenPrefixIto.data_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).stronglyMeasurable
  have hc:∀ω,Continuous (fun v=>Data v ω):=fun ω=>
    (embed.continuous.comp (S.first_continuous ω)).prodMk
      (embed.continuous.comp ((S.second_continuous ω).sub (S.first_continuous ω)))
  exact JointHeldPast.stronglyMeasurable 𝓕 _ (0,0) ha hc

variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0)(Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledWordTimeShift.relativeLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "Point"=>MovingNativeKernelFields.point
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Mean"=>MovingNativeKernelFields.mean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

def currentMean(k:ℕ)(θ:ℝ)(z:(ℝ≥0×(ℝ≥0×Ω))×History HeatCircle k):WordRecursion.State (1+k):=
  WithLp.toLp 2 (fun i=>
    functional (targets Zero k z.2 i-((z.1.2.1-z.1.1:ℝ≥0):ℝ)) (centers Zero k z.2 i)
      (S.first z.1.2.1 z.1.2.2)+
    θ*Real.exp (-Λ*(stops Zero k z.2 i-((z.1.2.1-z.1.1:ℝ≥0):ℝ)))*
      functional (targets Zero k z.2 i-((z.1.2.1-z.1.1:ℝ≥0):ℝ)) (centers Zero k z.2 i)
        (S.second z.1.2.1 z.1.2.2-S.first z.1.2.1 z.1.2.2))
local notation "Current"=>currentMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

theorem currentMean_predictable(k:ℕ)(θ:ℝ):
    @Measurable ((ℝ≥0×(ℝ≥0×Ω))×History HeatCircle k) _
      ((((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable).prod inferInstance)) _ (Current k θ):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hq:Measurable (fun z:(ℝ≥0×(ℝ≥0×Ω))×History HeatCircle k=>
      ((z.1.2.1-z.1.1:ℝ≥0):ℝ)):=NNReal.continuous_coe.measurable.comp
    (((PredictableClock.time_measurable 𝓕).comp measurable_fst.snd).sub measurable_fst.fst)
  have hU:=S.first_predictable.measurable.comp
    (measurable_fst.snd:Measurable (fun z:(ℝ≥0×(ℝ≥0×Ω))×History HeatCircle k=>z.1.2))
  have hD:=(S.second_predictable.sub S.first_predictable).measurable.comp
    (measurable_fst.snd:Measurable (fun z:(ℝ≥0×(ℝ≥0×Ω))×History HeatCircle k=>z.1.2))
  apply (WithLp.measurable_toLp 2 (Fin (1+k)→ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hT:Measurable (fun p:History HeatCircle k=>targets Zero k p i):=(carrier Zero k).observations.target_measurable i
  have hx:Measurable (fun p:History HeatCircle k=>centers Zero k p i):=(carrier Zero k).observations.center_measurable i
  have hσ:Measurable (fun p:History HeatCircle k=>stops Zero k p i):=by
    change Measurable (fun p=>min ((carrier Zero k).observations.observations p i).stop (h:ℝ))
    exact ((carrier Zero k).observations.stop_measurable i).min measurable_const
  have harg:=((hT.comp measurable_snd).sub hq).prodMk (hx.comp measurable_snd)
  have hfirst:=functional_joint_measurable.comp (hU.prodMk harg)
  have hdiff:=functional_joint_measurable.comp (hD.prodMk harg)
  have hdamp:=(((hσ.comp measurable_snd).sub hq).const_mul (-Λ)).exp.const_mul θ
  convert! hfirst.add (hdamp.mul hdiff) using 1

/-- The actual relative-row point, placed on the original current clock
with its strict post-past support. -/
def point(k:ℕ)(weighted:Bool)(θ:ℝ)
    (z:((ℝ≥0×(ℝ≥0×Ω))×History HeatCircle k)×HeatCircle):ℝ:=
  if z.1.1.1<z.1.1.2.1 ∧ z.1.1.2.1<z.1.1.1+h then
    Point k weighted θ z.1.1.1 (z.1.1.2.1-z.1.1.1) z.1.2 z.2 z.1.1.2.2
  else 0
local notation "Field"=>point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

/-- Genuine parameter-by-predictable measurability of the literal
actual Gaussian row, including the correlated moving past. -/
theorem point_predictable(k:ℕ)(weighted:Bool)(θ:ℝ):
    @Measurable (((ℝ≥0×(ℝ≥0×Ω))×History HeatCircle k)×HeatCircle) ℝ
      (((((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable).prod inferInstance)).prod inferInstance) _
      (Field k weighted θ):=by
  classical
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  let W:=((ℝ≥0×(ℝ≥0×Ω))×History HeatCircle k)×HeatCircle
  have hp:Measurable (fun z:W=>(θ,Held z.1.1)):=measurable_const.prodMk
    ((heldPast_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S).measurable.comp measurable_fst.fst)
  have hq:Measurable (fun z:W=>((z.1.1.2.1-z.1.1.1:ℝ≥0):ℝ)):=
    NNReal.continuous_coe.measurable.comp
      (((PredictableClock.time_measurable 𝓕).comp measurable_fst.fst.snd).sub measurable_fst.fst.fst)
  have hm:Measurable (fun z:W=>Current k θ z.1):=
    (currentMean_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm k θ).comp measurable_fst
  have hpoint:Measurable (fun z:W=>if weighted then
      ActualMeanKernel.weightedPoint (Base (θ,Held z.1.1)) k Λ
        ((z.1.1.2.1-z.1.1.1:ℝ≥0):ℝ) ((z.1.1.2.1-z.1.1.1:ℝ≥0):ℝ)
        (fun _=>Current k θ z.1) z.1.2 z.2 else
      ActualMeanKernel.rowPoint (Base (θ,Held z.1.1)) k
        ((z.1.1.2.1-z.1.1.1:ℝ≥0):ℝ) ((z.1.1.2.1-z.1.1.1:ℝ≥0):ℝ)
        (fun _=>Current k θ z.1) z.1.2 z.2):=by
    cases weighted
    · simpa only [Bool.false_eq_true,if_false,ControlledWordTimeShift.relativeLevel] using
        ControlledThetaNativePointFields.rowPoint_measurable P haP Λ 0 h bot_le Z htarget hstop F hF hFm k
          _ hp _ measurable_fst.snd _ _ hq hq _ hm _ measurable_snd
    · simpa only [if_true,ControlledWordTimeShift.relativeLevel] using
        ControlledThetaWeightedFields.weightedPoint_measurable P P.coefficient haP Λ 0 h bot_le Z htarget hstop F hF hFm k
          _ hp _ measurable_fst.snd _ _ hq hq _ hm _ measurable_snd
  have htime:Measurable (fun z:W=>z.1.1.2.1):=(PredictableClock.time_measurable 𝓕).comp measurable_fst.fst.snd
  have hv:Measurable (fun z:W=>z.1.1.1):=measurable_fst.fst.fst
  have hvh:Measurable (fun z:W=>z.1.1.1+h):=hv.add measurable_const
  have hset:MeasurableSet {z:W|z.1.1.1<z.1.1.2.1 ∧ z.1.1.2.1<z.1.1.1+h}:=
    (measurableSet_lt (α:=ℝ≥0) hv htime).inter (measurableSet_lt (α:=ℝ≥0) htime hvh)
  convert! hpoint.ite hset (measurable_const (a:=(0:ℝ))) using 1
  funext z
  by_cases hz:z.1.1.1<z.1.1.2.1 ∧ z.1.1.2.1<z.1.1.1+h
  · have hsum:z.1.1.1+(z.1.1.2.1-z.1.1.1)=z.1.1.2.1:=add_tsub_cancel_of_le hz.1.le
    have hheld:Held z.1.1=Data z.1.1.1 z.1.1.2.2:=by
      exact PredictablePastParameter.held_eq _ _ hz.1
    have hmz:Mean k θ z.1.1.1 (z.1.1.2.1-z.1.1.1) z.1.1.2.2=
        (fun p=>Current k θ (z.1.1,p)):=by
      funext p
      simp only [MovingNativeKernelFields.mean,currentMean,hsum]
    simp only [point,if_pos hz,MovingNativeKernelFields.point]
    unfold heldPast
    rw [PredictablePastParameter.held_eq _ _ hz.1]
    cases weighted <;>
      simp only [Bool.false_eq_true,if_false,if_true,ActualMeanKernel.rowPoint,
        ActualMeanKernel.weightedPoint,hmz,MixedNativeFrozenPrefixIto.data]
  · simp only [point,if_neg hz]
  all_goals infer_instance
end SHE.MovingNativePredictablePoint
