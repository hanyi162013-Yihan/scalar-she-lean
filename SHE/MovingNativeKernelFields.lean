module
public import SHE.MovingNativeFields
public import SHE.MixedPastNativeTimeFields
public import SHE.NativeRowTimeShift

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.MovingNativeKernelFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingNativeKernelFields_realSigma : MeasurableSpace RealL2 := borel _
local instance movingNativeKernelFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingNativeKernelFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingNativeKernelFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingNativeKernelFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingNativeKernelFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
open PastItoInputs PastItoAlgebra PhysicalProfile


local instance movingNativeKernelFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingNativeKernelFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance movingNativeKernelFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingNativeKernelFields_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0)(Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledWordTimeShift.relativeLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "Past" v:max ω:max=>(embed (S.first v ω),embed (S.second v ω-S.first v ω))

/-- The literal covered native mean at the original current v+s,
expressed in a fixed relative observation frame. -/
def mean (k:ℕ)(θ:ℝ)(v s:ℝ≥0)(ω:Ω)(p:History HeatCircle k):WordRecursion.State (1+k):=
  WithLp.toLp 2 (fun i=>functional (targets Zero k p i-(s:ℝ)) (centers Zero k p i) (S.first (v+s) ω)+
    θ*exp (-Λ*(stops Zero k p i-(s:ℝ)))*
      functional (targets Zero k p i-(s:ℝ)) (centers Zero k p i) (S.second (v+s) ω-S.first (v+s) ω))
local notation "Mean"=>mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem mean_joint_measurable (k:ℕ):
    Measurable (fun z:(ℝ×((ℝ≥0×ℝ≥0)×Ω))×History HeatCircle k=>
      Mean k z.1.1 z.1.2.1.1 z.1.2.1.2 z.1.2.2 z.2):=by
  have hu:=(S.first_predictable.mono (predictable_le_product 𝓕)).measurable
  have hv:=(S.second_predictable.mono (predictable_le_product 𝓕)).measurable
  have hmap:Measurable (fun z:(ℝ×((ℝ≥0×ℝ≥0)×Ω))×History HeatCircle k=>
      (z.1.2.1.1+z.1.2.1.2,z.1.2.2)):=
    (measurable_fst.snd.fst.fst.add measurable_fst.snd.fst.snd).prodMk measurable_fst.snd.snd
  have hU:=hu.comp hmap
  have hD:=((S.second_predictable.sub S.first_predictable).mono (predictable_le_product 𝓕)).measurable.comp hmap
  apply (WithLp.measurable_toLp 2 (Fin (1+k)→ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hT:Measurable (fun p:History HeatCircle k=>targets Zero k p i):=(carrier Zero k).observations.target_measurable i
  have hx:Measurable (fun p:History HeatCircle k=>centers Zero k p i):=(carrier Zero k).observations.center_measurable i
  have hs:Measurable (fun p:History HeatCircle k=>stops Zero k p i):=by
    change Measurable (fun p=>min ((carrier Zero k).observations.observations p i).stop (h:ℝ))
    exact ((carrier Zero k).observations.stop_measurable i).min measurable_const
  have hq:Measurable (fun z:(ℝ×((ℝ≥0×ℝ≥0)×Ω))×History HeatCircle k=>(z.1.2.1.2:ℝ)):=
    measurable_subtype_coe.comp measurable_fst.snd.fst.snd
  have harg:=((hT.comp measurable_snd).sub hq).prodMk (hx.comp measurable_snd)
  have hfirst:=functional_joint_measurable.comp (hU.prodMk harg)
  have hdiff:=functional_joint_measurable.comp (hD.prodMk harg)
  have hdamp:=measurable_fst.fst.mul (((hs.comp measurable_snd).sub hq).const_mul (-Λ)).exp
  convert! hfirst.add (hdamp.mul hdiff) using 1

/-- Original q-law point kernels with the past and current both moving.
The two Boolean branches are the common kernel and signed endpoint row. -/
def point (k:ℕ)(weighted:Bool)(θ:ℝ)(v s:ℝ≥0)(p:History HeatCircle k)(y:HeatCircle)(ω:Ω):ℝ:=
  if weighted then ActualMeanKernel.weightedPoint (Base (θ,Past v ω)) k Λ s s (Mean k θ v s ω) p y
  else ActualMeanKernel.rowPoint (Base (θ,Past v ω)) k s s (Mean k θ v s ω) p y
local notation "Point"=>point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem point_joint_measurable (k:ℕ)(weighted:Bool):
    Measurable (fun z:((ℝ×((ℝ≥0×ℝ≥0)×Ω))×History HeatCircle k)×HeatCircle=>
      Point k weighted z.1.1.1 z.1.1.2.1.1 z.1.1.2.1.2 z.1.2 z.2 z.1.1.2.2):=by
  let W:=((ℝ×((ℝ≥0×ℝ≥0)×Ω))×History HeatCircle k)×HeatCircle
  have hPast:Measurable (fun z:W=>Past z.1.1.2.1.1 z.1.1.2.2):=
    (MovingNativeFields.past_inputs_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S).comp
      (measurable_fst.fst.snd.fst.fst.prodMk measurable_fst.fst.snd.snd)
  have hp:=measurable_fst.fst.fst.prodMk hPast
  have hq:Measurable (fun z:W=>(z.1.1.2.1.2:ℝ)):=
    measurable_subtype_coe.comp measurable_fst.fst.snd.fst.snd
  have hm:Measurable (fun z:W=>Mean k z.1.1.1 z.1.1.2.1.1 z.1.1.2.1.2 z.1.1.2.2 z.1.2):=
    (mean_joint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm k).comp measurable_fst
  cases weighted
  · simpa only [point,Bool.false_eq_true,if_false,ControlledWordTimeShift.relativeLevel,ActualMeanKernel.rowPoint] using
      ControlledThetaNativePointFields.rowPoint_measurable P haP Λ 0 h bot_le Z htarget hstop F hF hFm k
        _ hp _ measurable_fst.snd _ _ hq hq _ hm _ measurable_snd
  · simpa only [point,if_true,ControlledWordTimeShift.relativeLevel,ActualMeanKernel.weightedPoint] using
      ControlledThetaWeightedFields.weightedPoint_measurable P P.coefficient haP Λ 0 h bot_le Z htarget hstop F hF hFm k
        _ hp _ measurable_fst.snd _ _ hq hq _ hm _ measurable_snd

end SHE.MovingNativeKernelFields
