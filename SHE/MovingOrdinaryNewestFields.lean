module
public import SHE.MixedPastNewestOrdinaryError
public import SHE.ControlledThetaBackwardFields
public import SHE.PhysicalWordErrorFields
public import SHE.MovingNativeKernelFields
public import SHE.MovingNativeFields
public import SHE.MixedPastNativeTimeFields
public import SHE.NativeRowTimeShift

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.MovingOrdinaryNewestFields
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
attribute [local irreducible] GaussianConvolution.gaussianAverage ActualMeanKernel.cappedAverage
  GaussianTaylor.hessian WordRecursion.hessian UncutSmoothWords.test
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

local notation "Mean"=>MovingNativeKernelFields.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Error"=>MixedPastNewestOrdinaryError.errorField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

/-- Actual U coefficient error stays outside the full backward
Gaussian Hessian; the past and physical current move jointly. -/
def point(k:ℕ)(v s:ℝ≥0)(p:History HeatCircle k)(y:HeatCircle)(ω:Ω):ℝ:=
  if (s:ℝ)<(carrier Zero k).terminal p then
    (1/2:ℝ)*Error ((v+s,ω),y)*
      GaussianTaylor.hessian (ActualMeanKernel.cappedAverage (Base (0,Past v ω)) k s p)
        (Mean k 0 v s ω p)
        (heatRow ((carrier Zero k).observations.observations p) s y)
        (heatRow ((carrier Zero k).observations.observations p) s y)
  else 0
local notation "Point"=>point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem point_measurable(k:ℕ):Measurable
    (fun z:(((ℝ≥0×ℝ≥0)×Ω)×History HeatCircle k)×HeatCircle=>
      Point k z.1.1.1.1 z.1.1.1.2 z.1.2 z.2 z.1.1.2):=by
  let W:=(((ℝ≥0×ℝ≥0)×Ω)×History HeatCircle k)×HeatCircle
  have hPast:Measurable (fun z:W=>Past z.1.1.1.1 z.1.1.2):=
    (MovingNativeFields.past_inputs_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S).comp
      (measurable_fst.fst.fst.fst.prodMk measurable_fst.fst.snd)
  have hp:Measurable (fun z:W=>((0:ℝ),Past z.1.1.1.1 z.1.1.2)):=measurable_const.prodMk hPast
  have hq:Measurable (fun z:W=>(z.1.1.1.2:ℝ)):=
    measurable_subtype_coe.comp measurable_fst.fst.fst.snd
  let mmap:W→(ℝ×((ℝ≥0×ℝ≥0)×Ω))×History HeatCircle k:=fun z=>((0,z.1.1),z.1.2)
  have hmm:Measurable mmap:=(measurable_const.prodMk measurable_fst.fst).prodMk measurable_fst.snd
  have hm0:=(MovingNativeKernelFields.mean_joint_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k).comp hmm
  have hm:Measurable (fun z:W=>Mean k 0 z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2):=by
    convert! hm0 using 1
  have hB:Measurable (fun z:W=>GaussianTaylor.hessian
      (ActualMeanKernel.cappedAverage (Base (0,Past z.1.1.1.1 z.1.1.2)) k z.1.1.1.2 z.1.2)
      (Mean k 0 z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2)):=by
    convert! (ControlledThetaBackwardFields.hessian_joint_measurable
      P P.coefficient haP Λ 0 h bot_le Z htarget hstop F hF hFm k).comp
      ((hp.prodMk (hq.prodMk measurable_fst.snd)).prodMk hm) using 1
  have hr:Measurable (fun z:W=>heatRow ((carrier Zero k).observations.observations z.1.2) z.1.1.1.2 z.2):=
    (carrier Zero k).observations.heatRow_measurable.comp
      (measurable_fst.snd.prodMk (hq.prodMk measurable_snd))
  have hbil:=((continuous_fst.clm_apply continuous_snd).measurable.comp
    (((continuous_fst.clm_apply continuous_snd).measurable.comp (hB.prodMk hr)).prodMk hr))
  have hu:Measurable (Function.uncurry S.first):=(S.first_predictable.mono (predictable_le_product 𝓕)).measurable
  have hn:=PredictableScalarField.nativeField_measurable hu
  have he:Measurable Error:=(haU.comp hn).sub (haV.comp hn)
  have hemap:Measurable (fun z:W=>((z.1.1.1.1+z.1.1.1.2,z.1.1.2),z.2)):=
    (((measurable_fst.fst.fst.fst.add measurable_fst.fst.fst.snd).prodMk measurable_fst.fst.snd).prodMk measurable_snd)
  have hactive:MeasurableSet {z:W|(z.1.1.1.2:ℝ)<(carrier Zero k).terminal z.1.2}:=
    measurableSet_lt hq ((carrier Zero k).terminal_measurable.comp measurable_fst.snd)
  convert! ((he.comp hemap |>.const_mul (1/2:ℝ)).mul hbil).ite hactive measurable_const using 1

/-- The full current integral remains a moving-past Borel field on the
fixed relative history, including the actual physical error factor. -/
def primitive(k:ℕ)(z:(ℝ≥0×Ω)×History HeatCircle k):ℝ:=
  ∫s in Ioc (0:ℝ) (h:ℝ),∫y,Point k z.1.1 s.toNNReal z.2 y z.1.2 ∂haarAddCircle
local notation "Primitive"=>primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem primitive_measurable(k:ℕ):Measurable (Primitive k):=by
  have hh:Measurable (fun z:(((ℝ≥0×Ω)×History HeatCircle k)×ℝ)×HeatCircle=>
      Point k z.1.1.1.1 z.1.2.toNNReal z.1.1.2 z.2 z.1.1.1.2):=
    (point_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k).comp
      ((((measurable_fst.fst.fst.fst.prodMk (measurable_real_toNNReal.comp measurable_fst.snd)).prodMk
        measurable_fst.fst.fst.snd).prodMk measurable_fst.fst.snd).prodMk measurable_snd)
  exact hh.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable

def average(k:ℕ)(z:(ℝ≥0×Ω)×HeatCircle):ℝ:=
  ∫t:Fin k→ℝ,∫w:Fin k→HeatCircle,
    Primitive k (z.1,separated k (z.2,t,w)) ∂Measure.pi (fun _=>haarAddCircle)
    ∂Measure.pi (fun _=>volume.restrict (Ioc 0 (h:ℝ)))
local notation "Average"=>average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem average_measurable(k:ℕ):Measurable (Average k):=by
  have hh:Measurable (fun z:(((ℝ≥0×Ω)×HeatCircle)×(Fin k→ℝ))×(Fin k→HeatCircle)=>
      Primitive k (z.1.1.1,separated k (z.1.1.2,z.1.2,z.2))):=
    (primitive_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k).comp
      (measurable_fst.fst.fst.prodMk ((separated_measurable k).comp
        (measurable_fst.fst.snd.prodMk (measurable_fst.snd.prodMk measurable_snd))))
  exact hh.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable

end SHE.MovingOrdinaryNewestFields
