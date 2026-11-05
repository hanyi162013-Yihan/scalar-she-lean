module
public import SHE.PhysicalWordErrorFields
public import SHE.MixedPastNewestOrdinaryError
public import SHE.InitialNativeKernelFields
public import SHE.InitialTerminalFields
public import SHE.MovingNativeFields
public import SHE.ZeroDirectionProfile
public import SHE.MixedPastNativeTimeFields
public import SHE.NativeRowTimeShift

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.InitialOrdinaryNewestFields
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
variable (h:ℝ≥0)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "R"=>InitialNativeKernelFields.referenceData Λ u₀ P haP h
local notation "L"=>InitialTerminalLevel.level R F hF hFm
local notation "Root"=>InitialTerminalLevel.Root R

local notation "Mean"=>InitialNativeKernelFields.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "Error"=>MixedPastNewestOrdinaryError.errorField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

def point(k:ℕ)(q:ℝ≥0)(p:History Root k)(y:HeatCircle)(ω:Ω):ℝ:=
  if (q:ℝ)<(carrier L k).terminal p then
    (1/2:ℝ)*Error ((q,ω),y)*
      WordRecursion.hessian (ActualMeanKernel.cappedAverage L k q p) (Mean k 0 q ω p)
        (heatRow ((carrier L k).observations.observations p) q y)
        (heatRow ((carrier L k).observations.observations p) q y)
  else 0
local notation "Point"=>point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

theorem point_measurable(k:ℕ):Measurable
    (fun z:((ℝ≥0×Ω)×History Root k)×HeatCircle=>Point k z.1.1.1 z.1.2 z.2 z.1.1.2):=by
  let W:=((ℝ≥0×Ω)×History Root k)×HeatCircle
  have hq:Measurable (fun z:W=>(z.1.1.1:ℝ)):=measurable_subtype_coe.comp measurable_fst.fst.fst
  let mmap:W→(ℝ×(ℝ≥0×Ω))×History Root k:=fun z=>((0,z.1.1),z.1.2)
  have hmm:Measurable mmap:=(measurable_const.prodMk measurable_fst.fst).prodMk measurable_fst.snd
  have hm0:=(InitialNativeKernelFields.mean_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k).comp hmm
  have hm:Measurable (fun z:W=>Mean k 0 z.1.1.1 z.1.1.2 z.1.2):=by
    convert! hm0 using 1
  have hB:= (PhysicalChainArrays.capped_hessian_joint_measurable L k).comp
    ((hq.prodMk measurable_fst.snd).prodMk hm)
  have hr:Measurable (fun z:W=>heatRow ((carrier L k).observations.observations z.1.2) z.1.1.1 z.2):=
    (carrier L k).observations.heatRow_measurable.comp
      (measurable_fst.snd.prodMk (hq.prodMk measurable_snd))
  have hbil:=((continuous_fst.clm_apply continuous_snd).measurable.comp
    (((continuous_fst.clm_apply continuous_snd).measurable.comp (hB.prodMk hr)).prodMk hr))
  have hu:Measurable (Function.uncurry S.first):=(S.first_predictable.mono (predictable_le_product 𝓕)).measurable
  have hn:=PredictableScalarField.nativeField_measurable hu
  have he:Measurable Error:=(haU.comp hn).sub (haV.comp hn)
  have hemap:Measurable (fun z:W=>(z.1.1,z.2)):=measurable_fst.fst.prodMk measurable_snd
  have hactive:MeasurableSet {z:W|(z.1.1.1:ℝ)<(carrier L k).terminal z.1.2}:=
    measurableSet_lt hq ((carrier L k).terminal_measurable.comp measurable_fst.snd)
  convert! ((he.comp hemap |>.const_mul (1/2:ℝ)).mul hbil).ite hactive measurable_const using 1

/-- The initial current is integrated only up to its actual variable
terminal; its output is never silently extended as a complete window. -/
def primitive(k:ℕ)(z:((Icc (R).base (R).horizon)×Ω)×History HeatCircle k):ℝ:=
  ∫q in Ioc (0:ℝ) (h:ℝ),if q≤(z.1.1:ℝ) then
    ∫y,Point k q.toNNReal (InitialTerminalFields.lift R z.1.1 k z.2) y z.1.2 ∂haarAddCircle else 0
local notation "Primitive"=>primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

theorem primitive_measurable(k:ℕ):Measurable (Primitive k):=by
  let W:=(((Icc (R).base (R).horizon)×Ω)×History HeatCircle k)×ℝ
  have hl:Measurable (fun z:W=>InitialTerminalFields.lift R z.1.1.1 k z.1.2):=
    (InitialTerminalFields.lift_measurable R k).comp (measurable_fst.fst.fst.prodMk measurable_fst.snd)
  have hh:Measurable (fun z:W×HeatCircle=>
      Point k z.1.2.toNNReal (InitialTerminalFields.lift R z.1.1.1.1 k z.1.1.2) z.2 z.1.1.1.2):=
    (point_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k).comp
      ((((measurable_real_toNNReal.comp measurable_fst.snd).prodMk measurable_fst.fst.fst.snd).prodMk
        (hl.comp measurable_fst)).prodMk measurable_snd)
  have hs:MeasurableSet {z:W|z.2≤(z.1.1.1:ℝ)}:=
    measurableSet_le measurable_snd (measurable_subtype_coe.comp measurable_fst.fst.fst)
  have hinner:Measurable (fun z:W=>if z.2≤(z.1.1.1:ℝ) then
      ∫y,Point k z.2.toNNReal (InitialTerminalFields.lift R z.1.1.1 k z.1.2) y z.1.1.2 ∂haarAddCircle else 0):=
    (hh.stronglyMeasurable.integral_prod_right'.measurable).ite hs measurable_const
  exact hinner.stronglyMeasurable.integral_prod_right'.measurable

def average(k:ℕ)(z:((Icc (R).base (R).horizon)×Ω)×HeatCircle):ℝ:=
  ∫t:Fin k→ℝ,if ∀i,t i≤(z.1.1:ℝ) then
    ∫w:Fin k→HeatCircle,Primitive k (z.1,separated k (z.2,t,w)) ∂Measure.pi (fun _=>haarAddCircle) else 0
    ∂Measure.pi (fun _=>volume.restrict (Ioc 0 (h:ℝ)))
local notation "Average"=>average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

theorem average_measurable(k:ℕ):Measurable (Average k):=by
  let W:=(((Icc (R).base (R).horizon)×Ω)×HeatCircle)×(Fin k→ℝ)
  have hh:Measurable (fun z:W×(Fin k→HeatCircle)=>
      Primitive k (z.1.1.1,separated k (z.1.1.2,z.1.2,z.2))):=
    (primitive_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k).comp
      (measurable_fst.fst.fst.prodMk ((separated_measurable k).comp
        (measurable_fst.fst.snd.prodMk (measurable_fst.snd.prodMk measurable_snd))))
  have hs:MeasurableSet {z:W|∀i,z.2 i≤(z.1.1.1:ℝ)}:=by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le ((measurable_pi_apply i).comp measurable_snd)
      (measurable_subtype_coe.comp measurable_fst.fst.fst)
  exact ((hh.stronglyMeasurable.integral_prod_right'.measurable).ite hs measurable_const).stronglyMeasurable.integral_prod_right'.measurable

end SHE.InitialOrdinaryNewestFields
