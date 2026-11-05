module

public import SHE.MixedPastProfileDerivative
public import SHE.ForestLeafMarkEnergy
public import SHE.MixedPastOmittedLeafMoments
public import SHE.ScalarRootSharpSections
public import SHE.HistoryRelativeSections
public import SHE.MixedPastDerivativeRMS
public import SHE.MixedPastOmittedMarkFields
public import SHE.MixedPastLiteralOmitted
public import SHE.ControlledThetaOmittedFields
public import SHE.ControlledFamilyProfileMarkFields
public import SHE.MixedPastLiteralFields
public import SHE.JointInterpolationFields
public import SHE.WeightedRowTimeShift
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledThetaWeightedFields
public import SHE.MixedPastDecayedWord
public import SHE.RelativeHistoryGeometry
public import SHE.ParentHeatFields
public import SHE.MixedPastActualMean
public import SHE.MixedPastJointData
public import SHE.MixedNativeJointHistory
public import SHE.ControlledJointMeanIdentity
public import SHE.CarrierStopBounds
public import SHE.CoveredControlledLaw
public import SHE.JointWordAnalytic
public import SHE.PastEventWeights
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 650000

namespace SHE.MixedPastOmittedLeafSpatial
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastOmittedLeafSpatial_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastOmittedLeafSpatial_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastOmittedLeafSpatial_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastOmittedLeafSpatial_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastOmittedLeafSpatial_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastOmittedLeafSpatial_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastOmittedLeafSpatial_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastOmittedLeafSpatial_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastOmittedLeafSpatial_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v


open HistoryProductMeasure ScalarRootRelativeGeometry ProfileL2

def relativeLeaf (k : ℕ) (θ : ℝ) (q : ℝ≥0) (t : Fin k→ℝ) (j0 : Fin k)
    (z : (Ω×HeatCircle)×(Fin k→HeatCircle)) : ℝ :=
  MixedPastOmittedMarkFields.leafMark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ q
      (separated k (z.1.2,t,fun i=>z.2 i+z.1.2)) j0 z.1.1

theorem relative_leaf_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) (θ : ℝ) (q : ℝ≥0) (t : Fin k→ℝ) (j0 : Fin k) :
    Measurable (relativeLeaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q t j0) := by
  let p:=fun z : (Ω×HeatCircle)×(Fin k→HeatCircle)=>separated k (z.1.2,t,fun i=>z.2 i+z.1.2)
  have hsites : Measurable (fun z : (Ω×HeatCircle)×(Fin k→HeatCircle)=>fun i=>z.2 i+z.1.2):=
    Measurable.of_eval (fun i=>((measurable_pi_apply i).comp measurable_snd).add measurable_fst.snd)
  have hp : Measurable p:=(separated_measurable k).comp
    (measurable_fst.snd.prodMk (measurable_const.prodMk hsites))
  have hh:=MixedPastOmittedMarkFields.leaf_mark_joint_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall k q j0
  convert! hh.comp ((measurable_const.prodMk measurable_fst.fst).prodMk hp) using 1

include hIJ₀ hIJ₁ in
/-- The literal actual omitted-baseline leaf is averaged in original
relative old space BEFORE sample/output L2. The derivative and native
word remain correlated throughout the conditional estimate. -/
theorem spatial_energy_ae (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon)
    (A : ℝ) (hA : ∀ x i,(Z.observations x i).target=A)
    (hcenter : ∀ x i,(Z.observations x i).center=x) (k : ℕ) :
    ∀ᵐ t : Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      let a:=separated k ((0:HeatCircle),t,fun _=>(0:HeatCircle))
      ∀ q : ℝ≥0,v≤q→q≤H→(q:ℝ)<(carrier Zero k).terminal a→
      ∀ hp : StrictHistory Zero k a,SmallHistory Zero (uniformHorizon 1) k a→
      ∀ θ : ℝ,|θ|≤1→∀ A0 ν : ℝ,0≤A0→0≤ν→
      (∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)→
      ∀ j0 : Fin k,∀ B0 : ℝ≥0,StandardTerminalBDGPower (k+2) J B0→
      let age:=targets Zero k a (leafIndex k (fun i=>i) j0)-(v:ℝ)
      let e:=MixedPastDerivativeRMS.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v age θ
      Integrable (fun z : Ω×HeatCircle=>|e z|^2) (μ.prod haarAddCircle)→
      let sharp:=MixedPastOmittedWord.total (d:=1) P
        (fun j=>lower Zero k a j-(v:ℝ)) (fun j=>upper Zero k a j-(v:ℝ))
        (fun j=>targets Zero k a (leafIndex k (fun i=>i) j)-(v:ℝ)) j0 A0 ν
      let scale:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a
      let C:=MixedPastOmittedWord.momentConstant P k k 1 j0
        ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
      let G:=relativeLeaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q t j0
      Integrable (fun z : Ω×HeatCircle=>|∫ w,G (z,w)
        ∂Measure.pi (fun _ : Fin k=>haarAddCircle)|^2) (μ.prod haarAddCircle) ∧
      (∫ z : Ω×HeatCircle,|∫ w,G (z,w)
        ∂Measure.pi (fun _ : Fin k=>haarAddCircle)|^2 ∂μ.prod haarAddCircle)≤
        C*(scale*sharp)^2*(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)^2*
          (∫ z : Ω×HeatCircle,|e z|^2 ∂μ.prod haarAddCircle) := by
  have hT : ∀ x,(Zero).terminal x=(b:ℝ):=fun _=>rfl
  have hA' : ∀ x i,((Zero).observations.observations x i).target=A:=hA
  have hc' : ∀ x i,((Zero).observations.observations x i).center=x:=hcenter
  have hpoint:=MixedPastOmittedLeafMoments.leaf_moment_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmall hages hspan haarAddCircle k
  have hsec:=ae_relative_spatial_sections _ k hpoint
  filter_upwards [hsec] with t ht
  intro a q hvq hqH hqt hp hs θ hθ A0 ν hA0 hν hjet j0 B0 hBDG age e hei sharp scale C G
  let p:=fun (x : HeatCircle) (w : Fin k→HeatCircle)=>separated k (x,t,fun i=>w i+x)
  let ind : Fin (1+k):=leafIndex (n:=1) k (fun i=>i) j0
  let tt:=targets Zero k a
  have hord : OrderedHeatForests.OrderedTimes k tt:=carrier_orderedTimes Zero hages k a hp
  have hm:=relative_leaf_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmall k θ q t j0
  have hem:=MixedPastDerivativeRMS.field_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hΛ hsmall v age θ
  have hei' := hei.prod_left_ae
  have htranslated : ∀ᵐ x : HeatCircle ∂haarAddCircle,∀ᵐ w : Fin k→HeatCircle ∂Measure.pi (fun _=>haarAddCircle),
      Integrable (fun ω=>|e (ω,x+OrderedHeatForests.values (fun _ : Fin 1=>(0:HeatCircle)) k w ind)|^2) μ := by
    have hfull : ∀ᵐ w : Fin k→HeatCircle ∂Measure.pi (fun _=>haarAddCircle),∀ᵐ x : HeatCircle ∂haarAddCircle,
        Integrable (fun ω=>|e (ω,x+OrderedHeatForests.values (fun _ : Fin 1=>(0:HeatCircle)) k w ind)|^2) μ := by
      apply ae_of_all
      intro w
      convert! (measurePreserving_add_right haarAddCircle
        (OrderedHeatForests.values (fun _ : Fin 1=>(0:HeatCircle)) k w ind)).quasiMeasurePreserving.ae hei' using 1
    have hmfun : Measurable (fun z : (HeatCircle×(Fin k→HeatCircle))×Ω=>
        |e (z.2,z.1.1+OrderedHeatForests.values (fun _ : Fin 1=>(0:HeatCircle)) k z.1.2 ind)|^2) :=
      (continuous_abs.measurable.comp (hem.comp (measurable_snd.prodMk
        (measurable_fst.fst.add (((continuous_apply ind).measurable.comp
          (OrderedHeatForests.values_continuous (fun _ : Fin 1=>(0:HeatCircle)) k).measurable).comp measurable_fst.snd))))).pow_const 2
    have hme : MeasurableSet {z : HeatCircle×(Fin k→HeatCircle)|
      Integrable (fun ω=>|e (ω,z.1+OrderedHeatForests.values (fun _ : Fin 1=>(0:HeatCircle)) k z.2 ind)|^2) μ}:=
      _root_.measurableSet_integrable hmfun.stronglyMeasurable
    exact (Measure.ae_ae_comm hme).mpr hfull
  have hinput (x : HeatCircle) (w : Fin k→HeatCircle) (ω : Ω) :
      MixedPastOmittedMarkFields.leafInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ (p x w) j0 ω=
      e (ω,x+OrderedHeatForests.values (fun _ : Fin 1=>(0:HeatCircle)) k w ind) := by
    have hl:=FixedHistoryTimeFactors.lower_sections Zero (b:ℝ) hT k t x 0 (fun i=>w i+x) (fun _=>0)
    have htleaf : targets Zero k a ind=lower Zero k a j0:=by
      rw [targets,leaf_observation Zero k a j0]
    have hsp:=congrFun (centers_relative Zero hc' k t x w) ind
    have hcc : centers Zero k (p x w) ind=space k (p x w) j0:=by
      rw [centers,leaf_observation Zero k (p x w) j0]
    change centers Zero k (p x w) ind=_ at hsp
    rw [hcc] at hsp
    simp only [MixedPastOmittedMarkFields.leafInput,e,MixedPastDerivativeRMS.field,
      MixedPastJointData.pastU,MixedPastJointData.pastD,age,ind] at *
    rw [hl,hsp,add_comm x,htleaf]
  have hinputSep:=hinput
  dsimp only [p] at hinputSep
  have hboth : ∀ᵐ x : HeatCircle ∂haarAddCircle,∀ᵐ w : Fin k→HeatCircle ∂Measure.pi (fun _=>haarAddCircle),
      Integrable (fun ω=>|G ((ω,x),w)|^2) μ ∧
      (∫ ω,|G ((ω,x),w)|^2 ∂μ)≤(C*(scale*sharp)^2)*
        (OrderedHeatForests.parentDensity 2 (by norm_num) k tt hord
          (OrderedHeatForests.values (fun _ : Fin 1=>(0:HeatCircle)) k w)*
          ScalarFibreRMS.rms μ e (x+OrderedHeatForests.values (fun _ : Fin 1=>(0:HeatCircle)) k w ind))^2 := by
    filter_upwards [ht,htranslated] with x hx hxi
    filter_upwards [hx,hxi] with w hw hwi
    have hp' : StrictHistory Zero k (p x w):=(FixedHistoryTimeFactors.strict_sections Zero (b:ℝ) hT k t x 0 _ _).mpr hp
    have hs' : SmallHistory Zero (uniformHorizon 1) k (p x w):=
      (small_history_sections Zero (b:ℝ) hT A hA' (uniformHorizon 1) k t x 0 _ _).mpr hs
    have hq' : (q:ℝ)<(carrier Zero k).terminal (p x w):=by
      simpa only [p,a,ActualMeanKernel.terminal_separated Zero (b:ℝ) hT] using hqt
    have hI : Integrable (fun ω=>|MixedPastOmittedMarkFields.leafInput
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ (p x w) j0 ω|^2) μ:=by
      simpa only [hinput] using hwi
    have hh:=hw q hvq hqH hq' hp' hs' θ hθ A0 ν hA0 hν
      (fun j hj z=>by simpa only [root_separated] using hjet x j hj z) j0 B0 hBDG hI
    have hl:=FixedHistoryTimeFactors.lower_sections Zero (b:ℝ) hT k t x 0 (fun i=>w i+x) (fun _=>0)
    have hu:=FixedHistoryTimeFactors.upper_sections Zero (b:ℝ) hT k t x 0 (fun i=>w i+x) (fun _=>0)
    have hta:=FixedHistoryTimeFactors.targets_sections Zero (b:ℝ) hT (fun _=>A) hA' k t x 0 (fun i=>w i+x) (fun _=>0)
    have hwgt:=FixedHistoryTimeFactors.timeWeight_sections Zero (b:ℝ) hT (fraction P*P.lower) (uniformConstant 1)
      k t x 0 (fun i=>w i+x) (fun _=>0)
    have hpar:=parent_density_relative Zero (b:ℝ) hT 2 (by norm_num) A hA' hc' k t x w
      (carrier_orderedTimes Zero hages k (p x w) hp')
    refine ⟨hh.1,?_⟩
    have hrms:=ScalarFibreRMS.sq μ e (x+OrderedHeatForests.values (fun _ : Fin 1=>(0:HeatCircle)) k w ind)
    rw [hpar] at hh
    simp only [hl,hu,hta,hwgt,hinputSep] at hh
    have hhr : (∫ ω,|G ((ω,x),w)|^2 ∂μ)≤C*(scale*sharp*
        OrderedHeatForests.parentDensity 2 (by norm_num) k tt hord
          (OrderedHeatForests.values (fun _ : Fin 1=>(0:HeatCircle)) k w))^2*
        (∫ ω,|e (ω,x+OrderedHeatForests.values (fun _ : Fin 1=>(0:HeatCircle)) k w ind)|^2 ∂μ) := by
      convert! hh.2 using 1 <;> dsimp only [C,scale,sharp,tt,G,relativeLeaf,p] <;> ring
    calc
      _≤_:=hhr
      _=_:=by rw [←hrms];ring
  exact ForestLeafMarkEnergy.leaf_mark_energy μ 2 (by norm_num) tt hord (fun _ : Fin 1=>(0:HeatCircle)) ind
    e hem hei G hm (C*(scale*sharp)^2) (mul_nonneg (MixedPastOmittedWord.momentConstant_nonneg _ _ _ _ _ _) (sq_nonneg _))
    (hboth.mono (fun x hx=>hx.mono (fun w hw=>hw.1)))
    (hboth.mono (fun x hx=>hx.mono (fun w hw=>hw.2)))

end SHE.MixedPastOmittedLeafSpatial
