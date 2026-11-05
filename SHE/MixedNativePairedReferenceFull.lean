module

public import SHE.MixedNativePairedReferenceCompleted
public import SHE.MixedNativePairedReferenceInitial
public import SHE.NativeOutputTimePatch
public import SHE.ControlledScalarReference
public import SHE.MixedNativeReferenceEnergyClock
public import SHE.PastReferenceBandConstants
public import SHE.MixedNativePairedReferenceOutput
public import SHE.MixedNativePairedReferenceEnergy
public import SHE.PastReferenceBandFrequency
public import SHE.PastReferenceEnergy
public import SHE.MixedNativePairedReferenceHilbert
public import SHE.PastReferenceComparisonSection
public import SHE.PastReferenceMeanTheta
public import SHE.PastReferenceThreeLeg
public import SHE.PastReferenceMeanRealization
public import SHE.PastReferenceCovarianceSection
public import SHE.PastReferenceBaselineSection
public import SHE.NegativeThreeLeg
public import SHE.MixedPastMeanRootL1
public import SHE.MovingRootThreeLeg
public import SHE.MovingMeanRootRealization
public import SHE.MovingCovarianceRootSections
public import SHE.MovingBaselineRootSections
public import SHE.MixedPastMeanThetaFourier
public import SHE.MovingMeanThetaEnergy
public import SHE.MovingMeanSectionEnergy
public import SHE.MeanThetaAverage
public import SHE.MovingMeanCost

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MixedNativePairedReferenceFull
open Real
open AddCircle
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingComparisonSection_realSigma : MeasurableSpace RealL2 := borel _
local instance movingComparisonSection_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingComparisonSection_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingComparisonSection_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingComparisonSection_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingComparisonSection_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingComparisonSection_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingComparisonSection_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingComparisonSection_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingComparisonSection_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
variable {W : Type} [MeasurableSpace W]



open Set CutoffWordLevel CutoffWordHistories ControlledProfile SmoothCylinders UniformSmooth
  PhysicalScoreChain ControlledOldIntervals
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (h : ℝ≥0) (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "AA"=>ControlledMeanOldAverageShift.absoluteAt P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "ZT" v=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v=>ControlledWordTimeShift.translatedStops h Z hstop v



local notation "Val"=>MovingMeanSectionEnergy.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

local notation "Avg"=>MovingMeanThetaEnergy.thetaValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

local notation "CT"=>MovingMarkRootTheta.covarianceTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "BT"=>MovingMarkRootTheta.baselineTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm

def endpointDifference (k : ℕ) (v s : ℝ≥0) (z : Ω×HeatCircle) : ℝ:=
  MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k 1 (v+s) z-
  MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k 0 (v+s) z

local notation "End"=>endpointDifference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))
variable (hrootStop:∀x i,(Z.observations x i).stop≤(h:ℝ))
variable (hrootTarget:∀x i,(Z.observations x i).target=(h:ℝ))
local notation "RS" v=>(fun x=>by
  change (Z.observations x 0).stop+(v:ℝ)=((v+h:ℝ≥0):ℝ)
  rw [le_antisymm (hrootStop x 0) (hstop x 0),NNReal.coe_add,add_comm])
local notation "RT" v=>(fun x=>by
  change (Z.observations x 0).target+(v:ℝ)=((v+h:ℝ≥0):ℝ)
  rw [hrootTarget x 0,NNReal.coe_add,add_comm])
variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
local notation "Ref"=>MixedNativePairedReferenceEnergy.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P h Z hstop F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget hL hρ
local notation "Output"=>MixedNativePairedReferenceOutput.output
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hL hρ
local notation "En"=>MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local instance referenceFull_second:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology

def initial(k:ℕ)(z:ℝ≥0×Ω):CircleL2:=
  MixedNativePairedReferenceEnergy.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P z.1 (ControlledScalarReference.observations z.1) (fun _ _=>le_rfl) F hF hFm
    J hIJ₀ hIJ₁ hnull hJ hAs (fun _ _=>le_rfl) (fun _ _=>rfl) hL hρ k (0,z.2)
local notation "Initial"=>initial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P F hF hFm
  J hIJ₀ hIJ₁ hnull hJ hAs hL hρ

def field(k:ℕ):ℝ≥0×Ω→CircleL2:=NativeOutputTimePatch.field h (fun _=>0) (Output k)
local notation "Field"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm hL hρ

def literal(k:ℕ):ℝ≥0×Ω→CircleL2:=NativeOutputTimePatch.field h (Initial k) (Ref k)
local notation "Literal"=>literal 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P h Z hstop F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget hL hρ

include haP htarget hstop hnull hJ hAs hL hIJ₀ hIJ₁ hrootStop hrootTarget in
/-- True common initial data makes the paired reference vanish on the
whole initial output triangle. No common sample event over all times
is asserted or needed. -/
theorem initial_zero 
(hA:P.coefficient=(fun z=>κ+aV z))(hlocal:StandardTerminalPastLocality J)
    (hH:(H:ℝ)≤1)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hcenter:∀x,(Z.observations x 0).center=x)
    (hspan:(h:ℝ)≤P.horizon)(k:ℕ)
    (hfresh:(h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold:∀j,j<k→(h:ℝ)≤PhysicalScoreChain.uniformHorizon 1 j)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (χ:ℝ)(hχpos:0<χ)(hχ1:χ<1)(p:ℕ)(hp:0<p)(horder:1≤(p:ℝ)*(1-χ))
    (Bpast Babs B0:ℝ≥0)(hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs:StandardTerminalBDGPower (k+2) J Babs)
    (hBDG:StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (hρpos:0<ρ)(hρhalf:ρ<1/2)
    (ε:ℝ)(hε:0≤ε)(hεhalf:ε<1/2)
    (hhH:h≤H)(hh:0<h):
    ∀ᵐt∂timeMeasure h,∀ᵐω∂μ,Initial k (t,ω)=0:=by
  have he:∀ᵐt:ℝ∂volume.restrict (Ioc (0:ℝ) (h:ℝ)),
      ∀ᵐω∂μ,Initial k (t.toNNReal,ω)=0:=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht':(t.toNNReal:ℝ)=t:=Real.coe_toNNReal _ ht.1.le
    have hth:t.toNNReal≤h:=NNReal.coe_le_coe.mp (by simpa only [ht'] using ht.2)
    have ht0:0<t.toNNReal:=Real.toNNReal_pos.mpr ht.1
    have hth':(t.toNNReal:ℝ)≤(h:ℝ):=by exact_mod_cast hth
    exact MixedNativePairedReferenceInitial.reference_zero
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP t.toNNReal
      (ControlledScalarReference.observations t.toNNReal) (fun _ _=>le_rfl) (fun _ _=>le_rfl)
      F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs (fun _ _=>le_rfl) (fun _ _=>rfl) hL hρ
      hA hlocal hH hsmallPoint hsmallL2 (fun _ _=>le_rfl) (fun _=>rfl)
      (hth'.trans hspan) k (hth'.trans hfresh) (fun j hj=>hth'.trans (hold j hj))
      A0 ν hA0 hν hjet χ hχpos hχ1 p hp horder Bpast Babs B0 hBDGpast hBDGabs hBDG
      hρpos hρhalf ε hε hεhalf (hth.trans hhH) ht0
  simpa only [Real.toNNReal_coe] using (timeMeasurePreserving h).quasiMeasurePreserving.ae he

include haP htarget hnull hJ hAs hL hIJ₀ hIJ₁ hrootStop hrootTarget in
/-- The paired reference is a genuine Borel native Hilbert field on
all original output times. Its initial strip is identified from common
initial data, and its completed windows carry the sharp band rates. -/
theorem actual_full 

(hA:P.coefficient=(fun z=>κ+aV z))(hlocal:StandardTerminalPastLocality J)
    (hH:(H:ℝ)≤1)
    (hsmallPoint:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hcenter:∀x,(Z.observations x 0).center=x)
    (hspan:(h:ℝ)≤P.horizon)(k:ℕ)
    (hfresh:(h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold:∀j,j<k→(h:ℝ)≤PhysicalScoreChain.uniformHorizon 1 j)
    (A ν:ℝ)(hAmp:0≤A)(hν:1≤ν)
    (hjet:∀x j,j≤k→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤(A*ν^(-P.exponent))*ν^j)
    (χ:ℝ)(hχpos:0<χ)(hχ1:χ<1)(p:ℕ)(hp:0<p)(horder:1≤(p:ℝ)*(1-χ))
    (Bpast Babs B0:ℝ≥0)(hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs:StandardTerminalBDGPower (k+2) J Babs)
    (hBDG:StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (hρpos:0<ρ)(hρhalf:ρ<1/2)
    (ε:ℝ)(hε:0≤ε)(hεhalf:ε<1/2)
    (hhH:h≤H)(hh:0<h)
    (hwindow:(h:ℝ)=NativeBandFrequencyRates.window P.exponent ν)(η:ℝ)(hη:0<η):
    let Ccov:=PastReferenceBandConstants.covariance P κ M k Babs η
    let Cbase:=PastReferenceBandConstants.baseline P κ M k Babs η
    let Cmean:=PastReferenceBandConstants.mean P κ M k p B0 ρ χ ε η
    let L:=3*A^2*(2:ℝ)^(2*η)*Λ^(-ρ)*
      (Ccov*ν^(-PastReferenceBandFrequency.covarianceDegree P.exponent k η)+
        Cbase*ν^(-PastReferenceBandFrequency.baselineDegree P.exponent k η))
    let R:=3*A^2*(2:ℝ)^(2*η)*Λ^(-2*ε)*Cmean*
      ν^(-PastReferenceBandFrequency.meanDegree P.exponent ρ ε k η)
    Measurable (Field k) ∧
      (∀ᵐt∂timeMeasure H,∀ᵐω∂μ,Field k (t,ω)=Literal k (t,ω)) ∧
      Integrable (fun z=>‖Field k z‖^2) (energyMeasure μ H) ∧
      (∫⁻z,ENNReal.ofReal (‖Field k z‖^2) ∂energyMeasure μ H)≤
      ENNReal.ofReal L*ENNReal.ofReal Global+
        ENNReal.ofReal R*((ENNReal.ofReal Global)^χ*(ENNReal.ofReal (H:ℝ))^(1-χ)):=by
  intro Ccov Cbase Cmean L R
  have hOut:=MixedNativePairedReferenceOutput.output_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
    hL hρ hsmallPoint k
  have hFm':Measurable (Field k):=NativeOutputTimePatch.measurable h (fun _=>0) (Output k) measurable_const hOut
  have hI:∀ᵐt∂timeMeasure h,∀ᵐω∂μ,(0:CircleL2)=Initial k (t,ω):=by
    have hi:=initial_zero 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h
      Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget hL hρ
      hA hlocal hH hsmallPoint hsmallL2 hages hcenter hspan k hfresh hold
      (A*ν^(-P.exponent)) ν (mul_nonneg hAmp (Real.rpow_nonneg (zero_le_one.trans hν) _))
      (zero_le_one.trans hν) hjet χ hχpos hχ1 p hp horder Bpast Babs B0
      hBDGpast hBDGabs hBDG hρpos hρhalf ε hε hεhalf hhH hh
    exact hi.mono (fun _ ht=>ht.mono (fun _ hω=>hω.symm))
  have hM:∀ᵐv∂timeMeasure (H-h),∀ᵐω∂μ,Output k (v,ω)=Ref k (v,ω):=by
    have he:∀ᵐv:ℝ∂volume.restrict (Ioc (0:ℝ) ((H-h:ℝ≥0):ℝ)),
        ∀ᵐω∂μ,Output k (v.toNNReal,ω)=Ref k (v.toNNReal,ω):=by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      have hv':(v.toNNReal:ℝ)=v:=Real.coe_toNNReal _ hv.1.le
      have hvh:v.toNNReal+h≤H:=by
        apply NNReal.coe_le_coe.mp
        rw [NNReal.coe_add,hv']
        have hvh:=hv.2
        rw [NNReal.coe_sub hhH] at hvh
        linarith
      exact MixedNativePairedReferenceOutput.output_eq
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
        J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget hL hρ hA hlocal hH hsmallPoint hsmallL2
        hages hcenter hspan k hfresh hold (A*ν^(-P.exponent)) ν
        (mul_nonneg hAmp (Real.rpow_nonneg (zero_le_one.trans hν) _)) (zero_le_one.trans hν) hjet
        Bpast Babs hBDGpast hBDGabs v.toNNReal hvh hh
    simpa only [Real.toNNReal_coe] using (timeMeasurePreserving (H-h)).quasiMeasurePreserving.ae he
  have hEq:=NativeOutputTimePatch.congr_sections μ H h hhH (fun _=>0) (Output k) (Initial k) (Ref k) hI hM
  have hc:=MixedNativePairedReferenceCompleted.completed_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
    J hIJ₀ hIJ₁ hnull hJ hAs hrootStop hrootTarget hL hρ hA hlocal hH hsmallPoint hsmallL2
    hages hcenter hspan k hfresh hold A ν hAmp hν hjet χ hχpos.le hχ1 p hp horder
    Bpast Babs B0 hBDGpast hBDGabs hBDG hρpos hρhalf ε hε hεhalf hhH hh hwindow η hη
  have hmass:(∫⁻z,ENNReal.ofReal (‖Field k z‖^2) ∂energyMeasure μ H)=
      (∫⁻z,ENNReal.ofReal (‖Output k z‖^2) ∂energyMeasure μ (H-h)):=by
    rw [field,NativeOutputTimePatch.mass μ H h hhH (fun _=>0) (Output k) measurable_const hOut]
    simp only [norm_zero,zero_pow (by norm_num:(2:ℕ)≠0),ENNReal.ofReal_zero,lintegral_zero,zero_add]
  have hb:(∫⁻z,ENNReal.ofReal (‖Field k z‖^2) ∂energyMeasure μ H)≤
      ENNReal.ofReal L*ENNReal.ofReal Global+
        ENNReal.ofReal R*((ENNReal.ofReal Global)^χ*(ENNReal.ofReal (H:ℝ))^(1-χ)):=hmass.trans_le hc
  have hpowG:ENNReal.ofReal Global^χ≠∞:=ENNReal.rpow_ne_top_of_nonneg hχpos.le ENNReal.ofReal_ne_top
  have hpowH:ENNReal.ofReal (H:ℝ)^(1-χ)≠∞:=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
  have hcap:ENNReal.ofReal L*ENNReal.ofReal Global+
      ENNReal.ofReal R*((ENNReal.ofReal Global)^χ*(ENNReal.ofReal (H:ℝ))^(1-χ))≠∞:=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hpowG hpowH)⟩
  have hi:Integrable (fun z=>‖Field k z‖^2) (energyMeasure μ H):=by
    refine ⟨(hFm'.norm.pow_const 2).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _))]
    exact lt_of_le_of_lt hb (lt_top_iff_ne_top.mpr hcap)
  exact ⟨hFm',hEq,hi,hb⟩

end SHE.MixedNativePairedReferenceFull
