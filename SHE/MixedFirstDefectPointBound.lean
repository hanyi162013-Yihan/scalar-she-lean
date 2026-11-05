module

public import SHE.MixedFirstDefectRelativeField
public import SHE.ControlledDefectAgeRMS
public import SHE.ControlledDefectConstants
public import SHE.MixedScalarRelativeDefectTrace
public import SHE.DefectSpatialNativeNorm
public import SHE.ForestTranslation
public import SHE.MixedFirstDefectIntegral
public import SHE.MixedFirstDefectRMS
public import SHE.ControlledReferenceFamilyDefectL1
public import SHE.RootHistoryCurrentMeasure
public import SHE.NativeBesselParameterAverageAE
public import SHE.HistoryMeasureGeometry
public import SHE.MixedCanonicalRootFields
public import SHE.DefectRelativeFactor
public import SHE.DefectCombinedTime
public import SHE.NativeBesselFieldAE
public import SHE.NativeSignedHaarProcess
public import SHE.ControlledScalarReference
public import SHE.ControlledThetaDefectEnvelope
public import SHE.MixedJointUncutDefectTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.MixedFirstDefectPointBound
open Set MeasureTheory Real AddCircle StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
  NativeHeatObservation CutoffWordLevel CutoffWordHistories CutoffCarriers ControlledProfile
  ControlledReferenceLevel PhysicalChainArrays PhysicalParentGeometry PhysicalScoreChain HistoryProductMeasure
  CoveredControlledLaw FiniteHaar JointWordAnalytic ControlledOldIntervals
open scoped NNReal ENNReal BigOperators
open Classical
local instance mixedFirstDefectRMS_period:Fact (0<2*π):=⟨by positivity⟩
local instance mixedFirstDefectRMS_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance mixedFirstDefectRMS_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedFirstDefectRMS_borel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (P:CanonicalCovariance.ProfileParameters)(hAs:SmoothCylinders.BoundedSmooth (fun z=>κ+aV z))
variable (θ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformSmooth.UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Z"=>ControlledScalarReference.observations b
local notation "Base"=>ControlledReferenceThetaGeometry.level P (fun z=>κ+aV z) hAs Λ v b hvb Z
  (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "R₀"=>referenceData P (fun z=>κ+aV z) hAs Λ 0 v b hvb (0,0)


local notation "Pt"=>MixedFirstDefectRMS.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb F hF hFm
local notation "Sp"=>MixedFirstDefectRMS.spatialPoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb F hF hFm
local notation "Field"=>MixedFirstDefectRMS.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb F hF hFm
local notation "past"=>MixedNativeRandomReferenceStep.randomParameter
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)


local notation "Rel"=>MixedFirstDefectRelativeField.relative 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb F hF hFm
local notation "Input"=>MixedFirstDefectRMS.inputEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV"=>MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S

set_option backward.isDefEq.respectTransparency true in
include hsmall in
/-- The literal actual old-space-averaged first-defect point has a
native Hilbert norm bound and a genuine L2 spatial section. The same
old-time event works before ALL current times and native samples. -/
theorem bound_with_constants (hM:0≤M) (hP:P.coefficient=(fun z=>κ+aV z))(hΛ:1≤Λ)
    {ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)(k:ℕ):
    ∃Hs Cs:ℝ,0<Hs ∧ 0<Cs ∧
      Hs=ControlledDefectConstants.horizon P.lower P.lower_pos ell M hell hM ρ hρ hρhalf k ∧
      Cs=ControlledDefectConstants.constant ell M hell hM ρ hρ hρhalf k P ∧
      ∀ᵐt:Fin k→ℝ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) b)),
        let z:=separated k ((0:HeatCircle),t,fun _=>0)
        StrictHistory Zero k z→SmallHistory Zero (uniformHorizon 1) k z→
        (b:ℝ)-(v:ℝ)≤P.horizon→(b:ℝ)-(v:ℝ)≤Hs→
        ∀A0 ν:ℝ,0≤A0→0≤ν→
          (∀x j,j≤k→∀y,‖iteratedFDeriv ℝ j (F x) y‖≤A0*ν^j)→
        ∀q:ℝ,(v:ℝ)≤q→q<(carrier Zero k).terminal z→∀ω:Ω,
          MemLp (fun x:HeatCircle=>(Sp k t q ω x:ℂ)) 2 haarAddCircle ∧
            ‖MixedFirstDefectRMS.pointValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
              P hAs θ v b hvb F hF hFm ρ hΛ hρ.le k t q ω‖≤
              Cs*MixedFirstDefectRMS.oldFactor Λ κ P hAs v b hvb F hF hFm k t A0 ν*
                MixedFirstDefectRMS.pairKernel Λ κ P hAs v b hvb F hF hFm ρ k t q*
                  sqrt (Input ρ hΛ hρ.le q ω):=by
  let Hs:=ControlledDefectConstants.horizon P.lower P.lower_pos ell M hell hM ρ hρ hρhalf k
  let Cs:=ControlledDefectConstants.ageConstant P.lower P.lower_pos ell M hell hM ρ hρ hρhalf k
  have hscores:=Classical.choose_spec (Classical.choose_spec
    (ControlledDefectAgeRMS.rms P.lower P.lower_pos hell hM hρ hρhalf k))
  have hHs:0<Hs:=hscores.1
  have hCs:0<Cs:=hscores.2.1
  have hscore:=hscores.2.2
  let D:=sqrt (TwoFreshBoundedEmptyWord.momentConstant P k k 1)
  let N:ℝ:=Fintype.card (OrderedHeatForests.Choices 1 k)
  let C:=1+Cs*D*N
  have hC:0<C:=by dsimp [C,D,N];positivity
  refine ⟨Hs,C,hHs,hC,rfl,rfl,?_⟩
  have hrun:=hscore P rfl
  rw [hP] at hrun
  have hh:=hrun hAs Λ hΛ v b hvb F hF hFm
  filter_upwards [hh] with t ht
  intro z hp hs hspan hspanH A0 ν hA0 hν hjet q hvq hqt ω
  let Wsp:=Fin k→HeatCircle
  let η:Measure Wsp:=Measure.pi (fun _=>haarAddCircle)
  let ht0:=carrier_orderedTimes Zero (fun _ _=>le_rfl) k z hp
  let Hparent:Wsp→ℝ:=fun w=>OrderedHeatForests.parentDensity 2 (by norm_num) k
    (targets Zero k z) ht0 (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w)
  have hHp:Measurable Hparent:=((OrderedHeatForests.parentDensity_continuous 2 (by norm_num) k _ ht0).comp
    (OrderedHeatForests.values_continuous (fun _:Fin 1=>(0:HeatCircle)) k)).measurable
  have hHpi:Integrable Hparent η:=((OrderedHeatForests.parentDensity_continuous 2 (by norm_num) k _ ht0).comp
    (OrderedHeatForests.values_continuous (fun _:Fin 1=>(0:HeatCircle)) k)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hHp0(w:Wsp):0≤Hparent w:=OrderedHeatForests.parentDensity_nonneg 2 (by norm_num) k _ _ _
  have hmass:(∫w,Hparent w ∂η)=N:=OrderedHeatForests.parentDensity_mass 2 (by norm_num) k _ ht0 _
  let G0:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k z*
    DefectRelativeFactor.total Zero P v k z A0 ν
  let Kq:=MixedFirstDefectRMS.pairKernel Λ κ P hAs v b hvb F hF hFm ρ k t q
  have hG0:0≤G0:=mul_nonneg
    (timeWeight_nonneg Zero (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1)
      (fun j=>(uniformConstant_pos 1 j).le) k z hp)
    (TwoFreshBoundedEmptyWord.total_nonneg P _ _ _ A0 ν)
  have hKq:0≤Kq:=by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact DefectCombinedTime.nonneg (zero_le_one.trans hΛ)
      (sub_nonneg.mpr ((carrier Zero k).targets_after z i))
      (sub_nonneg.mpr ((carrier Zero k).targets_after z j)) (sub_pos.mpr hqt).le
  let L:=Cs*D*G0*sqrt (Input ρ hΛ hρ.le q ω)*Kq
  have hL:0≤L:=by dsimp [L,D];positivity
  have hRel:=MixedFirstDefectRelativeField.measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb F hF hFm hsmall (zero_le_one.trans hΛ) k t q ω
  let p:ℝ×Inputs:=(θ,past ω)
  let c:=ContinuousHeatMild.coefficientFunction haU hell hbU S.first (q.toNNReal,ω)
  let d:=ContinuousHeatMild.coefficientFunction haV hell hbV S.second (q.toNNReal,ω)
  have hInput:StepInput.negativeEnergy 1 Λ ρ (c.1-d.1)=Input ρ hΛ hρ.le q ω:=by
    change _=‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (CircleNormalization.push (d.1-c.1))‖^2
    rw [show d.1-c.1=-(c.1-d.1) by abel,map_neg,map_neg,norm_neg,
      CircleNormalization.push_bessel_energy hΛ hρ.le]
  have hsections:∀ᵐw:Wsp∂η,
      Integrable (fun x:AddCircle (1:ℝ)=>|Rel k t q ω (x,w)|^2) haarAddCircle ∧
        Λ^(-ρ/2)*sqrt (∫x:AddCircle (1:ℝ),|Rel k t q ω (x,w)|^2 ∂haarAddCircle)≤L*Hparent w:=by
    filter_upwards [ht] with w hw
    let hx:=fun x:AddCircle (1:ℝ)=>separated k (CircleNormalization.scale 1 (2*π) x,t,
      fun i=>w i+CircleNormalization.scale 1 (2*π) x)
    let meanw:=fun x:AddCircle (1:ℝ)=>state (carrier (Base p) k) Λ
      (dU).physicalState (dV).physicalState (dU).physicalField (dV).physicalField (hx x) ω q
    let J:=fun x:AddCircle (1:ℝ)=>Rel k t q ω (x,w)
    have hJ:Measurable J:=hRel.comp (measurable_id.prodMk measurable_const)
    let Bh:=fun x:AddCircle (1:ℝ)=>GaussianTaylor.hessian (GaussianConvolution.gaussianAverage
      (WordRecursion.covariance (referenceData P (fun z=>κ+aV z) hAs Λ p.1 v b hvb p.2).reference
        ((carrier (Base p) k).observations.observations (hx x)) q ((carrier (Base p) k).terminal (hx x)))
        (UncutSmoothWords.test (Base p) k (hx x))) (meanw x)
    let ar:=fun x:AddCircle (1:ℝ)=>fun i=>(CircleNormalization.scale 1 (2*π)).symm
      (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w i)+x
    let Dh:=fun x:AddCircle (1:ℝ)=>NativeClippedHaarDirection.column hell c d
      (fun i=>stops Zero k z i-(v:ℝ)) (fun i=>targets Zero k z i-(v:ℝ)) (ar x) (q-(v:ℝ)) Λ
    let Wh:=fun x:AddCircle (1:ℝ)=>CommonHaarDefectTrace.direction
      (fun i=>NativeObservationCovariance.row hell d (targets Zero k z i-(v:ℝ)) (q-(v:ℝ))
        (StoppedGaussianScore.nativeCenter (ar x) i))
    have hObs:=ControlledReferenceThetaGeometry.carrier_observations_eq P (fun z=>κ+aV z) hAs Λ v b hvb Z
      (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm p (0,(0,0)) k z
    have hStops:stops (Base p) k z=stops Zero k z:=by
      unfold stops
      rw [hObs]
      rfl
    have hTargets:targets (Base p) k z=targets Zero k z:=by unfold targets;rw [hObs]
    have he:∀ᵐx:AddCircle (1:ℝ)∂haarAddCircle,
        J x=(1/2:ℝ)*(∑'l:HaarNode,(Bh x (Dh x l) (Wh x l)+Bh x (Wh x l) (Dh x l)+Bh x (Dh x l) (Dh x l))):=by
      apply ae_of_all
      intro x
      have hterm:(carrier (Base p) k).terminal (hx x)=(carrier Zero k).terminal z:=by
        rw [ControlledReferenceThetaGeometry.carrier_terminal_eq P (fun z=>κ+aV z) hAs Λ v b hvb Z
          (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm p (0,(0,0)) k (hx x)]
        change (carrier Zero k).terminal (separated k
          (CircleNormalization.scale 1 (2*π) x,t,fun i=>w i+CircleNormalization.scale 1 (2*π) x))=
          (carrier Zero k).terminal (separated k ((0:HeatCircle),t,fun _=>0))
        rw [ActualMeanKernel.terminal_separated Zero (b:ℝ) (fun _=>rfl),
          ActualMeanKernel.terminal_separated Zero (b:ℝ) (fun _=>rfl)]
      have hguard:(v:ℝ)≤q ∧ q≤(carrier (Base p) k).terminal (hx x):=
        ⟨hvq,hqt.le.trans_eq hterm.symm⟩
      have htrace:=MixedScalarRelativeDefectTrace.point_trace
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) (b:ℝ) (fun _=>rfl)
          (fun _ _=>⟨rfl,rfl,rfl⟩) k t w x (v:ℝ) q ((NNReal.coe_nonneg v).trans hvq) ω
      have hs0:stops (Base p) k (separated k ((0:HeatCircle),t,fun _=>0))=
          stops Zero k (separated k ((0:HeatCircle),t,fun _=>0)):=hStops
      have ht0':targets (Base p) k (separated k ((0:HeatCircle),t,fun _=>0))=
          targets Zero k (separated k ((0:HeatCircle),t,fun _=>0)):=hTargets
      have hh':MixedJointUncutDefectTrace.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          (Base p) k (hx x) ω q=(1/2:ℝ)*(∑'l:HaarNode,
            (Bh x (Dh x l) (Wh x l)+Bh x (Wh x l) (Dh x l)+Bh x (Dh x l) (Dh x l))):=by
        simpa only [hs0,ht0'] using htrace.2
      change (if (v:ℝ)≤q ∧ q≤(carrier (Base p) k).terminal (hx x) then
        MixedJointUncutDefectTrace.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          (Base p) k (hx x) ω q else 0)=_
      rw [if_pos hguard]
      exact hh'
    have hb:=hw p q hvq hqt hp hs hspan hspanH meanw c d A0 ν hA0 hν
      (fun x j hj y=>hjet _ j hj y) J hJ he
    refine ⟨hb.1,?_⟩
    rw [hInput] at hb
    have hb':Λ^(-ρ/2)*sqrt (∫x:AddCircle (1:ℝ),|J x|^2 ∂haarAddCircle)≤
        Cs*(D*(G0*Hparent w))*sqrt (Input ρ hΛ hρ.le q ω)*Kq:=hb.2
    exact hb'.trans_eq (by dsimp only [L];ring)
  have hAmap:Measurable (fun z:Ω×HeatCircle=>((t,q),z)):=measurable_const.prodMk measurable_id
  have hsp0:=MixedFirstDefectIntegral.spatial_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb F hF hFm hsmall (zero_le_one.trans hΛ) k
  have hsp1:=hsp0.comp hAmap
  have hSp:Measurable (fun z:Ω×HeatCircle=>Sp k t q z.1 z.2):=hsp1
  have hN:=DefectSpatialNativeNorm.norm_le η Λ ρ hΛ hρ.le (Rel k t q ω) hRel
    Hparent hHp hHpi hHp0 (fun z:Ω×HeatCircle=>Sp k t q z.1 z.2) hSp ω
    (ae_of_all _ (fun x=>MixedFirstDefectRelativeField.average
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb F hF hFm k t q ω x))
    hL (hsections.mono (fun _ h=>h.1)) (hsections.mono (fun _ h=>h.2))
  refine ⟨hN.1,?_⟩
  rw [hmass] at hN
  have hcoeff:Cs*D*N≤C:=by dsimp only [C];linarith only
  have hc:=mul_le_mul_of_nonneg_right hcoeff
    (mul_nonneg (mul_nonneg hG0 hKq) (sqrt_nonneg (Input ρ hΛ hρ.le q ω)))
  have hOld:G0=MixedFirstDefectRMS.oldFactor Λ κ P hAs v b hvb F hF hFm k t A0 ν:=rfl
  change _≤C*MixedFirstDefectRMS.oldFactor Λ κ P hAs v b hvb F hF hFm k t A0 ν*Kq*
    sqrt (Input ρ hΛ hρ.le q ω)
  rw [←hOld]
  calc
    _≤L*N:=hN.2
    _=(Cs*D*N)*(G0*Kq*sqrt (Input ρ hΛ hρ.le q ω)):=by dsimp only [L];ring
    _≤C*(G0*Kq*sqrt (Input ρ hΛ hρ.le q ω)):=hc
    _=C*G0*Kq*sqrt (Input ρ hΛ hρ.le q ω):=by ring

set_option backward.isDefEq.respectTransparency true in
include hsmall in
/-- The literal actual old-space-averaged first-defect point has a
native Hilbert norm bound and a genuine L2 spatial section. The same
old-time event works before ALL current times and native samples. -/
theorem bound (hP:P.coefficient=(fun z=>κ+aV z))(hΛ:1≤Λ)
    {ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)(k:ℕ):
    ∃Hs Cs:ℝ,0<Hs ∧ 0<Cs ∧
      ∀ᵐt:Fin k→ℝ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) b)),
        let z:=separated k ((0:HeatCircle),t,fun _=>0)
        StrictHistory Zero k z→SmallHistory Zero (uniformHorizon 1) k z→
        (b:ℝ)-(v:ℝ)≤P.horizon→(b:ℝ)-(v:ℝ)≤Hs→
        ∀A0 ν:ℝ,0≤A0→0≤ν→
          (∀x j,j≤k→∀y,‖iteratedFDeriv ℝ j (F x) y‖≤A0*ν^j)→
        ∀q:ℝ,(v:ℝ)≤q→q<(carrier Zero k).terminal z→∀ω:Ω,
          MemLp (fun x:HeatCircle=>(Sp k t q ω x:ℂ)) 2 haarAddCircle ∧
            ‖MixedFirstDefectRMS.pointValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
              P hAs θ v b hvb F hF hFm ρ hΛ hρ.le k t q ω‖≤
              Cs*MixedFirstDefectRMS.oldFactor Λ κ P hAs v b hvb F hF hFm k t A0 ν*
                MixedFirstDefectRMS.pairKernel Λ κ P hAs v b hvb F hF hFm ρ k t q*
                  sqrt (Input ρ hΛ hρ.le q ω):=by
  have hM:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  obtain ⟨Hs,Cs,hHs,hCs,_,_,hb⟩:=bound_with_constants
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb F hF hFm hsmall
      hM hP hΛ hρ hρhalf k
  exact ⟨Hs,Cs,hHs,hCs,hb⟩

end SHE.MixedFirstDefectPointBound
