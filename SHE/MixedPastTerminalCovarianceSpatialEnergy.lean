module

public import SHE.MixedPastTerminalCovarianceHistory
public import SHE.ControlledTerminalCovarianceSections
public import SHE.MixedPastTerminalCovarianceRelativeMass
public import SHE.RandomScoreSpatialAverage
public import SHE.RandomScoreSpatialAbsolute
public import SHE.ParentScoreInput
public import SHE.MixedPastFiniteTerminalMass

public import SHE.MixedPastCovariancePointMoments
public import SHE.MixedPastScoreEnergy
public import SHE.RandomFutureCenters
public import SHE.PastMeanSections
public import SHE.QuarterSpatialEvent
public import SHE.PastCovarianceMassSections

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastTerminalCovarianceSpatialEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovarianceSpatialFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovarianceSpatialFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovarianceSpatialFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovarianceSpatialFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastCovarianceSpatialFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovarianceSpatialFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

open ScalarRootRelativeGeometry ControlledResidualScoreInput MeasurableGaussianScores
  ProfileStability QuarterSpatialEvent OrderedHeatForests
local notation "Actual" => MixedPastLiteralCovariance.actualPoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "G"=>MixedPastTerminalCovarianceFields.active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "MActual"=>MixedPastTerminalCovarianceFields.mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "Point"=>MixedPastTerminalCovarianceSpatialFields.relativePoint
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Mass"=>MixedPastFiniteTerminalMass.scoreMass
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "TA"=>ControlledTerminalCovarianceSections.timeAmplitude
  P haP Λ v b hvb Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
/-- Actual terminal covariance old-space averaging has the TRUE past
energy to beta. The original positive parent forest is averaged before
squaring; its only cost is the finite original forest count. -/
theorem actual_spatial_energy_ae
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ)
    (hsmallL2:memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hv1:(v:ℝ)≤1) (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 1 J Bpast)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootstop:∀x i,(Z.observations x i).stop=(b:ℝ))
    (hrootage:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon) (hbH:b≤H) (k:ℕ)
    (hsmall:∀j,j<k+1→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    {ζ:ℝ} (hζ:0≤ζ) (hζ1:ζ≤1) {A0 ν:ℝ} (hA0:0≤A0) (hν:0≤ν)
    (hjet:∀x j,j≤k+1→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (B0:ℝ≥0) (hBDG:StandardTerminalBDGPower (k+3) J B0):
    ∀ᵐ t:Fin (k+1)→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
    ∀hp:StrictHistory Zero (k+1) (anchor (k+1) t),
    let CC:=MixedPastWordMoments.momentConstant P (k+1) (k+1) 1
      (((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (k+3) B0 κ M)^P.exponent)
    let Cm:=2*P.holder*(3*(((1+k:ℕ):ℝ)/(P.lower/2)))
    let EE:=(∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ)^P.exponent
    Integrable (Point k ζ t) ((μ.prod haarAddCircle).prod (Measure.pi (fun _:Fin (k+1)=>haarAddCircle))) ∧
      Integrable (fun y=>|∫w,Point k ζ t (y,w) ∂Measure.pi (fun _:Fin (k+1)=>haarAddCircle)|^2)
        (μ.prod haarAddCircle) ∧
      (∫y,|∫w,Point k ζ t (y,w) ∂Measure.pi (fun _:Fin (k+1)=>haarAddCircle)|^2 ∂μ.prod haarAddCircle)≤
        CC*Cm^2*EE*(TA (k+1) t A0 ν*(Fintype.card (Choices 1 (k+1)):ℝ))^2 ∧
      (∫z,|Point k ζ t z| ∂(μ.prod haarAddCircle).prod
        (Measure.pi (fun _:Fin (k+1)=>haarAddCircle)))≤
        Real.sqrt (CC*Cm^2*EE)*TA (k+1) t A0 ν*(Fintype.card (Choices 1 (k+1)):ℝ):=by
  have hm:=MixedPastTerminalCovarianceHistory.actual_second_moment_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hages
    (fun x i=>(hrootstop x i).le) (fun x i=>(hrootage x i).le)
    hspan hbH haarAddCircle k hsmall hζ hζ1 hA0 hν hjet B0 hBDG
  have hsect:=HistoryProductMeasure.ae_relative_old_first
    (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) (k+1) hm
  have hrel:=MixedPastTerminalCovarianceRelativeMass.mass_relative_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hages hrootstop hrootage hcenter k
  filter_upwards [hsect,hrel] with t ht htr
  intro hp CC Cm EE
  let a:=anchor (k+1) t
  let K:(Fin (k+1)→HeatCircle)→ℝ:=fun w=>parentDensity 2 (by norm_num) (k+1)
    (targets Zero (k+1) a) (carrier_orderedTimes Zero hages (k+1) a hp)
    (values (fun _:Fin 1=>(0:HeatCircle)) (k+1) w)
  have hKc:Continuous K:=(ForestedScoreInput.parentDensity_continuous 2 (by norm_num) (k+1) _ _).comp
    (values_continuous (fun _:Fin 1=>(0:HeatCircle)) (k+1))
  have hKi:Integrable K (Measure.pi (fun _:Fin (k+1)=>haarAddCircle)):=
    hKc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hK(w):0≤K w:=parentDensity_nonneg 2 (by norm_num) (k+1) _ _ _
  have hCC:0≤CC:=MixedPastWordMoments.momentConstant_nonneg P (k+1) (k+1) 1 _
  have hEE:0≤EE:=Real.rpow_nonneg (integral_nonneg (fun _=>sq_nonneg _)) _
  have hFM:=MixedPastTerminalCovarianceSpatialFields.relativePoint_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k ζ t
  have hMM:=MixedPastFiniteTerminalMass.scoreMass_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k ζ t
  have hMass:∀ᵐw ∂Measure.pi (fun _:Fin (k+1)=>haarAddCircle),
      Integrable (fun y:Ω×HeatCircle=>|Mass k ζ t (y,w)|^2) (μ.prod haarAddCircle) ∧
      (∫y:Ω×HeatCircle,|Mass k ζ t (y,w)|^2 ∂μ.prod haarAddCircle)≤Cm^2*EE:=by
    apply ae_of_all
    exact MixedPastFiniteTerminalMass.actual_mass_energy
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
      hΛ hsmallL2 (hvb.trans hbH) hv1 Bpast hBDGpast hages hspan k t hp hζ hζ1
  have hPoint:∀ᵐw ∂Measure.pi (fun _:Fin (k+1)=>haarAddCircle),∀ᵐx ∂haarAddCircle,
      Integrable (fun ω=>|Mass k ζ t ((ω,x),w)|^2) μ→
      Integrable (fun ω=>|Point k ζ t ((ω,x),w)|^2) μ ∧
      (∫ω,|Point k ζ t ((ω,x),w)|^2 ∂μ)≤
        (CC*(TA (k+1) t A0 ν)^2)*(K w)^2*(∫ω,|Mass k ζ t ((ω,x),w)|^2 ∂μ):=by
    filter_upwards [ht,htr] with w hw hwr
    filter_upwards [hw,hwr] with x hx hxr
    intro _
    have hh:=hx
    have heq(ω):MActual (k+1) ζ (separated (k+1) (x,t,fun i=>w i+x)) ω=
        Mass k ζ t ((ω,x),w):=hxr ζ ω
    simp_rw [heq] at hh
    rw [ControlledTerminalCovarianceSections.amplitude_relative
      P haP Λ v b hvb Z htarget hstop F hF hFm hages hrootage hcenter (k+1) t hp x w A0 ν] at hh
    refine ⟨hh.1,?_⟩
    have hb:(∫ω,|Point k ζ t ((ω,x),w)|^2 ∂μ)≤
        CC*(TA (k+1) t A0 ν*K w)^2*(∫ω,(Mass k ζ t ((ω,x),w))^2 ∂μ):=hh.2
    exact hb.trans_eq (by simp only [sq_abs];ring)
  have hCE:0≤Cm^2*EE:=mul_nonneg (sq_nonneg _) hEE
  have hCP:0≤CC*(TA (k+1) t A0 ν)^2:=mul_nonneg hCC (sq_nonneg _)
  have hAbs:=RandomScoreSpatialAbsolute.joint_integrable μ haarAddCircle
    (Measure.pi (fun _:Fin (k+1)=>haarAddCircle)) (Point k ζ t) (Mass k ζ t) hFM hMM
    K hKc.measurable hKi hK hCP hCE hMass hPoint
  have hAvg:=RandomScoreSpatialAverage.average_energy μ haarAddCircle
    (Measure.pi (fun _:Fin (k+1)=>haarAddCircle)) (Point k ζ t) (Mass k ζ t) hFM hMM
    K hKc.measurable hKi hK hCP hCE hMass hPoint
  refine ⟨hAbs.1,hAvg.1,?_,?_⟩
  · have hb:=hAvg.2
    simp only [K,ForestedScoreInput.parentDensity_mass] at hb
    exact hb.trans_eq (by ring)
  · have hTA:0≤TA (k+1) t A0 ν:=by
      unfold ControlledTerminalCovarianceSections.timeAmplitude
      exact div_nonneg (mul_nonneg
        (timeWeight_nonneg Zero (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1)
          (fun j=>(uniformConstant_pos 1 j).le) (k+1) a hp)
        (PastWordTimeFields.total_nonneg Zero P (k+1) a A0 ν)) (by norm_num)
    have hbase:0≤CC*Cm^2*EE:=mul_nonneg (mul_nonneg hCC (sq_nonneg _)) hEE
    have hsqrt:Real.sqrt ((CC*(TA (k+1) t A0 ν)^2)*(Cm^2*EE))=
        Real.sqrt (CC*Cm^2*EE)*TA (k+1) t A0 ν:=by
      rw [show (CC*(TA (k+1) t A0 ν)^2)*(Cm^2*EE)=
        (CC*Cm^2*EE)*(TA (k+1) t A0 ν)^2 by ring,
        Real.sqrt_mul hbase,Real.sqrt_sq_eq_abs,abs_of_nonneg hTA]
    have hb:=hAbs.2
    rw [hsqrt] at hb
    simpa only [K,ForestedScoreInput.parentDensity_mass] using hb

end SHE.MixedPastTerminalCovarianceSpatialEnergy
