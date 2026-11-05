module
public import SHE.MixedFirstDefectNativeBound
public import SHE.MixedFirstDefectEnvelopeIdentity

public import SHE.MixedFirstDefectNormEnvelope
public import SHE.MixedFirstDefectConvolutionTransport
public import SHE.MixedFirstDefectMinkowski
public import SHE.MixedFirstDefectDisintegration
public import SHE.NativeBesselParameterSection
public import SHE.MixedFirstDefectIntegral
public import SHE.MixedJointActiveVolume
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

namespace SHE.MixedFirstDefectActualBound
open Set MeasureTheory Real AddCircle StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
  NativeHeatObservation CutoffWordLevel CutoffWordHistories CutoffCarriers ControlledProfile
  ControlledReferenceLevel PhysicalChainArrays PhysicalParentGeometry PhysicalScoreChain HistoryProductMeasure
  CoveredControlledLaw
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
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (P:CanonicalCovariance.ProfileParameters)(hAs:SmoothCylinders.BoundedSmooth (fun z=>κ+aV z))
variable (θ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformSmooth.UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Z"=>ControlledScalarReference.observations b
local notation "Base"=>ControlledReferenceThetaGeometry.level P (fun z=>κ+aV z) hAs Λ v b hvb Z
  (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "R₀"=>referenceData P (fun z=>κ+aV z) hAs Λ 0 v b hvb (0,0)



local notation "Sp"=>MixedFirstDefectRMS.spatialPoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P hAs θ v b hvb F hF hFm
local notation "PV"=>MixedFirstDefectRMS.pointValue
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs θ v b hvb F hF hFm
local notation "Val"=>MixedFirstDefectRMS.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs θ v b hvb F hF hFm
local notation "Env"=>MixedFirstDefectNormEnvelope.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs v b hvb F hF hFm
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

set_option backward.isDefEq.respectTransparency true in
include hsmall in
/-- The actual complete first-defect mark is bounded by the literal
relative negative-input convolution. Every point/space/time applicability
premise is discharged; the constant is explicitly structural. -/
theorem norm_le (hM:0≤M)(hP:P.coefficient=(fun z=>κ+aV z))
    (ρ:ℝ)(hL:1≤Λ)(hρ:0<ρ)(hρhalf:ρ<1/2)(k:ℕ)
    (hspanP:(b:ℝ)-(v:ℝ)≤P.horizon)
    (hspanAge:(b:ℝ)-(v:ℝ)≤ControlledDefectConstants.horizon P.lower P.lower_pos ell M hell hM ρ hρ hρhalf k)
    (hOld:∀j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (h:ℝ)(hh:0<h)(hspan:(b:ℝ)-(v:ℝ)≤h)(hpos:v<b)(hbH:b≤H)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)
    (hjet:∀x j,j≤k→∀y,‖iteratedFDeriv ℝ j (F x) y‖≤A0*ν^j)(ω:Ω):
    ‖Val ρ hL hρ.le k ω‖≤
      ControlledDefectConstants.constant ell M hell hM ρ hρ hρhalf k P*
        MixedFirstDefectRelativeEnergy.value
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
            (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) h A0 ν k ρ hL hρ.le (b,ω):=by
  obtain ⟨Hs,Cs,hHs,hCs,hHeq,hCeq,hsections⟩:=MixedFirstDefectPointSections.sections_with_constants
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs θ v b hvb F hF hFm hsmall
      hM hP hL hρ hρhalf k
  have hspanHs:(b:ℝ)-(v:ℝ)≤Hs:=by rw [hHeq];exact hspanAge
  have hs:=hsections hspanP hspanHs hOld A0 ν hA0 hν hjet
  have hsec:∀ᵐa:(Fin k→ℝ)×ℝ∂
      (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))).prod volume,
      MemLp (fun x:HeatCircle=>(Sp k a.1 a.2 ω x:ℂ)) 2 haarAddCircle:=
    hs.mono (fun a ha=>(ha ω).1)
  have hb:∀ᵐa:(Fin k→ℝ)×ℝ∂
      (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))).prod volume,
      ‖PV ρ hL hρ.le k a.1 a.2 ω‖≤Cs*Env ρ hL hρ.le k A0 ν ω a:=by
    filter_upwards [hs] with a ha
    have hd:=(ha ω).2
    rw [MixedFirstDefectEnvelopeIdentity.envelope_eq
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs v b hvb F hF hFm
        ρ hL hρ.le k hbH A0 ν ω a] at hd
    exact hd
  have hρ1:ρ≤1:=hρhalf.le.trans (by norm_num)
  have hbnd:=MixedFirstDefectNativeBound.norm_le
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs θ v b hvb F hF hFm hsmall
      ρ hL hρ hρ1 k h hh hspan hpos hbH A0 ν hA0 hν ω Cs hCs.le hsec hb
  simpa only [hCeq] using hbnd

end SHE.MixedFirstDefectActualBound
