module

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

namespace SHE.MixedFirstDefectNativeBound
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

include hsmall in
/-- Native averaging and honest time convolution preserve the sharp
actual negative-input RMS, before its square is taken. The pointwise
hypotheses here are supplied by the all-age spatial trace estimate. -/
theorem norm_le (ρ:ℝ)(hL:1≤Λ)(hρ:0<ρ)(hρ1:ρ≤1)(k:ℕ)
    (h:ℝ)(hh:0<h)(hspan:(b:ℝ)-(v:ℝ)≤h)(hpos:v<b)(hbH:b≤H)
    (A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)(ω:Ω)(Cs:ℝ)(hCs:0≤Cs)
    (hsec:∀ᵐa:(Fin k→ℝ)×ℝ∂
      (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))).prod volume,
      MemLp (fun x:HeatCircle=>(Sp k a.1 a.2 ω x:ℂ)) 2 haarAddCircle)
    (hb:∀ᵐa:(Fin k→ℝ)×ℝ∂
      (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))).prod volume,
      ‖PV ρ hL hρ.le k a.1 a.2 ω‖≤Cs*Env ρ hL hρ.le k A0 ν ω a):
    ‖Val ρ hL hρ.le k ω‖≤Cs*MixedFirstDefectRelativeEnergy.value
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P
      (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1) h A0 ν k ρ hL hρ.le (b,ω):=by
  have he:=MixedFirstDefectNormEnvelope.integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs v b hvb F hF hFm
      ρ hL hρ hρ1 k hpos A0 ν hA0 hν ω
  have hm:=MixedFirstDefectMinkowski.norm_le
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs θ v b hvb F hF hFm hsmall
      ρ hL hρ.le k ω hsec (fun a=>Cs*Env ρ hL hρ.le k A0 ν ω a)
        (he.2.2.const_mul Cs) hb
  rw [integral_const_mul,MixedFirstDefectNormEnvelope.integral_eq
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs v b hvb F hF hFm
      ρ hL hρ.le k hpos hbH A0 ν ω he.2.2] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left
    (MixedFirstDefectConvolutionTransport.le_relative
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs v b hvb F hF hFm
        ρ hL hρ hρ1 k h hh hspan hpos hbH A0 ν hA0 hν ω) hCs)

end SHE.MixedFirstDefectNativeBound
