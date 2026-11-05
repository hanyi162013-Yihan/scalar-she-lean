module

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

namespace SHE.MixedFirstDefectRelativeField
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


def relative (k:ℕ)(t:Fin k→ℝ)(q:ℝ)(ω:Ω)(z:AddCircle (1:ℝ)×(Fin k→HeatCircle)):ℝ:=
  Pt k (separated k (CircleNormalization.scale 1 (2*π) z.1,t,
    fun i=>z.2 i+CircleNormalization.scale 1 (2*π) z.1)) ω q

include hsmall in
set_option backward.isDefEq.respectTransparency true in
 theorem measurable (hΛ:0≤Λ)(k:ℕ)(t:Fin k→ℝ)(q:ℝ)(ω:Ω):
    Measurable (relative 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb F hF hFm k t q ω):=by
  have hroot:Measurable (fun z:AddCircle (1:ℝ)×(Fin k→HeatCircle)=>
      CircleNormalization.scale 1 (2*π) z.1):=
    (CircleNormalization.scaleMeasurableEquiv 1 (2*π)).measurable.comp measurable_fst
  have hw:Measurable (fun z:AddCircle (1:ℝ)×(Fin k→HeatCircle)=>
      fun i=>z.2 i+CircleNormalization.scale 1 (2*π) z.1):=
    Measurable.of_eval (fun i=>((measurable_pi_apply i).comp measurable_snd).add hroot)
  have hmap:Measurable (fun z:AddCircle (1:ℝ)×(Fin k→HeatCircle)=>
      ((separated k (CircleNormalization.scale 1 (2*π) z.1,t,
        fun i=>z.2 i+CircleNormalization.scale 1 (2*π) z.1),ω),q)):=
    (((separated_measurable k).comp (hroot.prodMk (measurable_const.prodMk hw))).prodMk
      measurable_const).prodMk measurable_const
  have hm:=(MixedFirstDefectIntegral.point_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb F hF hFm hsmall hΛ k).comp hmap
  exact hm

 theorem average (k:ℕ)(t:Fin k→ℝ)(q:ℝ)(ω:Ω)(x:AddCircle (1:ℝ)):
    Sp k t q ω (CircleNormalization.scale 1 (2*π) x)=
      ∫w:Fin k→HeatCircle,relative 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb F hF hFm k t q ω (x,w) ∂Measure.pi (fun _=>haarAddCircle):=by
  have hh:=(OrderedHeatForests.relativeShift_preserving k (CircleNormalization.scale 1 (2*π) x)).integral_comp'
    (fun w:Fin k→HeatCircle=>Pt k (separated k (CircleNormalization.scale 1 (2*π) x,t,w)) ω q)
  exact hh.symm

end SHE.MixedFirstDefectRelativeField
