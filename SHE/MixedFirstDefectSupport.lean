module

public import SHE.ControlledThetaPhysicalGeometry
public import SHE.NativeBesselParameterSection
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

namespace SHE.MixedFirstDefectSupport
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


/-- The actual spatial section is zero off its exact strict/clock support. -/
theorem spatial_zero (k:ℕ)(t:Fin k→ℝ)(q:ℝ)(ω:Ω)
    (hn:¬(StrictHistory Zero k (separated k ((0:HeatCircle),t,fun _=>0)) ∧
      (v:ℝ)≤q ∧ q≤(carrier Zero k).terminal (separated k ((0:HeatCircle),t,fun _=>0))))
    (x:HeatCircle):Sp k t q ω x=0:=by
  let z:=separated k ((0:HeatCircle),t,fun _=>0)
  let p:ℝ×Inputs:=(θ,past ω)
  have hz(w:Fin k→HeatCircle):Pt k (separated k (x,t,w)) ω q=0:=by
    let h:=separated k (x,t,w)
    have hterm:(carrier (Base p) k).terminal h=(carrier Zero k).terminal z:=by
      rw [ControlledReferenceThetaGeometry.carrier_terminal_eq P (fun z=>κ+aV z) hAs Λ v b hvb Z
        (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm p (0,(0,0)) k h]
      change (carrier Zero k).terminal (separated k (x,t,w))=
        (carrier Zero k).terminal (separated k ((0:HeatCircle),t,fun _=>0))
      rw [ActualMeanKernel.terminal_separated Zero (b:ℝ) (fun _=>rfl),
        ActualMeanKernel.terminal_separated Zero (b:ℝ) (fun _=>rfl)]
    change (if (v:ℝ)≤q ∧ q≤(carrier (Base p) k).terminal h then
      MixedJointUncutDefectTrace.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (Base p) k h ω q else 0)=0
    split_ifs with hq
    · have hns:¬StrictHistory (Base p) k h:=by
        intro hs
        have hs0:StrictHistory Zero k h:=(ControlledThetaPhysicalGeometry.strict_iff P (fun z=>κ+aV z)
          hAs Λ v b hvb Z (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm p (0,(0,0)) k h).mp hs
        have hsz:StrictHistory Zero k z:=(FixedHistoryTimeFactors.strict_sections Zero (b:ℝ)
          (fun _=>rfl) k t x 0 w (fun _=>0)).mp hs0
        exact hn ⟨hsz,hq.1,hq.2.trans_eq hterm⟩
      rw [MixedJointUncutDefectTrace.point_eq_weight
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k h ω q hq,
        PhysicalParentGeometry.weight_zero_of_not_strict (Base p) k h hns,zero_mul]
    · rfl
  change (∫w:Fin k→HeatCircle,Pt k (separated k (x,t,w)) ω q
    ∂Measure.pi (fun _=>haarAddCircle))=0
  simp only [hz,integral_zero]

/-- A vanishing actual spatial section has zero canonical native value,
including the canonical realization's bad-section branch. -/
theorem pointValue_zero (ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)(k:ℕ)(t:Fin k→ℝ)(q:ℝ)(ω:Ω)
    (hn:¬(StrictHistory Zero k (separated k ((0:HeatCircle),t,fun _=>0)) ∧
      (v:ℝ)≤q ∧ q≤(carrier Zero k).terminal (separated k ((0:HeatCircle),t,fun _=>0)))):
    MixedFirstDefectRMS.pointValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb F hF hFm ρ hΛ hρ k t q ω=0:=by
  let A:Ω×HeatCircle→ℂ:=fun z=>(Sp k t q z.1 z.2:ℂ)
  have hz(x:HeatCircle):A (ω,x)=0:=by
    change (Sp k t q ω x:ℂ)=0
    rw [spatial_zero 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb F hF hFm k t q ω hn x,Complex.ofReal_zero]
  have hc:(fun x:HeatCircle=>MeasurableL2FieldAE.clean haarAddCircle A (ω,x))=0:=by
    funext x
    unfold MeasurableL2FieldAE.clean
    split_ifs
    · exact hz x
    · rfl
  change OneInputOperator.besselHalf Λ ρ hΛ hρ
    (MeasurableL2Field.realizeL2 (ν:=haarAddCircle) (MeasurableL2FieldAE.clean haarAddCircle A) ω)=0
  unfold MeasurableL2Field.realizeL2
  rw [hc]
  split_ifs
  · rw [MemLp.toLp_zero,map_zero]
  · exact map_zero _

end SHE.MixedFirstDefectSupport
