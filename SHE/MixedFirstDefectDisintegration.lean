module

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

namespace SHE.MixedFirstDefectDisintegration
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


/-- The actual retained full defect is the scalar integral over the
original old/current times of the actual old-space averaged point.
This is an AE identity in the original output Haar measure. -/
theorem field_eq_average (hΛ:0≤Λ)(k:ℕ)(ω:Ω):
    (fun x:HeatCircle=>Field k (ω,x))=ᵐ[haarAddCircle]
      (fun x=>∫a:(Fin k→ℝ)×ℝ,Sp k a.1 a.2 ω x
        ∂(Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))).prod volume):=by
  let T:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))
  let W:=Measure.pi (fun _:Fin k=>haarAddCircle (T:=2*Real.pi))
  let p:=past ω
  have hi:=ControlledReferenceFamilyDefectL1.history_integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z
      (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm hΛ haarAddCircle k p ω
  have he:historyMeasure (referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb (0,0)) haarAddCircle k=
      historyMeasure R₀ haarAddCircle k:=HistoryMeasureGeometry.historyMeasure_eq
        (R:=referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb (0,0)) (Q:=R₀) rfl rfl (haarAddCircle:Measure HeatCircle) k
  rw [he] at hi
  have hp:=(separated_measurePreserving R₀ (haarAddCircle:Measure HeatCircle) k).prod
    (MeasurePreserving.id (volume:Measure ℝ))
  have hs:Integrable (fun z:(HeatCircle×((Fin k→ℝ)×(Fin k→HeatCircle)))×ℝ=>
      Pt k (separated k (z.1.1,z.1.2.1,z.1.2.2)) ω z.2)
      (((haarAddCircle:Measure HeatCircle).prod (T.prod W)).prod volume):=
    hp.integrable_comp_of_integrable hi
  have ha:Integrable (fun z:HeatCircle×(((Fin k→ℝ)×(Fin k→HeatCircle))×ℝ)=>
      Pt k (separated k (z.1,z.2.1.1,z.2.1.2)) ω z.2.2)
      ((haarAddCircle:Measure HeatCircle).prod ((T.prod W).prod volume)):=
    (measurePreserving_prodAssoc (haarAddCircle:Measure HeatCircle) (T.prod W)
      (volume:Measure ℝ)).symm.integrable_comp_of_integrable hs
  have hfield (x:HeatCircle):Field k (ω,x)=
      ∫t:Fin k→ℝ,∫w:Fin k→HeatCircle,∫q:ℝ,
        Pt k (separated k (x,t,w)) ω q ∂volume ∂W ∂T:=by
    change (∫t:Fin k→ℝ,∫w:Fin k→HeatCircle,
      MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (Base (θ,p)) k (separated k (x,t,w)) ω ∂W ∂T)=_
    apply integral_congr_ae
    filter_upwards with t
    apply integral_congr_ae
    filter_upwards with w
    exact MixedJointActiveVolume.mark_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (Base (θ,p)) k (separated k (x,t,w)) ω
  filter_upwards [ha.prod_right_ae] with x hx
  have hb:Integrable (fun z:(Fin k→ℝ)×((Fin k→HeatCircle)×ℝ)=>
      Pt k (separated k (x,z.1,z.2.1)) ω z.2.2) (T.prod (W.prod volume)):=
    (measurePreserving_prodAssoc T W (volume:Measure ℝ)).symm.integrable_comp_of_integrable hx
  have hsp:=MixedFirstDefectIntegral.spatial_integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb F hF hFm hΛ k ω
  have hspx:Integrable (fun a:(Fin k→ℝ)×ℝ=>Sp k a.1 a.2 ω x) (T.prod volume):=by
    have hh:Integrable (fun z:((Fin k→ℝ)×ℝ)×(Fin k→HeatCircle)=>
        Pt k (separated k (x,z.1.1,z.2)) ω z.1.2) ((T.prod volume).prod W):=
      (NodeIntegralCycle.measurePreserving_cycle T W (volume:Measure ℝ)).symm.integrable_comp_of_integrable hx
    exact hh.integral_prod_left
  rw [hfield,integral_prod _ hspx]
  apply integral_congr_ae
  filter_upwards [hb.prod_right_ae] with t ht
  exact integral_integral_swap ht

end SHE.MixedFirstDefectDisintegration
