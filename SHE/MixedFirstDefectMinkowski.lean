module

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

namespace SHE.MixedFirstDefectMinkowski
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



local notation "PV"=>MixedFirstDefectRMS.pointValue
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb F hF hFm
local notation "Val"=>MixedFirstDefectRMS.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb F hF hFm

set_option backward.isDefEq.respectTransparency true in
include hsmall in
/-- Apply a sharp integrable point norm envelope to the actual retained
first defect. The actual current convolution is integrated first, then
its norm is bounded; no stochastic square enters the time integrals. -/
theorem norm_le (ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)(k:ℕ)(ω:Ω)
    (hsec:∀ᵐa:(Fin k→ℝ)×ℝ∂
      (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))).prod volume,
      MemLp (fun x:HeatCircle=>(Sp k a.1 a.2 ω x:ℂ)) 2 haarAddCircle)
    (E:((Fin k→ℝ)×ℝ)→ℝ)
    (hE:Integrable E ((Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))).prod volume))
    (hb:∀ᵐa:(Fin k→ℝ)×ℝ∂
      (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))).prod volume,
      ‖PV ρ hΛ hρ k a.1 a.2 ω‖≤E a):
    ‖Val ρ hΛ hρ k ω‖≤∫a:(Fin k→ℝ)×ℝ,E a
      ∂(Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))).prod volume:=by
  let ν:Measure ((Fin k→ℝ)×ℝ):=
    (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))).prod volume
  let Q:(((Fin k→ℝ)×ℝ)×HeatCircle)→ℂ:=fun z=>(Sp k z.1.1 z.1.2 ω z.2:ℂ)
  let G:Ω×HeatCircle→ℂ:=fun z=>(Field k z:ℂ)
  have hmap:Measurable (fun z:((Fin k→ℝ)×ℝ)×HeatCircle=>(z.1,(ω,z.2))):=
    measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
  have hsp:=MixedFirstDefectIntegral.spatial_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb F hF hFm hsmall
      (le_trans (by norm_num) hΛ) k
  have hQr:=hsp.comp hmap
  have hQ:Measurable Q:=Complex.continuous_ofReal.measurable.comp hQr
  have hi:Integrable Q (ν.prod haarAddCircle):=
    (MixedFirstDefectIntegral.spatial_integrable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb F hF hFm
        (le_trans (by norm_num) hΛ) k ω).ofReal
  have hGr:Measurable (Field k):=MixedCanonicalRootFields.field_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z
      (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm hsmall (le_trans (by norm_num) hΛ) 2 k
  have hG:Measurable G:=Complex.continuous_ofReal.measurable.comp hGr
  obtain ⟨C,hCn,hC⟩:=MixedCanonicalRootFields.field_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z
      (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm hsmall (le_trans (by norm_num) hΛ) k
  have hGp:MemLp (fun x:HeatCircle=>G (ω,x)) 2 haarAddCircle:=
    MemLp.of_bound (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable C (by
      filter_upwards with x
      simpa only [G,Complex.norm_real,MixedFirstDefectRMS.field] using hC 2 (ω,x))
  have he:(fun x:HeatCircle=>G (ω,x))=ᵐ[haarAddCircle] fun x=>∫a,Q (a,x) ∂ν:=by
    filter_upwards [MixedFirstDefectDisintegration.field_eq_average
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb F hF hFm
        (le_trans (by norm_num) hΛ) k ω] with x hx
    change (Field k (ω,x):ℂ)=∫a:(Fin k→ℝ)×ℝ,(Sp k a.1 a.2 ω x:ℂ) ∂ν
    rw [integral_complex_ofReal,hx]
  have hv:∀ᵐa∂ν,‖NativeBesselFieldAE.value Λ ρ hΛ hρ Q a‖≤E a:=by
    filter_upwards [hb] with a ha
    have heq:=NativeBesselParameterSection.congr Λ ρ hΛ hρ Q
      (fun z:Ω×HeatCircle=>(Sp k a.1 a.2 z.1 z.2:ℂ)) a ω rfl
    rw [heq]
    exact ha
  exact NativeBesselParameterAverageAE.norm_le ν Λ ρ hΛ hρ Q hQ hi hsec G hG ω hGp he E hE hv

end SHE.MixedFirstDefectMinkowski
