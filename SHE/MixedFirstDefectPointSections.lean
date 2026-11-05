module

public import SHE.MixedFirstDefectPointBound
public import SHE.MixedFirstDefectSupport
public import SHE.RelativeHistoryGeometry
public import SHE.MixedFirstDefectRelativeField
public import SHE.ControlledDefectAgeRMS
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

namespace SHE.MixedFirstDefectPointSections
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

def envelope (ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)(k:ℕ)(A0 ν:ℝ)(ω:Ω)(a:(Fin k→ℝ)×ℝ):ℝ:=
  let z:=separated k ((0:HeatCircle),a.1,fun _=>0)
  if StrictHistory Zero k z ∧ (v:ℝ)<a.2 ∧ a.2≤(carrier Zero k).terminal z then
    MixedFirstDefectRMS.oldFactor Λ κ P hAs v b hvb F hF hFm k a.1 A0 ν*
      MixedFirstDefectRMS.pairKernel Λ κ P hAs v b hvb F hF hFm ρ k a.1 a.2*
        sqrt (Input ρ hΛ hρ a.2 ω) else 0

set_option backward.isDefEq.respectTransparency true in
include hsmall in
/-- The actual sharp bound on the full original time product, including
its exact zero extensions. The event is common before every sample. -/
theorem sections_with_constants (hM:0≤M) (hP:P.coefficient=(fun z=>κ+aV z))(hΛ:1≤Λ)
    {ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)(k:ℕ):
    ∃Hs Cs:ℝ,0<Hs ∧ 0<Cs ∧
      Hs=ControlledDefectConstants.horizon P.lower P.lower_pos ell M hell hM ρ hρ hρhalf k ∧
      Cs=ControlledDefectConstants.constant ell M hell hM ρ hρ hρhalf k P ∧
      ((b:ℝ)-(v:ℝ)≤P.horizon→(b:ℝ)-(v:ℝ)≤Hs→
      (∀j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)→
      ∀A0 ν:ℝ,0≤A0→0≤ν→
        (∀x j,j≤k→∀y,‖iteratedFDeriv ℝ j (F x) y‖≤A0*ν^j)→
      ∀ᵐa:(Fin k→ℝ)×ℝ∂
        (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))).prod volume,
        ∀ω:Ω,MemLp (fun x:HeatCircle=>(Sp k a.1 a.2 ω x:ℂ)) 2 haarAddCircle ∧
          ‖MixedFirstDefectRMS.pointValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
            P hAs θ v b hvb F hF hFm ρ hΛ hρ.le k a.1 a.2 ω‖≤
              Cs*envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
                P hAs v b hvb F hF hFm ρ hΛ hρ.le k A0 ν ω a):=by
  obtain ⟨Hs,Cs,hHs,hCs,hHeq,hCeq,hb⟩:=MixedFirstDefectPointBound.bound_with_constants
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb F hF hFm hsmall hM hP hΛ hρ hρhalf k
  refine ⟨Hs,Cs,hHs,hCs,hHeq,hCeq,?_⟩
  intro hspan hspanH hH A0 ν hA0 hν hjet
  let νt:Measure (Fin k→ℝ):=Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))
  let T: (Fin k→ℝ)→ℝ:=fun t=>(carrier Zero k).terminal (separated k ((0:HeatCircle),t,fun _=>0))
  have hT:Measurable T:=(carrier Zero k).terminal_measurable.comp
    ((separated_measurable k).comp (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
  have hne:∀ᵐa:(Fin k→ℝ)×ℝ∂νt.prod volume,a.2≠T a.1:=by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_snd (hT.comp measurable_fst)).compl).mpr
    exact ae_of_all _ (fun t=>volume.ae_ne (T t))
  have hnev:∀ᵐa:(Fin k→ℝ)×ℝ∂νt.prod volume,a.2≠(v:ℝ):=
    Measure.quasiMeasurePreserving_snd.ae (volume.ae_ne (v:ℝ))
  have hsmallZ(t:Fin k→ℝ):SmallHistory Zero (uniformHorizon 1) k
      (separated k ((0:HeatCircle),t,fun _=>0)):=
    RelativeHistoryGeometry.smallHistory_of_span Zero b (fun _=>le_rfl) (fun _ _=>le_rfl)
      (uniformHorizon 1) k hH _
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hb,hne,hnev] with a ha hneT hneV
  intro ω
  let z:=separated k ((0:HeatCircle),a.1,fun _=>0)
  by_cases hm:StrictHistory Zero k z ∧ (v:ℝ)<a.2 ∧ a.2≤(carrier Zero k).terminal z
  · have hq:a.2<(carrier Zero k).terminal z:=lt_of_le_of_ne hm.2.2 hneT
    have hx:=ha hm.1 (hsmallZ a.1) hspan hspanH A0 ν hA0 hν hjet a.2 hm.2.1.le hq ω
    refine ⟨hx.1,?_⟩
    change _≤Cs*(if StrictHistory Zero k z ∧ (v:ℝ)<a.2 ∧ a.2≤(carrier Zero k).terminal z then
      MixedFirstDefectRMS.oldFactor Λ κ P hAs v b hvb F hF hFm k a.1 A0 ν*
        MixedFirstDefectRMS.pairKernel Λ κ P hAs v b hvb F hF hFm ρ k a.1 a.2*
          sqrt (Input ρ hΛ hρ.le a.2 ω) else 0)
    rw [if_pos hm]
    convert hx.2 using 1 <;> ring
  · have hn:¬(StrictHistory Zero k z ∧ (v:ℝ)≤a.2 ∧ a.2≤(carrier Zero k).terminal z):=by
      intro hh
      exact hm ⟨hh.1,lt_of_le_of_ne hh.2.1 (Ne.symm hneV),hh.2.2⟩
    have hz(x:HeatCircle):Sp k a.1 a.2 ω x=0:=MixedFirstDefectSupport.spatial_zero
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb F hF hFm k a.1 a.2 ω hn x
    refine ⟨?_,?_⟩
    · simpa only [hz,Complex.ofReal_zero] using (MemLp.zero' : MemLp (0:HeatCircle→ℂ) 2 haarAddCircle)
    · rw [MixedFirstDefectSupport.pointValue_zero
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb F hF hFm
          ρ hΛ hρ.le k a.1 a.2 ω hn,norm_zero]
      change 0≤Cs*(if StrictHistory Zero k z ∧ (v:ℝ)<a.2 ∧ a.2≤(carrier Zero k).terminal z then
        MixedFirstDefectRMS.oldFactor Λ κ P hAs v b hvb F hF hFm k a.1 A0 ν*
          MixedFirstDefectRMS.pairKernel Λ κ P hAs v b hvb F hF hFm ρ k a.1 a.2*
            sqrt (Input ρ hΛ hρ.le a.2 ω) else 0)
      rw [if_neg hm,mul_zero]

set_option backward.isDefEq.respectTransparency true in
include hsmall in
/-- The actual sharp bound on the full original time product, including
its exact zero extensions. The event is common before every sample. -/
theorem sections (hP:P.coefficient=(fun z=>κ+aV z))(hΛ:1≤Λ)
    {ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)(k:ℕ):
    ∃Hs Cs:ℝ,0<Hs ∧ 0<Cs ∧
      ((b:ℝ)-(v:ℝ)≤P.horizon→(b:ℝ)-(v:ℝ)≤Hs→
      (∀j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)→
      ∀A0 ν:ℝ,0≤A0→0≤ν→
        (∀x j,j≤k→∀y,‖iteratedFDeriv ℝ j (F x) y‖≤A0*ν^j)→
      ∀ᵐa:(Fin k→ℝ)×ℝ∂
        (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) b))).prod volume,
        ∀ω:Ω,MemLp (fun x:HeatCircle=>(Sp k a.1 a.2 ω x:ℂ)) 2 haarAddCircle ∧
          ‖MixedFirstDefectRMS.pointValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
            P hAs θ v b hvb F hF hFm ρ hΛ hρ.le k a.1 a.2 ω‖≤
              Cs*envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
                P hAs v b hvb F hF hFm ρ hΛ hρ.le k A0 ν ω a):=by
  have hM:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  obtain ⟨Hs,Cs,hHs,hCs,_,_,hb⟩:=sections_with_constants
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb F hF hFm hsmall
      hM hP hΛ hρ hρhalf k
  exact ⟨Hs,Cs,hHs,hCs,hb⟩

end SHE.MixedFirstDefectPointSections
