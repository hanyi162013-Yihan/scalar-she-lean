module
public import SHE.MovingNativePredictablePoint
public import SHE.MovingNativeColumns
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.MovingNativePredictableKernel
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  Set WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories HistoryProductMeasure AddCircle
open scoped NNReal ENNReal
local instance movingNativePredictableKernel_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingNativePredictableKernel_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance movingNativePredictableKernel_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance movingNativePredictableKernel_realSigma:MeasurableSpace RealL2:=borel _
local instance movingNativePredictableKernel_realBorel:BorelSpace RealL2:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0)(Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Point"=>MovingNativePredictablePoint.point
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
abbrev Param(k:ℕ):Type:=(Fin k→ℝ)×(ℝ≥0×(ℝ≥0×Ω))

def field(k:ℕ)(weighted:Bool)(θ:ℝ)(z:Param (Ω:=Ω) k×(HeatCircle×HeatCircle)):ℂ:=
  ((∫w:Fin k→HeatCircle,Point k weighted θ ((z.1.2,separated k (z.2.2,z.1.1,w)),z.2.1)
    ∂Measure.pi (fun _=>haarAddCircle)):ℝ)
local notation "Field"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm
local notation "Spatial"=>MovingNativeSpatialKernel.field
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem field_predictable(k:ℕ)(weighted:Bool)(θ:ℝ):
    @Measurable (Param (Ω:=Ω) k×(HeatCircle×HeatCircle)) ℂ
      ((((inferInstance:MeasurableSpace (Fin k→ℝ)).prod
        ((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable))).prod inferInstance) _
      (Field k weighted θ):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  let W:=(Param (Ω:=Ω) k×(HeatCircle×HeatCircle))×(Fin k→HeatCircle)
  have hh:Measurable (fun z:W=>separated k (z.1.2.2,z.1.1.1,z.2)):=
    (separated_measurable k).comp
      (measurable_fst.snd.snd.prodMk (measurable_fst.fst.fst.prodMk measurable_snd))
  have hmap:Measurable (fun z:W=>((z.1.1.2,separated k (z.1.2.2,z.1.1.1,z.2)),z.1.2.1)):=
    (measurable_fst.fst.snd.prodMk hh).prodMk measurable_fst.snd.fst
  have hp:=(MovingNativePredictablePoint.point_predictable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k weighted θ).comp hmap
  have hi:=hp.stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _:Fin k=>haarAddCircle (T:=2*Real.pi)))
  exact Complex.continuous_ofReal.measurable.comp hi.measurable

theorem field_eq(k:ℕ)(weighted:Bool)(θ:ℝ)(z:Param (Ω:=Ω) k)(y x:HeatCircle):
    Field k weighted θ (z,(y,x))=
      if z.2.1<z.2.2.1 ∧ z.2.2.1<z.2.1+h then
        Spatial k weighted ((θ,((z.2.1,z.2.2.1-z.2.1),(z.1,z.2.2.2))),(y,x)) else 0:=by
  by_cases hz:z.2.1<z.2.2.1 ∧ z.2.2.1<z.2.1+h
  · simp only [field,MovingNativePredictablePoint.point,if_pos hz,MovingNativeSpatialKernel.field]
  · simp only [field,MovingNativePredictablePoint.point,if_neg hz,integral_zero,Complex.ofReal_zero]

def common(k:ℕ)(z:Param (Ω:=Ω) k×(HeatCircle×HeatCircle)):ℂ:=
  Field k false 1 z-Field k false 0 z
def endpoint(k:ℕ)(z:Param (Ω:=Ω) k×(HeatCircle×HeatCircle)):ℂ:=Field k true 1 z
local notation "Common"=>common 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm
local notation "Endpoint"=>endpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm
local notation "OldCommon"=>MovingNativeColumns.common
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "OldEndpoint"=>MovingNativeColumns.endpoint
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem common_predictable(k:ℕ):
    @Measurable (Param (Ω:=Ω) k×(HeatCircle×HeatCircle)) ℂ
      ((((inferInstance:MeasurableSpace (Fin k→ℝ)).prod
        ((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable))).prod inferInstance) _ (Common k):=
  (field_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k false 1).sub
  (field_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k false 0)

theorem endpoint_predictable(k:ℕ):
    @Measurable (Param (Ω:=Ω) k×(HeatCircle×HeatCircle)) ℂ
      ((((inferInstance:MeasurableSpace (Fin k→ℝ)).prod
        ((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable))).prod inferInstance) _ (Endpoint k):=
  field_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k true 1

theorem common_eq(k:ℕ)(z:Param (Ω:=Ω) k)(y x:HeatCircle):
    Common k (z,(y,x))=if z.2.1<z.2.2.1 ∧ z.2.2.1<z.2.1+h then
      OldCommon k (((z.2.1,z.2.2.1-z.2.1),(z.1,z.2.2.2)),(y,x)) else 0:=by
  rw [common,field_eq,field_eq]
  split_ifs <;> simp only [MovingNativeColumns.common,sub_self]

theorem endpoint_eq(k:ℕ)(z:Param (Ω:=Ω) k)(y x:HeatCircle):
    Endpoint k (z,(y,x))=if z.2.1<z.2.2.1 ∧ z.2.2.1<z.2.1+h then
      OldEndpoint k (((z.2.1,z.2.2.1-z.2.1),(z.1,z.2.2.2)),(y,x)) else 0:=
  field_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k true 1 z y x

theorem common_bound(hΛ:0≤Λ)(k:ℕ)(z:Param (Ω:=Ω) k):∃B:ℝ,0≤B∧∀y x,‖Common k (z,(y,x))‖≤B:=by
  obtain ⟨B,hB,hbound⟩:=MovingNativeColumns.common_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ k
    ((z.2.1,z.2.2.1-z.2.1),(z.1,z.2.2.2))
  refine ⟨B,hB,fun y x=>?_⟩
  rw [common_eq]
  split_ifs
  · exact hbound y x
  · simpa only [norm_zero] using hB

theorem endpoint_bound(hΛ:0≤Λ)(k:ℕ)(z:Param (Ω:=Ω) k):∃B:ℝ,0≤B∧∀y x,‖Endpoint k (z,(y,x))‖≤B:=by
  obtain ⟨B,hB,hbound⟩:=MovingNativeColumns.endpoint_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm hΛ k
    ((z.2.1,z.2.2.1-z.2.1),(z.1,z.2.2.2))
  refine ⟨B,hB,fun y x=>?_⟩
  rw [endpoint_eq]
  split_ifs
  · exact hbound y x
  · simpa only [norm_zero] using hB
end SHE.MovingNativePredictableKernel
