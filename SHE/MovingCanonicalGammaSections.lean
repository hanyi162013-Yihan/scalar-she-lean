module
public import SHE.MovingNativeGammaFields
public import SHE.ComplexRealification
public import SHE.ScalarHeatSixReal
public import SHE.WindowFieldSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.MovingCanonicalGammaSections
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier NativeHeatObservation
open OrthogonalItoChannels DyadicApproximation SmoothCylinders
open scoped NNReal ENNReal
local instance movingCanonicalGammaSections_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance movingCanonicalGammaSections_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingCanonicalGammaSections_realSigma : MeasurableSpace RealL2:=borel _
local instance movingCanonicalGammaSections_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance movingCanonicalGammaSections_circleSigma : MeasurableSpace CircleL2:=borel _
local instance movingCanonicalGammaSections_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance movingCanonicalGammaSections_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance movingCanonicalGammaSections_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance movingCanonicalGammaSections_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance movingCanonicalGammaSections_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)(u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (P:CanonicalCovariance.ProfileParameters)(hκP:κ<P.lower)(W h:ℝ)
variable (hW:0≤W)(hh:0<h)(hcover:W+h≤H)(hH:(H:ℝ)≤1)
local notation "past" r:max=>NativeMovingGammaClock.past W r
local notation "terminal" r:max=>NativeMovingGammaClock.terminal W h r
local notation "covered" r:max=>NativeMovingGammaClock.terminal_le hW hh.le H hcover r
local notation "one" r:max=>(show (terminal r:ℝ)≤1 from
  (show (terminal r:ℝ)≤(H:ℝ) by exact_mod_cast covered r).trans hH)
local notation "Canon"=>MovingNativeGammaFields.canonical 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP W h hW hh hcover hH
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1:ℝ≥0)(hBDG0:StandardTerminalBDG16 I₀ B0)(hBDG1:StandardTerminalBDG16 I₁ B1)
variable {a:ℝ→ℝ}(ha:BoundedSmooth a){A:ℝ}(hA:0≤A)
variable (hholder:∀z w,|a z-a w|≤A*|z-w|^P.exponent)(j:ℕ)

include hnull hBDG0 hBDG1 ha in
theorem canonical_predictable (r:ℝ)(i:Fin 6):
    @Measurable ((ℝ≥0×Ω)×HeatCircle) ℂ (𝓕.predictable.prod inferInstance) _ (Canon a j r i):=
  NativeJointGammaFields.fields_predictable (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=past r) (b:=terminal r)
    (hbH:=covered r) (hb1:=one r) (U:=Function.uncurry S.first) (V:=Function.uncurry S.second)
    (hU:=S.first_predictable) (hV:=S.second_predictable) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP)
    (I0:=I₀) (I1:=I₁) (NativeMovingGammaClock.terminal_pos hW hh r) hnull B0 B1 hBDG0 hBDG1 a ha j i

theorem canonical_real (r:ℝ)(i:Fin 6)(z:(ℝ≥0×Ω)×HeatCircle):
    (Canon a j r i z).im=0:=
  ScalarHeatSixReal.im a j _ _ _ _ _ _ i z

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hF:StandardItoStoppedParameterFubini J)
variable (hIJ0:NativeObservationNaturality.StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ1:NativeObservationNaturality.StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hW hh hcover hH hF hIJ0 hIJ1 hnull hBDG0 hBDG1 ha hA hholder in
/-- One jointly predictable REAL six-field realization has exactly the
original canonical fixed-past sections in the ORIGINAL energy class.
The spatial equality is obtained by measurable window-event Fubini. -/
theorem exists_sections (ν:Measure ℝ)[IsFiniteMeasure ν]:
    ∃g:Fin 6→MovingNativeGammaFields.Domain Ω→ℂ,
      (∀i,@Measurable (MovingNativeGammaFields.Domain Ω) ℂ
        (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance) _ (g i)) ∧
      (∀i z,‖g i z‖≤ScalarHeatSingleMultiplier.cap A P.exponent j) ∧
      (∀i z,(g i z).im=0) ∧
      ∀ᵐr∂ν,∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,
        ∀ᵐp∂energyMeasure μ H,p∈NativeGammaClock.window (past r) (terminal r)→∀i,
          g i ((r,p),x)=Canon a j r i (p,x):=by
  obtain ⟨g,hg,hbound,he⟩:=MovingNativeGammaFields.exists_fields 𝓕 μ H Λ κ hκ haU haV
    hell hbU hbV I₀ I₁ u₀ v₀ S P hκP W h hW hh hcover hH J hF hIJ0 hIJ1 hnull
    B0 B1 hBDG0 hBDG1 ha hA hholder j ν
  let G:Fin 6→MovingNativeGammaFields.Domain Ω→ℂ:=fun i z=>ComplexRealification.value (g i z)
  have hG:∀i,@Measurable (MovingNativeGammaFields.Domain Ω) ℂ
      (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance) _ (G i):=
    fun i=>ComplexRealification.measurable.comp (hg i)
  refine ⟨G,hG,fun i z=>(ComplexRealification.norm_le _).trans (hbound i z),fun i z=>rfl,?_⟩
  filter_upwards [he] with r hr
  have hpred:∀i,@Measurable ((ℝ≥0×Ω)×HeatCircle) ℂ (𝓕.predictable.prod inferInstance) _
      (fun z=>G i ((r,z.1),z.2)):=by
    letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
    exact fun i=>(hG i).comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hfst:Measurable (fun z:(ℝ≥0×Ω)×HeatCircle=>z.1):=measurable_fst
  have hfst':@Measurable ((ℝ≥0×Ω)×HeatCircle) (ℝ≥0×Ω) inferInstance 𝓕.predictable Prod.fst:=
    hfst.mono le_rfl (predictable_le_product 𝓕)
  have hid:@Measurable ((ℝ≥0×Ω)×HeatCircle) ((ℝ≥0×Ω)×HeatCircle)
      inferInstance (𝓕.predictable.prod inferInstance) id:=hfst'.prodMk measurable_snd
  have hf:∀i,Measurable (fun z:(ℝ≥0×Ω)×HeatCircle=>G i ((r,z.1),z.2)):=
    fun i=>(hpred i).comp hid
  have hc:∀i,Measurable (Canon a j r i):=fun i=>
    (canonical_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP W h hW hh hcover hH
      hnull B0 B1 hBDG0 hBDG1 ha j r i).comp hid
  apply WindowFieldSections.window (timeMeasure H) μ AddCircle.haarAddCircle
    (fun i z=>G i ((r,z.1),z.2)) (Canon a j r) (NativeGammaClock.window (past r) (terminal r))
    ((predictable_le_product 𝓕) _ (NativeGammaClock.window_measurable 𝓕 (past r) (terminal r))) hf hc
  filter_upwards [hr] with q hq
  filter_upwards [hq] with x hx
  filter_upwards [hx] with ω hω
  intro hp i
  change ComplexRealification.value (g i ((r,(q,ω)),x))=_
  rw [hω hp.1 hp.2.le i]
  exact ComplexRealification.eq (canonical_real 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP W h hW hh hcover hH j r i ((q,ω),x))
end SHE.MovingCanonicalGammaSections
