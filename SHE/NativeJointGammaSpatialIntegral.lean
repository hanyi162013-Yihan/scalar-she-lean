module
public import SHE.NativeJointGammaFourierColumns
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.NativeJointGammaSpatialIntegral
open MeasureTheory Set FiniteHaar StoppedFourier OrthogonalItoChannels AddCircle
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput):=borel _
local instance : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(v b:ℝ≥0)
variable {κ m U:ℝ}(hκ:0<κ)(hm:0<m)
variable (B:ℝ)(hB:0≤B)(g:Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ)
variable (hgm:∀i,@Measurable _ ℂ (𝓕.predictable.prod inferInstance) _ (g i))
variable (hg:∀i p x,‖g i (p,x)‖≤B)
variable (c0 c1 r0 r1:ℝ≥0×Ω→EllipticField m U)
variable (hc0:Measurable[𝓕.predictable] c0)(hc1:Measurable[𝓕.predictable] c1)
variable (hr0:Measurable[𝓕.predictable] r0)(hr1:Measurable[𝓕.predictable] r1)
variable (d:ℝ≥0×Ω→ℝ)(hd:Measurable[𝓕.predictable] d)(hdb:∀p,0≤d p ∧ d p≤1)
local notation "Raw"=>NativeJointPhysicalGammaInput.raw v b hκ hm g c0 c1 r0 r1 d

include hgm hc0 hc1 hr0 hr1 hd in
theorem stronglyMeasurable (p:ℝ≥0×Ω):StronglyMeasurable (fun x:HeatCircle=>Raw (p,x)):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  exact (NativeJointPhysicalGammaInput.raw_predictable 𝓕 v b hκ hm g hgm c0 c1 r0 r1
    hc0 hc1 hr0 hr1 d hd).comp_measurable (measurable_const.prodMk measurable_id)

include hB hgm hg hc0 hc1 hr0 hr1 hd hdb in
/-- The literal original two-channel input is spatially Bochner integrable
at EVERY time/sample, with no chosen L2 representative in the statement. -/
theorem integrable (p:ℝ≥0×Ω):Integrable (fun x:HeatCircle=>Raw (p,x)) haarAddCircle:=by
  apply (integrable_const (1+NativePhysicalGammaInput.majorant v b (κ:=κ) (U:=U) B p)).mono'
    (stronglyMeasurable 𝓕 v b hκ hm g hgm c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd p).aestronglyMeasurable
  filter_upwards with x
  have hs:=NativeJointPhysicalGammaInput.raw_majorized v b hκ hm B hB g hg c0 c1 r0 r1 d hdb p x
  nlinarith [sq_nonneg (‖Raw (p,x)‖-1)]

include hB hgm hg hc0 hc1 hr0 hr1 hd hdb in
theorem coordinate_integrable (p:ℝ≥0×Ω)(L:Both RealHaarInput→L[ℝ]ℝ)(l:ℤ):
    Integrable (fun x:HeatCircle=>fourier (-l) x*(L (Raw (p,x)):ℂ)) haarAddCircle:=by
  have hi:Integrable (fun x:HeatCircle=>(L (Raw (p,x)):ℂ)) haarAddCircle:=
    (Complex.ofRealCLM.comp L).integrable_comp
      (integrable 𝓕 v b hκ hm B hB g hgm hg c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb p)
  exact hi.bdd_mul (fourier (-l)).continuous.measurable.aestronglyMeasurable
    (ae_of_all _ (fun x=>show ‖fourier (-l) x‖≤(1:ℝ) by simp [fourier_apply]))
end SHE.NativeJointGammaSpatialIntegral
