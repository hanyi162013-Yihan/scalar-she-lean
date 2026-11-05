module
public import SHE.NativeJointPhysicalGammaInput
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeGammaInputCongruence
open Set MeasureTheory FiniteHaar StoppedFourier NativeObservationCovariance OrthogonalItoChannels PredictableL2
open scoped NNReal ENNReal
local instance nativeGammaInputCongruence_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeGammaInputCongruence_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeGammaInputCongruence_circleSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeGammaInputCongruence_circleBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeGammaInputCongruence_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance nativeGammaInputCongruence_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance nativeGammaInputCongruence_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance nativeGammaInputCongruence_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (v b:ℝ≥0){κ m U:ℝ}(hκ:0<κ)(hm:0<m)
variable (g f:Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ)
variable (c0 c1 r0 r1:ℝ≥0×Ω→EllipticField m U)(d:ℝ≥0×Ω→ℝ)

/-- The literal convex physical Gamma row depends only on its actual
four scalar multipliers on the original stopped window. -/
theorem raw_eq (p:ℝ≥0×Ω)(x:HeatCircle)
    (he:p∈NativeGammaClock.window v b→∀i,g i (p,x)=f i (p,x)):
    NativeJointPhysicalGammaInput.raw v b hκ hm g c0 c1 r0 r1 d (p,x)=
      NativeJointPhysicalGammaInput.raw v b hκ hm f c0 c1 r0 r1 d (p,x):=by
  by_cases hp:p∈NativeGammaClock.window v b
  · simp only [NativeJointPhysicalGammaInput.raw,NativePhysicalGammaKernel.raw,ite_eq_left hp,
      he hp 0,he hp 2,he hp 3,he hp 5]
  · simp only [NativeJointPhysicalGammaInput.raw,NativePhysicalGammaKernel.raw,ite_eq_right hp,
      smul_zero,add_zero]

variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (hbH:b≤H)(hb1:(b:ℝ)≤1)(B:ℝ)(hB:0≤B)
variable (hgm:∀i,@Measurable _ ℂ (𝓕.predictable.prod inferInstance) _ (g i))
variable (hfm:∀i,@Measurable _ ℂ (𝓕.predictable.prod inferInstance) _ (f i))
variable (hg:∀i p x,‖g i (p,x)‖≤B)(hf:∀i p x,‖f i (p,x)‖≤B)
variable (hc0:Measurable[𝓕.predictable] c0)(hc1:Measurable[𝓕.predictable] c1)
variable (hr0:Measurable[𝓕.predictable] r0)(hr1:Measurable[𝓕.predictable] r1)
variable (hd:Measurable[𝓕.predictable] d)(hdb:∀p,0≤d p∧d p≤1)

theorem process_eq (x:HeatCircle)
    (he:∀ᵐp∂energyMeasure μ H,p∈NativeGammaClock.window v b→∀i,g i (p,x)=f i (p,x)):
    NativeJointPhysicalGammaInput.process 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg
      c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb x=
    NativeJointPhysicalGammaInput.process 𝓕 v b hκ hm μ H hbH hb1 B hB f hfm hf
      c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb x:=by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [NativeJointPhysicalGammaInput.process_ae 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg
      c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb x,
    NativeJointPhysicalGammaInput.process_ae 𝓕 v b hκ hm μ H hbH hb1 B hB f hfm hf
      c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb x,he] with p hg hf he
  rw [hg,hf]
  exact raw_eq v b hκ hm g f c0 c1 r0 r1 d p x he
end SHE.NativeGammaInputCongruence
