module
public import SHE.NativeJointGammaFourierColumns
public import SHE.NativeFourierRowAverage
public import SHE.NativeJointGammaSpatialIntegral
public import SHE.NativeConvexGammaEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.NativeJointGammaFourierAverage
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
variable {Λ ρ:ℝ}(hΛ:1≤Λ)(hρ:0<ρ)(hρhalf:ρ<1/2)(hb1:(b:ℝ)≤1)
variable {κ m U:ℝ}(hκ:0<κ)(hm:0<m)
variable (B:ℝ)(hB:0≤B)(g:Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ)
variable (hgm:∀i,@Measurable _ ℂ (𝓕.predictable.prod inferInstance) _ (g i))
variable (hg:∀i p x,‖g i (p,x)‖≤B)(hr:∀i p x,(g i (p,x)).im=0)
variable (c0 c1 r0 r1:ℝ≥0×Ω→EllipticField m U)
variable (hc0:Measurable[𝓕.predictable] c0)(hc1:Measurable[𝓕.predictable] c1)
variable (hr0:Measurable[𝓕.predictable] r0)(hr1:Measurable[𝓕.predictable] r1)
variable (d:ℝ≥0×Ω→ℝ)(hd:Measurable[𝓕.predictable] d)(hdb:∀p,0≤d p ∧ d p≤1)
local notation "Raw"=>NativeJointPhysicalGammaInput.raw v b hκ hm g c0 c1 r0 r1 d

local notation "Const"=>(fun _:ℝ≥0×Ω=>AdditiveHaarForcing.constantField κ hκ)
local notation "K0"=>NativePairedGammaProcess.field 𝓕 v b hb1 hΛ hρ.le hρhalf hκ B g hgm hg Const Const Const Const
local notation "K1"=>NativeConvexGammaProcess.field 𝓕 v b hb1 hΛ hρ.le hρhalf hm B g hgm hg d c0 c1 r0 r1

include hB hgm hg hr hc0 hc1 hr0 hr1 hd hdb in
/-- Exact spatial Bochner identity for the complete original two-channel
row and every real linear Fourier coordinate. -/
theorem row (p:ℝ≥0×Ω)(l:ℤ)(a:ℂ→L[ℝ]ℝ):
    WithLp.toLp 2 (HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (K0 p),
      HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (K1 p))=
      ∫x:HeatCircle,((Λ+(l:ℝ)^2)^(-ρ/2)*a (fourier (-l) x)) • Raw (p,x) ∂haarAddCircle:=by
  exact NativeFourierRowAverage.row (fun x=>Raw (p,x))
    (NativeJointGammaSpatialIntegral.integrable 𝓕 v b hκ hm B hB g hgm hg c0 c1 r0 r1
      hc0 hc1 hr0 hr1 d hd hdb p) (K0 p) (K1 p) a l ((Λ+(l:ℝ)^2)^(-ρ/2))
    (fun k=>NativeJointGammaFourierColumns.additive 𝓕 v b hb1 hΛ hρ.le hρhalf hκ hm B g hgm hg hr
      c0 c1 r0 r1 d p k l)
    (fun k=>NativeJointGammaFourierColumns.residual 𝓕 v b hb1 hΛ hρ.le hρhalf hκ hm B g hgm hg hr
      c0 c1 r0 r1 d p k l)

include hB hgm hg hr hc0 hc1 hr0 hr1 hd hdb in
theorem real (p:ℝ≥0×Ω)(l:ℤ):
    NativeFourierNoiseRows.bothReal l (K0 p) (K1 p)=
      ∫x:HeatCircle,((Λ+(l:ℝ)^2)^(-ρ/2)*(fourier (-l) x).re) • Raw (p,x) ∂haarAddCircle:=
  row 𝓕 v b hΛ hρ hρhalf hb1 hκ hm B hB g hgm hg hr c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb p l Complex.reCLM

include hB hgm hg hr hc0 hc1 hr0 hr1 hd hdb in
theorem imag (p:ℝ≥0×Ω)(l:ℤ):
    NativeFourierNoiseRows.bothImag l (K0 p) (K1 p)=
      ∫x:HeatCircle,((Λ+(l:ℝ)^2)^(-ρ/2)*(fourier (-l) x).im) • Raw (p,x) ∂haarAddCircle:=
  row 𝓕 v b hΛ hρ hρhalf hb1 hκ hm B hB g hgm hg hr c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb p l Complex.imCLM
end SHE.NativeJointGammaFourierAverage
