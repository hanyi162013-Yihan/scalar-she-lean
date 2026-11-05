module
public import SHE.NativeKernelHaarColumns
public import SHE.RawKernelColumns
public import SHE.NativeKernelAction
public import SHE.NativeMultiplierFourierIntegral
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.NativeKernelFourierIntegral
open MeasureTheory AddCircle StoppedFourier FiniteHaar NativeRandomKernel NativeFourierNoiseRows
open scoped NNReal ENNReal
local instance nativeKernelFourierIntegral_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeKernelFourierIntegral_p:Fact (1≤(2:ENNReal)):=⟨by norm_num⟩
variable {W:Type*}[MeasurableSpace W]

/-- The Fourier coefficient of the literal negative-output kernel
column is its original scalar spatial input, with the native Bessel
weight retained exactly. -/
theorem operator_coefficient {F:W×(HeatCircle×HeatCircle)→ℂ}(hF:Measurable F)
    {B:ℝ}(hB:0≤B)(hb:∀p y x,‖F (p,(y,x))‖≤B)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(p:W)(f:CircleL2)(l:ℤ):
    coefficient l (OneInputOperator.besselHalf mass ρ hmass hρ (integralOperator F p f))=
      (((mass+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*
        ∫x:HeatCircle,fourier (-l) x*(∫y:HeatCircle,F (p,(y,x))*f y ∂haarAddCircle) ∂haarAddCircle:=by
  rw [NativeMultiplierFourierIntegral.coefficient_apply,OneInputOperator.besselHalf_fourierCoeff]
  congr 1
  unfold fourierCoeff
  apply integral_congr_ae
  filter_upwards [integralOperator_ae hF hB hb p f] with x hx
  rw [hx]
  rfl

theorem haar_column_coefficient {F:W×(HeatCircle×HeatCircle)→ℂ}(hF:Measurable F)
    {B:ℝ}(hB:0≤B)(hb:∀p y x,‖F (p,(y,x))‖≤B)
    {mass ρ m Upper:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(hm:0<m)
    (c:W→EllipticField m Upper)(p:W)(j:HaarNode)(l:ℤ):
    coefficient l (NativeKernelHaarColumns.columns hmass hρ hm hF (fun p=>⟨B,hb p⟩) c p j)=
      (((mass+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*
        ∫x:HeatCircle,fourier (-l) x*(∫y:HeatCircle,F (p,(y,x))*
          CircleNormalization.push (globalHaarColumn j (c p).1) y ∂haarAddCircle) ∂haarAddCircle:=by
  exact operator_coefficient hF hB hb hmass hρ p _ l

theorem signed_column_coefficient {F:W×(HeatCircle×HeatCircle)→ℂ}(hF:Measurable F)
    {B:ℝ}(hB:0≤B)(hb:∀p y x,‖F (p,(y,x))‖≤B)
    {mass ρ m Upper:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(hm:0<m)
    (c d:W→EllipticField m Upper)(p:W)(j:HaarNode)(l:ℤ):
    coefficient l (SignedKernelColumns.rawColumns F mass ρ hmass hρ m Upper hm c d p j)=
      (((mass+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*
        ∫x:HeatCircle,fourier (-l) x*(∫y:HeatCircle,F (p,(y,x))*
          CircleNormalization.push (globalHaarColumn j (d p).1-globalHaarColumn j (c p).1) y
            ∂haarAddCircle) ∂haarAddCircle:=by
  rw [SignedKernelColumns.rawColumns_apply]
  exact operator_coefficient hF hB hb hmass hρ p _ l

/-- Genuine old-time Hilbert integration commutes with each scalar
Fourier/Haar coordinate. The original L1 applicability is explicit. -/
theorem average_coefficient (ν:Measure W)(K:W→NativeKernelHaarColumns.Space)
    (hK:Integrable K ν)(j:HaarNode)(l:ℤ):
    coefficient l ((∫t,K t ∂ν) j)=∫t,coefficient l (K t j) ∂ν:=by
  exact (((coefficient l).comp (lp.evalCLM ℝ (fun _:HaarNode=>CircleL2) 2 j)).integral_comp_comm hK).symm

end SHE.NativeKernelFourierIntegral
