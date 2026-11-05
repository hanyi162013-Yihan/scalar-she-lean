module
public import SHE.NativeGammaConvexFourier
public import SHE.NativeJointGammaCoordinates
public import SHE.NativeConvexGammaProcess
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.NativeJointGammaFourierColumns
open Set MeasureTheory FiniteHaar StoppedFourier AddCircle
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(v b:ℝ≥0)(hb1:(b:ℝ)≤1)
variable {Λ ρ m U κ:ℝ}(hΛ:1≤Λ)(hρ:0≤ρ)(hρhalf:ρ<1/2)(hκ:0<κ)(hm:0<m)
variable (B:ℝ)(g:Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ)
variable (hgm:∀i,@Measurable _ _ (𝓕.predictable.prod inferInstance) _ (g i))
variable (hg:∀i p x,‖g i (p,x)‖≤B)(hr:∀i p x,(g i (p,x)).im=0)
variable (c0 c1 r0 r1:ℝ≥0×Ω→EllipticField m U)(d:ℝ≥0×Ω→ℝ)
local notation "Const"=>(fun _:ℝ≥0×Ω=>AdditiveHaarForcing.constantField κ hκ)
local notation "K0"=>NativePairedGammaProcess.field 𝓕 v b hb1 hΛ hρ hρhalf hκ B g hgm hg Const Const Const Const
local notation "K1"=>NativeConvexGammaProcess.field 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hg d c0 c1 r0 r1
local notation "Raw"=>NativeJointPhysicalGammaInput.raw v b hκ hm g c0 c1 r0 r1 d

theorem row_age {ell M:ℝ}(hell:0<ell)(f:EllipticField ell M)(p:ℝ≥0×Ω)
    (hp:p∈NativeGammaClock.window v b)(x:HeatCircle):
    NativeObservationCovariance.row hell f (NativeGammaClock.age v b p) 0 x=
      NativeObservationCovariance.row hell f b p.1 x:=by
  unfold NativeObservationCovariance.row
  rw [show NativeGammaClock.age v b p=(b:ℝ)-(p.1:ℝ) from if_pos hp,sub_zero]

include hr in
/-- The additive native Fourier column is exactly the Fourier average
of the unchanged additive coordinate of the ORIGINAL scalar Gamma row. -/
theorem additive (p:ℝ≥0×Ω)(k:HaarNode)(l:ℤ):
    NativeFourierNoiseRows.coefficient l (K0 p k)=
      (((Λ+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*∫x:HeatCircle,fourier (-l) x*
        (NativeJointColumnDirections.left k (Raw (p,x)):ℂ) ∂haarAddCircle:=by
  classical
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  by_cases hp:p∈NativeGammaClock.window v b
  · rw [NativePairedGammaProcess.field,indicator_of_mem hp,
      NativeGammaPairedFourier.coefficient]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    rw [NativeJointGammaCoordinates.left_active v b hκ hm g c0 c1 r0 r1 d p hp x]
    simp only [row_age v b hκ _ p hp x]
    have he:∀i:Fin 6,g i (p,x)=((g i (p,x)).re:ℂ):=fun i=>Complex.ext rfl (by simpa only [Complex.ofReal_im] using hr i p x)
    rw [he 0,he 3,he 2,he 5]
    simp only [Complex.ofReal_re,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_sub]
    ring
  · simp only [NativePairedGammaProcess.field,indicator_of_notMem hp,
      lp.coeFn_zero,Pi.zero_apply,map_zero]
    have hz:∀x:HeatCircle,Raw (p,x)=0:=fun x=>NativeJointGammaCoordinates.inactive v b hκ hm g c0 c1 r0 r1 d p hp x
    simp only [hz,map_zero,Complex.ofReal_zero,mul_zero,integral_zero]
include hr in
/-- The complete convex residual Hilbert column is exactly the Fourier
average of the SAME original scalar residual input, including its
predictable damper inside the original common-Haar integral. -/
theorem residual (p:ℝ≥0×Ω)(k:HaarNode)(l:ℤ):
    NativeFourierNoiseRows.coefficient l (K1 p k)=
      (((Λ+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*∫x:HeatCircle,fourier (-l) x*
        (NativeJointColumnDirections.right k (Raw (p,x)):ℂ) ∂haarAddCircle:=by
  classical
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  by_cases hp:p∈NativeGammaClock.window v b
  · rw [NativeConvexGammaProcess.field]
    simp only [NativePairedGammaProcess.field,indicator_of_mem hp]
    rw [NativeGammaConvexFourier.coefficient]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    rw [NativeJointGammaCoordinates.right_active v b hκ hm g c0 c1 r0 r1 d p hp x]
    simp only [NativeGammaConvexFourier.physical]
    rw [row_age v b hm (c0 p) p hp x,row_age v b hm (c1 p) p hp x,
      row_age v b hm (r0 p) p hp x,row_age v b hm (r1 p) p hp x]
    have he:∀i:Fin 6,g i (p,x)=((g i (p,x)).re:ℂ):=fun i=>Complex.ext rfl (by simpa only [Complex.ofReal_im] using hr i p x)
    rw [he 0,he 3,he 2,he 5]
    simp only [Algebra.smul_def,Complex.ofReal_re,Complex.ofReal_mul,Complex.ofReal_add,
      Complex.ofReal_sub,Complex.ofReal_one]
    have hmap (a:ℝ):(algebraMap ℝ ℂ) a=(a:ℂ):=rfl
    simp only [hmap,Complex.ofReal_sub,Complex.ofReal_one]
    ring
  · simp only [NativeConvexGammaProcess.field,NativePairedGammaProcess.field,indicator_of_notMem hp,
      smul_zero,add_zero,lp.coeFn_zero,Pi.zero_apply,map_zero]
    have hz:∀x:HeatCircle,Raw (p,x)=0:=fun x=>NativeJointGammaCoordinates.inactive v b hκ hm g c0 c1 r0 r1 d p hp x
    simp only [hz,map_zero,Complex.ofReal_zero,mul_zero,integral_zero]
end SHE.NativeJointGammaFourierColumns
