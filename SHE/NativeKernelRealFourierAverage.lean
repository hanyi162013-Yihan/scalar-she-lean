module
public import SHE.NativeKernelFourierIntegral
public import SHE.KernelAverageFubini
public import SHE.NativeRealNoise

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.NativeKernelRealFourierAverage
open MeasureTheory AddCircle StoppedFourier NativeFourierNoiseRows
open scoped ENNReal
local instance nativeKernelRealFourierAverage_period:Fact (0<2*Real.pi):=⟨by positivity⟩
variable {A:Type*}[MeasurableSpace A]

/-- Absolute old-space/output integrability is supplied by the finite
physical kernel cap before the signed scalar coordinates are combined. -/
theorem actions_integrable (ν:Measure A)[IsFiniteMeasure ν]
    {F:A×(HeatCircle×HeatCircle)→ℂ}(hF:Measurable F)
    {B:ℝ}(hB:0≤B)(hb:∀a y x,‖F (a,(y,x))‖≤B)(f:CircleL2):
    Integrable (fun z:A×HeatCircle=>(∫y:HeatCircle,F (z.1,(y,z.2))*f y ∂haarAddCircle).re)
      (ν.prod haarAddCircle):=by
  have hm:Measurable (fun z:HeatCircle×(A×HeatCircle)=>F (z.2.1,(z.1,z.2.2))*f z.1):=
    (hF.comp (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))).mul
      ((Lp.stronglyMeasurable f).measurable.comp measurable_fst)
  have hR:=Complex.continuous_re.measurable.comp
    (hm.stronglyMeasurable.integral_prod_left' (μ:=haarAddCircle)).measurable
  have hv:Integrable (fun y:HeatCircle=>‖f y‖) haarAddCircle:=
    ((Lp.memLp f).integrable (by norm_num:(1:ENNReal)≤2)).norm
  apply (integrable_const (B*∫y:HeatCircle,‖f y‖ ∂haarAddCircle)).mono' hR.aestronglyMeasurable
  refine ae_of_all _ (fun z=>?_)
  change |(∫y:HeatCircle,F (z.1,(y,z.2))*f y ∂haarAddCircle).re|≤_
  calc
    _≤‖∫y:HeatCircle,F (z.1,(y,z.2))*f y ∂haarAddCircle‖:=Complex.abs_re_le_norm _
    _≤∫y:HeatCircle,B*‖f y‖ ∂haarAddCircle:=
      norm_integral_le_of_norm_le (hv.const_mul B) (ae_of_all _ (fun y=>by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hb z.1 y z.2) (norm_nonneg _)))
    _=_:=integral_const_mul _ _

/-- Real physical kernels and real native inputs have a genuinely real
scalar action, independently of the chosen L2 representative. -/
theorem integral_real (G:HeatCircle→ℂ)(hG:∀y,(G y).im=0)
    (f:CircleL2)(hf:∀ᵐy∂haarAddCircle,(f y).im=0):
    (∫y:HeatCircle,G y*f y ∂haarAddCircle)=
      ((∫y:HeatCircle,G y*f y ∂haarAddCircle).re:ℂ):=by
  have he:∀ᵐy∂haarAddCircle,G y*f y=(((G y*f y).re:ℝ):ℂ):=by
    filter_upwards [hf] with y hy
    apply Complex.ext
    · rfl
    · simp [Complex.mul_im,hG y,hy]
  have hi:(∫y:HeatCircle,G y*f y ∂haarAddCircle)=
      ((∫y:HeatCircle,(G y*f y).re ∂haarAddCircle:ℝ):ℂ):=
    (integral_congr_ae he).trans integral_complex_ofReal
  calc
    _=_:=hi
    _=_:=by
      congr 1
      simpa only [Complex.ofReal_re] using (congrArg Complex.re hi).symm

/-- The actual old-space average and each native Bessel Fourier
coordinate commute, with the real original scalar coordinate retained.
The finite spatial cap supplies the absolute Fubini applicability. -/
theorem coefficient_average (ν:Measure A)[IsFiniteMeasure ν]
    {F:A×(HeatCircle×HeatCircle)→ℂ}(hF:Measurable F)
    {B:ℝ}(hB:0≤B)(hb:∀a y x,‖F (a,(y,x))‖≤B)
    (hr:∀a y x,(F (a,(y,x))).im=0)
    (f:CircleL2)(hf:∀ᵐy∂haarAddCircle,(f y).im=0)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(l:ℤ):
    let G:Unit×(HeatCircle×HeatCircle)→ℂ:=fun z=>∫a,F (a,z.2) ∂ν
    coefficient l (OneInputOperator.besselHalf mass ρ hmass hρ
      (NativeRandomKernel.integralOperator G () f))=
      (((mass+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*
        ∫x:HeatCircle,fourier (-l) x*
          ((∫a,(∫y:HeatCircle,F (a,(y,x))*f y ∂haarAddCircle).re ∂ν:ℝ):ℂ) ∂haarAddCircle:=by
  intro G
  have hG:Measurable G:=by
    exact (hF.stronglyMeasurable.integral_prod_left').measurable.comp measurable_snd
  have hbG:∀p y x,‖G (p,(y,x))‖≤B*ν.real Set.univ:=by
    intro p y x
    exact norm_integral_le_of_norm_le_const (ae_of_all _ (fun a=>hb a y x))
  have hBG:0≤B*ν.real Set.univ:=mul_nonneg hB (measureReal_nonneg)
  rw [NativeKernelFourierIntegral.operator_coefficient hG hBG hbG hmass hρ () f l]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  have hFx:Measurable (fun z:A×HeatCircle=>F (z.1,(z.2,x))):=
    hF.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  rw [KernelAverageFubini.integral_average_mul ν hFx hB (fun a y=>hb a y x) f]
  calc
    _=∫a,(((∫y:HeatCircle,F (a,(y,x))*f y ∂haarAddCircle).re:ℝ):ℂ) ∂ν:=by
      apply integral_congr_ae
      exact ae_of_all _ (fun a=>integral_real _ (fun y=>hr a y x) f hf)
    _=_:=integral_complex_ofReal

end SHE.NativeKernelRealFourierAverage
