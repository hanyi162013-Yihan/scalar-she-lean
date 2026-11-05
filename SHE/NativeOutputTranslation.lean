module

public import SHE.NativeKernelAction

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeOutputTranslation
open MeasureTheory AddCircle Real StoppedFourier NativeRandomKernel
open scoped ENNReal
local instance nativeOutputTranslation_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩

def translate (a : HeatCircle) : CircleL2 →ₗᵢ[ℂ] CircleL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x-a) (measurePreserving_sub_right haarAddCircle a)

theorem translate_ae (a : HeatCircle) (f : CircleL2) :
    (translate a f : HeatCircle → ℂ)=ᵐ[haarAddCircle] fun x => f (x-a) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right haarAddCircle a)

theorem fourierCoeff_translate (a : HeatCircle) (f : CircleL2) (n : ℤ) :
    fourierCoeff (translate a f) n=fourier (-n) a*fourierCoeff f n := by
  unfold fourierCoeff
  calc
    _ = ∫ x : HeatCircle, fourier (-n) x*f (x-a) ∂haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [translate_ae a f] with x hx
      rw [hx,smul_eq_mul]
    _ = ∫ x : HeatCircle, fourier (-n) (x+a)*f x ∂haarAddCircle := by
      have hh := integral_add_right_eq_self (μ:=haarAddCircle)
        (fun x : HeatCircle => fourier (-n) x*f (x-a)) a
      simpa only [add_sub_cancel_right] using hh.symm
    _ = _ := by
      have hadd (x : HeatCircle) : fourier (-n) (x+a)=fourier (-n) x*fourier (-n) a := by
        simp only [fourier_apply,zsmul_add,AddCircle.toCircle_add,Circle.coe_mul]
      simp_rw [hadd,mul_right_comm _ (fourier (-n) a),mul_comm _ (fourier (-n) a)]
      rw [integral_const_mul]
      rfl

/-- A fixed output translation preserves the actual negative-output
energy. This does not translate or otherwise alter the signed input. -/
theorem bessel_norm_translate {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (a : HeatCircle) (f : CircleL2) :
    ‖OneInputOperator.besselHalf Λ ρ hΛ hρ (translate a f)‖=
      ‖OneInputOperator.besselHalf Λ ρ hΛ hρ f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [OneInputOperator.norm_sq_fourier,OneInputOperator.norm_sq_fourier]
  apply tsum_congr
  intro n
  rw [OneInputOperator.besselHalf_fourierCoeff,OneInputOperator.besselHalf_fourierCoeff,
    fourierCoeff_translate,norm_mul,norm_mul,norm_mul,
    show ‖fourier (-n) a‖=1 from Circle.norm_coe _,one_mul]

def shiftedOutput {Ω : Type*} (a : HeatCircle)
    (F : Ω × (HeatCircle × HeatCircle) → ℂ) (p : Ω × (HeatCircle × HeatCircle)) : ℂ :=
  F (p.1,(p.2.1,p.2.2-a))

theorem shiftedOutput_measurable {Ω : Type*} [MeasurableSpace Ω] (a : HeatCircle)
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F) : Measurable (shiftedOutput a F) :=
  hF.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk (measurable_snd.snd.sub measurable_const)))

theorem operator_shiftedOutput {Ω : Type*} [MeasurableSpace Ω] (a : HeatCircle)
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) (ω : Ω) :
    integralOperator (shiftedOutput a F) ω=
      (translate a).toContinuousLinearMap.comp (integralOperator F ω) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  have ha := (measurePreserving_sub_right (haarAddCircle (T:=2*π)) a).quasiMeasurePreserving.ae
    (integralOperator_ae hF hB hb ω v)
  filter_upwards [integralOperator_ae (shiftedOutput_measurable a hF) hB (fun ω y x => hb ω y (x-a)) ω v,
    translate_ae a (integralOperator F ω v),ha] with x hl ht hr
  change integralOperator (shiftedOutput a F) ω v x=translate a (integralOperator F ω v) x
  rw [hl,ht,hr]
  rfl

theorem bessel_norm_shiftedOutput {Ω : Type*} [MeasurableSpace Ω] (a : HeatCircle)
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) (ω : Ω)
    {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (v : CircleL2) :
    ‖OneInputOperator.besselHalf Λ ρ hΛ hρ (integralOperator (shiftedOutput a F) ω v)‖=
      ‖OneInputOperator.besselHalf Λ ρ hΛ hρ (integralOperator F ω v)‖ := by
  rw [operator_shiftedOutput a hF hB hb ω]
  exact bessel_norm_translate hΛ hρ a _

end SHE.NativeOutputTranslation
