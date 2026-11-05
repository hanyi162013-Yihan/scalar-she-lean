module

public import SHE.MovingPastFractional

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.MovingParameterFractional
open Set MeasureTheory
open scoped ENNReal
variable {T:Type*} [MeasurableSpace T]

/-- Moving-past translation with the ENTIRE original old-time array
as parameter. The current clock may depend on every old time. -/
theorem current (ν:Measure T) [SFinite ν] (K:T→ℝ≥0∞) (q:T→ℝ)
    (F:ℝ→ℝ≥0∞) (hK:Measurable K) (hq:Measurable q) (hF:Measurable F)
    {χ:ℝ} (hχ:0≤χ) (hχ1:χ≤1) (H:ℝ):
    (∫⁻ v in Ioc (0:ℝ) H,∫⁻ t,K t*MovingPastFractional.powerWindow H χ F (v+q t) ∂ν)≤
      (∫⁻ t,K t ∂ν)*((∫⁻ r in Ioc (0:ℝ) H,F r)^χ*(ENNReal.ofReal H)^(1-χ)):=by
  let G:=MovingPastFractional.powerWindow H χ F
  have hG:Measurable G:=MovingPastFractional.powerWindow_measurable hF H χ
  calc
    _=(∫⁻ t,(∫⁻ v in Ioc (0:ℝ) H,K t*G (v+q t)) ∂ν):=by
      apply lintegral_lintegral_swap
      exact ((hK.comp measurable_snd).mul
        (hG.comp (measurable_fst.add (hq.comp measurable_snd)))).aemeasurable
    _≤∫⁻ t,(∫⁻ v:ℝ,K t*G (v+q t)) ∂ν:=by
      apply lintegral_mono
      intro t
      exact lintegral_mono' Measure.restrict_le_self le_rfl
    _=(∫⁻ t,K t ∂ν)*(∫⁻ r:ℝ,G r):=by
      have he(t):(∫⁻ v:ℝ,K t*G (v+q t))=K t*(∫⁻ r:ℝ,G r):=by
        have hmq:Measurable (fun v:ℝ=>G (v+q t)):=hG.comp (measurable_id.add_const (q t))
        rw [lintegral_const_mul _ hmq,lintegral_add_right_eq_self]
      simp only [he]
      exact lintegral_mul_const _ hK
    _≤_:=by
      gcongr
      exact MovingPastFractional.powerWindow_mass hF hχ hχ1 H

theorem past (ν:Measure T) [SFinite ν] (K:T→ℝ≥0∞) (F:ℝ→ℝ≥0∞)
    (hK:Measurable K) (hF:Measurable F)
    {χ:ℝ} (hχ:0≤χ) (hχ1:χ≤1) (H:ℝ):
    (∫⁻ v in Ioc (0:ℝ) H,∫⁻ t,K t*(F v)^χ ∂ν)≤
      (∫⁻ t,K t ∂ν)*((∫⁻ r in Ioc (0:ℝ) H,F r)^χ*(ENNReal.ofReal H)^(1-χ)):=by
  have he(v):(∫⁻ t,K t*(F v)^χ ∂ν)=(∫⁻ t,K t ∂ν)*(F v)^χ:=lintegral_mul_const _ hK
  simp_rw [he]
  rw [lintegral_const_mul _ (hF.pow_const χ)]
  gcongr
  have hh:=FiniteMomentFractional.lintegral_fraction_mass
    (μ:=volume.restrict (Ioc (0:ℝ) H)) hF.aemeasurable hχ hχ1
  simpa only [Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioc,sub_zero] using hh

end SHE.MovingParameterFractional
