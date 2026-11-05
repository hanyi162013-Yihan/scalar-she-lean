module

public import SHE.InitialRetainedTriangleEnergy
public import SHE.RetainedTerminalAllFrequency

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.InitialCompleteTimePatch
open Classical Set MeasureTheory Real
open scoped ENNReal
variable {Y:Type*} [MeasurableSpace Y]

/-- Initial outputs and complete moving windows cover the entire
original output interval. No strip is set to zero. -/
def field (h:ℝ) (I M:ℝ×Y→ℝ) (z:ℝ×Y):ℝ:=
  if z.1≤h then I z else M (z.1-h,z.2)

theorem field_measurable (h:ℝ) (I M:ℝ×Y→ℝ) (hI:Measurable I) (hM:Measurable M):
    Measurable (field h I M):=
  hI.ite (measurableSet_le measurable_fst measurable_const)
    (hM.comp ((measurable_fst.sub_const h).prodMk measurable_snd))

/-- Exact output-time transport gives the SUM of the two genuine
space/sample energies, before any negative-output contraction. -/
theorem energy (μ:Measure Y) [SFinite μ] {h H:ℝ} (hh:0≤h)
    (I M:ℝ×Y→ℝ) (hI:Measurable I) (hM:Measurable M)
    (hi:Integrable (fun z=>|I z|^2) ((volume.restrict (Ioc 0 H)).prod μ))
    (hm:Integrable (fun z=>|M z|^2) ((volume.restrict (Ioc 0 H)).prod μ)):
    Integrable (fun z=>|field h I M z|^2) ((volume.restrict (Ioc 0 H)).prod μ) ∧
      (∫z,|field h I M z|^2 ∂(volume.restrict (Ioc 0 H)).prod μ)≤
        (∫z,|I z|^2 ∂(volume.restrict (Ioc 0 H)).prod μ)+
          (∫z,|M z|^2 ∂(volume.restrict (Ioc 0 H)).prod μ):=by
  let A:ℝ→ℝ≥0∞:=fun t=>∫⁻y,ENNReal.ofReal (|I (t,y)|^2) ∂μ
  let B:ℝ→ℝ≥0∞:=fun t=>∫⁻y,ENNReal.ofReal (|M (t,y)|^2) ∂μ
  have hAm:Measurable A:=(ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp hI).pow_const 2)).lintegral_prod_right'
  have hBm:Measurable B:=(ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp hM).pow_const 2)).lintegral_prod_right'
  let C:ℝ→ℝ≥0∞:=(Ioc 0 H).indicator B
  have hCm:Measurable C:=hBm.indicator measurableSet_Ioc
  have hshift:(∫⁻t in Ioc (0:ℝ) H,C (t-h))≤∫⁻t in Ioc (0:ℝ) H,B t:=by
    calc
      _≤∫⁻t:ℝ,C (t-h):=lintegral_mono' Measure.restrict_le_self le_rfl
      _=∫⁻t:ℝ,C t:=by simpa only [sub_eq_add_neg] using lintegral_add_right_eq_self (fun t:ℝ=>C t) (-h)
      _=∫⁻t in Ioc (0:ℝ) H,B t:=lintegral_indicator measurableSet_Ioc B
  have hpoint:∀ᵐt∂volume.restrict (Ioc (0:ℝ) H),
      (∫⁻y,ENNReal.ofReal (|field h I M (t,y)|^2) ∂μ)≤A t+C (t-h):=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    by_cases hth:t≤h
    · simp only [field,if_pos hth]
      exact le_add_right le_rfl
    · have hc:t-h∈Ioc (0:ℝ) H:=⟨sub_pos.mpr (lt_of_not_ge hth),by linarith [ht.2]⟩
      simp only [field,if_neg hth,C,indicator_of_mem hc]
      exact le_add_left le_rfl
  have hsum:(∫⁻t in Ioc (0:ℝ) H,∫⁻y,ENNReal.ofReal (|field h I M (t,y)|^2) ∂μ)≤
      (∫⁻t in Ioc (0:ℝ) H,A t)+(∫⁻t in Ioc (0:ℝ) H,B t):=by
    apply (lintegral_mono_ae hpoint).trans
    rw [lintegral_add_left hAm]
    exact add_le_add le_rfl hshift
  have hf:Measurable (fun z:ℝ×Y=>|field h I M z|^2):=
    (continuous_abs.measurable.comp (field_measurable h I M hI hM)).pow_const 2
  have hreal:(∫⁻z:ℝ×Y,ENNReal.ofReal (|field h I M z|^2) ∂(volume.restrict (Ioc 0 H)).prod μ)≤
      ENNReal.ofReal ((∫z,|I z|^2 ∂(volume.restrict (Ioc 0 H)).prod μ)+
        (∫z,|M z|^2 ∂(volume.restrict (Ioc 0 H)).prod μ)):=by
    have hIA:(∫⁻t in Ioc (0:ℝ) H,A t)=ENNReal.ofReal (∫z,|I z|^2 ∂(volume.restrict (Ioc 0 H)).prod μ):=by
      calc
        _=∫⁻z:ℝ×Y,ENNReal.ofReal (|I z|^2) ∂(volume.restrict (Ioc 0 H)).prod μ:=by
          symm
          apply lintegral_prod
          convert! (ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp hI).pow_const 2)).aemeasurable using 1
        _=_:=(ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _=>sq_nonneg _))).symm
    have hMB:(∫⁻t in Ioc (0:ℝ) H,B t)=ENNReal.ofReal (∫z,|M z|^2 ∂(volume.restrict (Ioc 0 H)).prod μ):=by
      calc
        _=∫⁻z:ℝ×Y,ENNReal.ofReal (|M z|^2) ∂(volume.restrict (Ioc 0 H)).prod μ:=by
          symm
          apply lintegral_prod
          convert! (ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp hM).pow_const 2)).aemeasurable using 1
        _=_:=(ofReal_integral_eq_lintegral_ofReal hm (ae_of_all _ (fun _=>sq_nonneg _))).symm
    calc
      _=∫⁻t in Ioc (0:ℝ) H,∫⁻y,ENNReal.ofReal (|field h I M (t,y)|^2) ∂μ:=by
        apply lintegral_prod
        convert! (ENNReal.measurable_ofReal.comp hf).aemeasurable using 1
      _≤_:=hsum
      _=_:=by rw [hIA,hMB,ENNReal.ofReal_add
        (integral_nonneg (fun _=>sq_nonneg _)) (integral_nonneg (fun _=>sq_nonneg _))]
  have hfi:Integrable (fun z=>|field h I M z|^2) ((volume.restrict (Ioc 0 H)).prod μ):=by
    refine ⟨hf.aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _))]
    exact hreal.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hfi,(ENNReal.ofReal_le_ofReal_iff (add_nonneg
    (integral_nonneg (fun _=>sq_nonneg _)) (integral_nonneg (fun _=>sq_nonneg _)))).mp ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ (fun _=>sq_nonneg _))]
  exact hreal

end SHE.InitialCompleteTimePatch
