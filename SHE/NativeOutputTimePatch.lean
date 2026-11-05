module
public import SHE.MovingClockEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.NativeOutputTimePatch
open Classical Set MeasureTheory PredictableL2
open scoped NNReal ENNReal

private theorem partition (H h:ℝ)(hh:0≤h)(hhH:h≤H)(A B:ℝ→ℝ≥0∞):
    (∫⁻t in Ioc (0:ℝ) H,if t≤h then A t else B (t-h))=
      (∫⁻t in Ioc (0:ℝ) h,A t)+(∫⁻v in Ioc (0:ℝ) (H-h),B v):=by
  have h₁:Iic h∩Ioc (0:ℝ) H=Ioc 0 h:=by
    ext t
    simp only [mem_inter_iff,mem_Iic,mem_Ioc]
    constructor
    · rintro ⟨ht,ht0,_⟩
      exact ⟨ht0,ht⟩
    · intro ht
      exact ⟨ht.2,ht.1,ht.2.trans hhH⟩
  have h₂:(Iic h)ᶜ∩Ioc (0:ℝ) H=Ioc h H:=by
    ext t
    simp only [mem_inter_iff,mem_compl_iff,mem_Iic,not_le,mem_Ioc]
    constructor
    · exact fun ht=>⟨ht.1,ht.2.2⟩
    · exact fun ht=>⟨ht.1,lt_of_le_of_lt hh ht.1,ht.2⟩
  have he:(∫⁻t in Ioc (0:ℝ) H,if t≤h then A t else B (t-h))=
      (∫⁻t in Ioc (0:ℝ) h,A t)+(∫⁻t in Ioc h H,B (t-h)):=by
    change (∫⁻t,(Iic h).piecewise A (fun t=>B (t-h)) t ∂volume.restrict (Ioc (0:ℝ) H))=_
    rw [lintegral_piecewise measurableSet_Iic.nullMeasurableSet,
      Measure.restrict_restrict measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic.compl,h₁,h₂]
  rw [he]
  congr 1
  have ht:=(MovingClockEnergy.translation h (H-h)).lintegral_comp_emb
    (MeasurableEquiv.addRight h).measurableEmbedding (fun t=>B (t-h))
  have hsum:h+(H-h)=H:=by ring
  simpa only [hsum,MeasurableEquiv.coe_addRight,add_sub_cancel_right] using ht.symm

variable {Ω E:Type*}[MeasurableSpace Ω][NormedAddCommGroup E]
  [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]

/-- The native output uses its real initial strip and then the complete
past window; both are fields on the same original time/sample clock. -/
def field(h:ℝ≥0)(I M:ℝ≥0×Ω→E)(z:ℝ≥0×Ω):E:=
  if z.1≤h then I z else M (z.1-h,z.2)

theorem measurable(h:ℝ≥0)(I M:ℝ≥0×Ω→E)(hI:Measurable I)(hM:Measurable M):
    Measurable (field h I M):=
  hI.ite (measurableSet_le measurable_fst measurable_const)
    (hM.comp ((measurable_fst.sub_const h).prodMk measurable_snd))

/-- Exact transport of the initial and complete native energies. The
moving clock is translated before the norm is squared. -/
theorem mass (μ:Measure Ω)[SFinite μ](H h:ℝ≥0)(hhH:h≤H)
    (I M:ℝ≥0×Ω→E)(hI:Measurable I)(hM:Measurable M):
    (∫⁻z,ENNReal.ofReal (‖field h I M z‖^2) ∂energyMeasure μ H)=
      (∫⁻z,ENNReal.ofReal (‖I z‖^2) ∂energyMeasure μ h)+
        (∫⁻z,ENNReal.ofReal (‖M z‖^2) ∂energyMeasure μ (H-h)):=by
  let A:ℝ→ℝ≥0∞:=fun t=>∫⁻ω,ENNReal.ofReal (‖I (t.toNNReal,ω)‖^2) ∂μ
  let B:ℝ→ℝ≥0∞:=fun t=>∫⁻ω,ENNReal.ofReal (‖M (t.toNNReal,ω)‖^2) ∂μ
  have hIm:Measurable (fun z=>ENNReal.ofReal (‖I z‖^2)):=hI.norm.pow_const 2 |>.ennreal_ofReal
  have hMm:Measurable (fun z=>ENNReal.ofReal (‖M z‖^2)):=hM.norm.pow_const 2 |>.ennreal_ofReal
  have hFm:Measurable (fun z=>ENNReal.ofReal (‖field h I M z‖^2)):=
    (measurable h I M hI hM).norm.pow_const 2 |>.ennreal_ofReal
  have hIA:(∫⁻z,ENNReal.ofReal (‖I z‖^2) ∂energyMeasure μ h)=∫⁻t in Ioc (0:ℝ) (h:ℝ),A t:=by
    rw [energyMeasure,lintegral_prod _ hIm.aemeasurable,timeMeasure_lintegral]
  have hMB:(∫⁻z,ENNReal.ofReal (‖M z‖^2) ∂energyMeasure μ (H-h))=
      ∫⁻t in Ioc (0:ℝ) ((H:ℝ)-(h:ℝ)),B t:=by
    rw [energyMeasure,lintegral_prod _ hMm.aemeasurable,timeMeasure_lintegral,NNReal.coe_sub hhH]
  rw [hIA,hMB,energyMeasure,lintegral_prod _ hFm.aemeasurable,timeMeasure_lintegral]
  have he:(∫⁻t in Ioc (0:ℝ) (H:ℝ),∫⁻ω,ENNReal.ofReal (‖field h I M (t.toNNReal,ω)‖^2) ∂μ)=
      ∫⁻t in Ioc (0:ℝ) (H:ℝ),if t≤(h:ℝ) then A t else B (t-(h:ℝ)):=by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht':(t.toNNReal:ℝ)=t:=Real.coe_toNNReal _ ht.1.le
    by_cases hth:t≤(h:ℝ)
    · have htn:t.toNNReal≤h:=NNReal.coe_le_coe.mp (by simpa only [ht'] using hth)
      simp only [field,if_pos htn,if_pos hth,A]
    · have htn:¬t.toNNReal≤h:=by
        intro hh
        exact hth (by simpa only [ht'] using NNReal.coe_le_coe.mpr hh)
      have hle:h≤t.toNNReal:=le_of_lt (lt_of_not_ge htn)
      have hsub:t.toNNReal-h=(t-(h:ℝ)).toNNReal:=by
        ext
        rw [NNReal.coe_sub hle,ht',Real.coe_toNNReal _ (by linarith [lt_of_not_ge hth])]
      simp only [field,if_neg htn,if_neg hth,hsub,B]
  rw [he]
  exact partition (H:ℝ) (h:ℝ) h.2 (by exact_mod_cast hhH) A B

/-- The physical patch preserves genuine product L2 integrability and
has the sum of the two actual branch energies, with constant one. -/
theorem energy (μ:Measure Ω)[SFinite μ](H h:ℝ≥0)(hhH:h≤H)
    (I M:ℝ≥0×Ω→E)(hI:Measurable I)(hM:Measurable M)
    (hi:Integrable (fun z=>‖I z‖^2) (energyMeasure μ h))
    (hm:Integrable (fun z=>‖M z‖^2) (energyMeasure μ (H-h))):
    Integrable (fun z=>‖field h I M z‖^2) (energyMeasure μ H) ∧
      (∫z,‖field h I M z‖^2 ∂energyMeasure μ H)=
        (∫z,‖I z‖^2 ∂energyMeasure μ h)+(∫z,‖M z‖^2 ∂energyMeasure μ (H-h)):=by
  have he:=mass μ H h hhH I M hI hM
  have hia:=ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _=>sq_nonneg _))
  have hma:=ofReal_integral_eq_lintegral_ofReal hm (ae_of_all _ (fun _=>sq_nonneg _))
  rw [←hia,←hma,←ENNReal.ofReal_add (integral_nonneg (fun _=>sq_nonneg _))
    (integral_nonneg (fun _=>sq_nonneg _))] at he
  have hf:Integrable (fun z=>‖field h I M z‖^2) (energyMeasure μ H):=by
    refine ⟨((measurable h I M hI hM).norm.pow_const 2).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _)),he]
    exact ENNReal.ofReal_lt_top
  refine ⟨hf,?_⟩
  have hfa:=ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ (fun _=>sq_nonneg _))
  apply (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (fun _=>sq_nonneg _))
    (add_nonneg (integral_nonneg (fun _=>sq_nonneg _)) (integral_nonneg (fun _=>sq_nonneg _)))).mp
  exact hfa.trans he


/-- AE section identities for actual stochastic versions transport to
the full output clock, even when only the chosen version is jointly
Borel. No measurable diagonal of stochastic versions is assumed. -/
theorem congr_sections (μ:Measure Ω)(H h:ℝ≥0)(hhH:h≤H)
    (I M I₀ M₀:ℝ≥0×Ω→E)
    (hI:∀ᵐt∂timeMeasure h,∀ᵐω∂μ,I (t,ω)=I₀ (t,ω))
    (hM:∀ᵐv∂timeMeasure (H-h),∀ᵐω∂μ,M (v,ω)=M₀ (v,ω)):
    ∀ᵐt∂timeMeasure H,∀ᵐω∂μ,field h I M (t,ω)=field h I₀ M₀ (t,ω):=by
  have hIr:∀ᵐt:ℝ∂volume.restrict (Ioc (0:ℝ) (h:ℝ)),
      ∀ᵐω∂μ,I (t.toNNReal,ω)=I₀ (t.toNNReal,ω):=by
    rw [←timeMeasure_map h]
    apply nonnegative_coe_measurableEmbedding.ae_map_iff.mpr
    simpa only [Real.toNNReal_coe] using hI
  have hMr:∀ᵐv:ℝ∂volume.restrict (Ioc (0:ℝ) ((H:ℝ)-(h:ℝ))),
      ∀ᵐω∂μ,M (v.toNNReal,ω)=M₀ (v.toNNReal,ω):=by
    rw [←NNReal.coe_sub hhH,←timeMeasure_map (H-h)]
    apply nonnegative_coe_measurableEmbedding.ae_map_iff.mpr
    simpa only [Real.toNNReal_coe] using hM
  have hshift:∀ᵐt:ℝ∂volume.restrict (Ioc (h:ℝ) (H:ℝ)),
      ∀ᵐω∂μ,M ((t-(h:ℝ)).toNNReal,ω)=M₀ ((t-(h:ℝ)).toNNReal,ω):=by
    have hp:=MovingClockEnergy.translation (h:ℝ) ((H:ℝ)-(h:ℝ))
    have hend:(h:ℝ)+((H:ℝ)-(h:ℝ))=(H:ℝ):=by ring
    rw [hend] at hp
    rw [←hp.map_eq]
    apply (MeasurableEquiv.addRight (h:ℝ)).measurableEmbedding.ae_map_iff.mpr
    simpa only [MeasurableEquiv.coe_addRight,add_sub_cancel_right] using hMr
  rw [ae_restrict_iff' measurableSet_Ioc] at hIr hshift
  have he:∀ᵐt:ℝ∂volume.restrict (Ioc (0:ℝ) (H:ℝ)),
      ∀ᵐω∂μ,field h I M (t.toNNReal,ω)=field h I₀ M₀ (t.toNNReal,ω):=by
    filter_upwards [ae_restrict_of_ae hIr,ae_restrict_of_ae hshift,
      ae_restrict_mem measurableSet_Ioc] with t hi hm ht
    have ht':(t.toNNReal:ℝ)=t:=Real.coe_toNNReal _ ht.1.le
    by_cases hth:t≤(h:ℝ)
    · have htn:t.toNNReal≤h:=NNReal.coe_le_coe.mp (by simpa only [ht'] using hth)
      simpa only [field,if_pos htn] using hi ⟨ht.1,hth⟩
    · have htn:¬t.toNNReal≤h:=by
        intro hh
        exact hth (by simpa only [ht'] using NNReal.coe_le_coe.mpr hh)
      have hle:h≤t.toNNReal:=le_of_lt (lt_of_not_ge htn)
      have hsub:t.toNNReal-h=(t-(h:ℝ)).toNNReal:=by
        ext
        rw [NNReal.coe_sub hle,ht',Real.coe_toNNReal _ (by linarith [lt_of_not_ge hth])]
      simpa only [field,if_neg htn,hsub] using hm ⟨lt_of_not_ge hth,ht.2⟩
  have hh:=(timeMeasurePreserving H).quasiMeasurePreserving.ae he
  simpa only [Real.toNNReal_coe] using hh

end SHE.NativeOutputTimePatch
