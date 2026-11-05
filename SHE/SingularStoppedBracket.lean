module

public import SHE.StoppedBoundedBracket
public import SHE.IntervalTimeMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.SingularStoppedBracket
open MeasureTheory Set PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)

/-- An inverse-root singularity at a fixed future heat target still
gives a square-root bracket modulus for every stopped increment of the
SAME full-horizon integral. The current upper endpoint may equal the
heat target. -/
theorem increment_bound (u : Process (E:=C) 𝓕 μ H) (b : ℝ≥0) {K : ℝ} (hK : 0≤K)
    (hu : ∀ᵐ p ∂energyMeasure μ H,p.1≤b → ‖u p‖^2≤K*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)))
    (s t : ℝ≥0) (hst : s≤t) (htb : t≤b) (htH : t≤H) :
    ∀ᵐ ω ∂μ,(∫⁻ r,ENNReal.ofReal
      (‖(stop 𝓕 μ H (t:ℝ) u-stop 𝓕 μ H (s:ℝ) u) (r,ω)‖^2) ∂timeMeasure H)≤
      ENNReal.ofReal (2*K*((t:ℝ)-(s:ℝ))^(1/2:ℝ)) := by
  have he : ∀ᵐ p ∂energyMeasure μ H,
      ‖(stop 𝓕 μ H (t:ℝ) u-stop 𝓕 μ H (s:ℝ) u) p‖^2≤
        (Ico s t).indicator (fun r : ℝ≥0 => K*((t:ℝ)-(r:ℝ))^(-(1/2:ℝ))) p.1 := by
    filter_upwards [hu,stop_ae 𝓕 μ H (t:ℝ) u,stop_ae 𝓕 μ H (s:ℝ) u,
      ae_eq_of_ae_eq_trim (Lp.coeFn_sub (stop 𝓕 μ H (t:ℝ) u) (stop 𝓕 μ H (s:ℝ) u))]
      with p hp ht hs he
    rw [he]
    simp only [Pi.sub_apply]
    rw [ht,hs]
    simp only [Set.indicator_apply,before,mem_setOf_eq]
    change ‖(if p.1<t then u p else 0)-(if p.1<s then u p else 0)‖^2≤
      (if p.1∈Ico s t then K*((t:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)) else 0)
    by_cases hps : p.1<s
    · have hpt : p.1<t := hps.trans_le hst
      simp [hpt,hps,mem_Ico,not_le.mpr hps]
    · by_cases hpt : p.1<t
      · have hpm : p.1∈Ico s t := ⟨le_of_not_gt hps,hpt⟩
        simp only [hpt,hps,ite_true,ite_false,sub_zero,hpm]
        apply (hp (hpt.le.trans htb)).trans
        apply mul_le_mul_of_nonneg_left _ hK
        apply Real.rpow_le_rpow_of_nonpos (sub_pos.mpr (by exact_mod_cast hpt))
        · have := NNReal.coe_le_coe.mpr htb
          linarith
        · norm_num
      · simp [hpt,hps,mem_Ico]
  have hs := (Measure.measurePreserving_swap (μ:=μ) (ν:=timeMeasure H)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  calc
    _ ≤ ∫⁻ r,(Ico s t).indicator
        (fun r : ℝ≥0 => ENNReal.ofReal (K*((t:ℝ)-(r:ℝ))^(-(1/2:ℝ)))) r ∂timeMeasure H := by
      apply lintegral_mono_ae
      filter_upwards [hω] with r hr
      have hh := ENNReal.ofReal_le_ofReal hr
      by_cases hrmem : r∈Ico s t <;> simpa [Prod.swap,hrmem] using hh
    _ = ∫⁻ r,ENNReal.ofReal (K*((t:ℝ)-(r:ℝ))^(-(1/2:ℝ))) ∂intervalTimeMeasure s t := by
      rw [lintegral_indicator measurableSet_Ico,
        Measure.restrict_congr_set (Ico_ae_eq_Ioc (μ:=timeMeasure H)),timeMeasure_restrict_Ioc s htH]
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul hK]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        interval_causal_rpow_mass (by norm_num : (-1:ℝ)< -(1/2:ℝ)) hst,
        ←ENNReal.ofReal_mul hK]
      congr 1
      norm_num only [show -(1/2:ℝ)+1=1/2 by norm_num]
      ring

end SHE.SingularStoppedBracket
