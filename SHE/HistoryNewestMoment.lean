module

public import SHE.HistoryNewestSpatial
public import SHE.RealMomentBound

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section
namespace SHE.HistoryNewestMoment
open Set MeasureTheory StoppedFourier CutoffWordLevel CutoffWordHistories
local instance historyNewestMoment_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {X Ω:Type} [MeasurableSpace X] [MeasurableSpace Ω]

/-- True newest-spatial conditional moments lift to the ORIGINAL
history measure using the Borel lintegral event of the actual field.
No uncountable parameter event or adaptive-center substitution is used. -/
theorem ae_succ_even (R:ReferenceData) (ρ:Measure X) [IsFiniteMeasure ρ]
    (k:ℕ) (μ:Measure Ω) [SFinite μ]
    (F:History X (k+1)×Ω→ℝ) (hF:Measurable F)
    (B:History X (k+1)→ℝ) (hB:Measurable B) (hB0:∀h,0≤B h) (p:ℕ)
    (hsections:∀ᵐ old ∂historyMeasure R ρ k,
      ∀ᵐ t ∂volume.restrict (Ioc R.base R.horizon),
        ∀ᵐ x:HeatCircle ∂AddCircle.haarAddCircle,
          Integrable (fun ω=>|F ((old,(t,x)),ω)|^(2*p)) μ ∧
          (∫ω,|F ((old,(t,x)),ω)|^(2*p) ∂μ)≤B (old,(t,x))):
    ∀ᵐ h ∂historyMeasure R ρ (k+1),
      Integrable (fun ω=>|F (h,ω)|^(2*p)) μ ∧
      (∫ω,|F (h,ω)|^(2*p) ∂μ)≤B h:=by
  let G:History X (k+1)×Ω→ℝ:=fun z=>|F z|^(2*p)
  have hG:Measurable G:=(continuous_abs.measurable.comp hF).pow_const _
  have hgm:Measurable (fun z:History X (k+1)×Ω=>ENNReal.ofReal (G z)):=
    ENNReal.measurable_ofReal.comp hG
  have hlin:Measurable (fun h=>∫⁻ω,ENNReal.ofReal (G (h,ω)) ∂μ):=
    hgm.lintegral_prod_right
  have hset:MeasurableSet {h | (∫⁻ω,ENNReal.ofReal (G (h,ω)) ∂μ)≤ENNReal.ofReal (B h)}:=
    measurableSet_le hlin (ENNReal.measurable_ofReal.comp hB)
  have hevent:∀ᵐ h ∂historyMeasure R ρ (k+1),
      (∫⁻ω,ENNReal.ofReal (G (h,ω)) ∂μ)≤ENNReal.ofReal (B h):=by
    apply (HistoryNewestSpatial.ae_succ_iff R ρ k _ hset).mpr
    filter_upwards [hsections] with old hold
    filter_upwards [hold] with t ht
    filter_upwards [ht] with x hx
    have he:=ofReal_integral_eq_lintegral_ofReal hx.1
      (ae_of_all μ (fun ω=>pow_nonneg (abs_nonneg _) _))
    change (∫⁻ω,ENNReal.ofReal (|F ((old,(t,x)),ω)|^(2*p)) ∂μ)≤_
    rw [←he]
    exact ENNReal.ofReal_le_ofReal hx.2
  filter_upwards [hevent] with h hh
  have hm:Measurable (fun ω=>G (h,ω)):=hG.comp (measurable_const.prodMk measurable_id)
  have h0:0≤ᵐ[μ] (fun ω=>G (h,ω)):=ae_of_all μ (fun ω=>pow_nonneg (abs_nonneg _) _)
  have hi:Integrable (fun ω=>G (h,ω)) μ:=⟨hm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal h0).mpr (hh.trans_lt ENNReal.ofReal_lt_top)⟩
  have he:=ofReal_integral_eq_lintegral_ofReal hi h0
  rw [←he] at hh
  exact ⟨hi,(ENNReal.ofReal_le_ofReal_iff (hB0 h)).mp hh⟩

end SHE.HistoryNewestMoment
