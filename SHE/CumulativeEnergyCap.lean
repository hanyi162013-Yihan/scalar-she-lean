module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.CumulativeEnergyCap
open MeasureTheory Set

def cumulative (f:ℝ→ℝ)(t:ℝ):ℝ:=∫s in (0:ℝ)..t,f s

def clipped (f:ℝ→ℝ)(t:ℝ):ℝ:=if cumulative f t<1 then f t else 0

theorem continuous_cumulative {f:ℝ→ℝ}(hf:Continuous f):Continuous (cumulative f):=by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hf.integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt

theorem monotone_cumulative {f:ℝ→ℝ}(hf:Continuous f)(h0:∀s,0≤f s):
    MonotoneOn (cumulative f) (Ici 0):=by
  intro a ha b hb hab
  exact intervalIntegral.integral_mono_interval le_rfl ha hab
    (ae_of_all _ h0) (hf.intervalIntegrable 0 b)

theorem clipped_nonneg {f:ℝ→ℝ}(h0:∀s,0≤f s)(t:ℝ):0≤clipped f t:=by
  unfold clipped
  split_ifs
  · exact h0 t
  · exact le_rfl

theorem clipped_le {f:ℝ→ℝ}(h0:∀s,0≤f s)(t:ℝ):clipped f t≤f t:=by
  unfold clipped
  split_ifs <;> simp_all

/-- Predictable energy clipping has a deterministic total cap of one.
Only ordinary real integration and the intermediate value theorem are
used; no stopping or exponential-martingale theorem is assumed here. -/
theorem energy_le_one {f:ℝ→ℝ}(hf:Continuous f)(h0:∀s,0≤f s){H:ℝ}(hH:0≤H):
    Integrable (clipped f) (volume.restrict (Ioc 0 H)) ∧
      (∫t,clipped f t ∂volume.restrict (Ioc 0 H))≤1:=by
  have hA:=continuous_cumulative hf
  have hmono:=monotone_cumulative hf h0
  have hfm:Measurable (clipped f):=hf.measurable.ite
    (measurableSet_lt hA.measurable measurable_const) measurable_const
  have hi:Integrable f (volume.restrict (Ioc 0 H)):=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hH).mp (hf.intervalIntegrable 0 H)
  have hc:Integrable (clipped f) (volume.restrict (Ioc 0 H)):=by
    apply hi.mono' hfm.aestronglyMeasurable
    exact ae_of_all _ (fun t=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (clipped_nonneg h0 t)]
      exact clipped_le h0 t)
  refine ⟨hc,?_⟩
  by_cases hend:cumulative f H≤1
  · apply (integral_mono hc hi (clipped_le h0)).trans
    simpa only [cumulative,intervalIntegral.integral_of_le hH] using hend
  · have h0A:cumulative f 0=0:=by simp only [cumulative,intervalIntegral.integral_same]
    have h1:1∈Icc (cumulative f 0) (cumulative f H):=by rw [h0A];exact ⟨by norm_num,le_of_lt (lt_of_not_ge hend)⟩
    obtain ⟨τ,hτ,hAτ⟩:∃τ∈Icc (0:ℝ) H,cumulative f τ=1:=
      intermediate_value_Icc hH hA.continuousOn h1
    let g:ℝ→ℝ:=(Ioc (0:ℝ) τ).indicator f
    have hg:Integrable g (volume.restrict (Ioc 0 H)):=hi.indicator measurableSet_Ioc
    have hle:∀ᵐt∂volume.restrict (Ioc 0 H),clipped f t≤g t:=by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      by_cases htτ:t≤τ
      · change clipped f t≤(Ioc (0:ℝ) τ).indicator f t
        rw [indicator_of_mem (show t∈Ioc (0:ℝ) τ from ⟨ht.1,htτ⟩)]
        exact clipped_le h0 t
      · have hAt:1≤cumulative f t:=hAτ ▸ hmono hτ.1 ht.1.le (le_of_not_ge htτ)
        simp only [clipped,not_lt.mpr hAt,ite_false,g,indicator_of_notMem (show t∉Ioc 0 τ from fun h=>htτ h.2),le_refl]
    apply (integral_mono_ae hc hg hle).trans_eq
    change (∫t,(Ioc (0:ℝ) τ).indicator f t ∂volume.restrict (Ioc 0 H))=1
    rw [integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc]
    have he:Ioc (0:ℝ) τ∩Ioc 0 H=Ioc 0 τ:=inter_eq_left.mpr (Ioc_subset_Ioc le_rfl hτ.2)
    rw [he,←intervalIntegral.integral_of_le hτ.1]
    exact hAτ

/-- On the no-exit event the clipped control equals the full control
at EVERY time, not only for almost every time. -/
theorem no_exit {f:ℝ→ℝ}(hf:Continuous f)(h0:∀s,0≤f s){H:ℝ}(hend:cumulative f H<1)
    {t:ℝ}(ht:t∈Icc (0:ℝ) H):clipped f t=f t:=by
  have hh: cumulative f t<1:=(monotone_cumulative hf h0 ht.1 (ht.1.trans ht.2) ht.2).trans_lt hend
  exact if_pos hh
end SHE.CumulativeEnergyCap
