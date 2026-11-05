module
public import SHE.NativeGammaClock
public import SHE.PredictableTime
public import Mathlib.MeasureTheory.Group.Prod
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.NativeGammaAgeMeasure
open Set MeasureTheory PredictableL2
open scoped NNReal ENNReal

/-- Exact ORIGINAL full-H time measure changed to future age b-q.
Both original stop cutoffs remain; endpoints are removed only by
Lebesgue nullity. No frequency or integrability assumption is used. -/
theorem scalar (H v b : ℝ≥0) (hbH:b≤H) (F:ℝ≥0→ℝ≥0∞) :
    (∫⁻q,(Ioo v b).indicator F q ∂timeMeasure H)=
      ∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),F ((b:ℝ)-τ).toNNReal := by
  rw [timeMeasure_lintegral]
  have he:(fun q:ℝ=>(Ioo v b).indicator F q.toNNReal)=ᵐ[volume.restrict (Ioc 0 (H:ℝ))]
      (Ioo (v:ℝ) (b:ℝ)).indicator (fun q:ℝ=>F q.toNNReal):=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    have hq0:0≤q:=hq.1.le
    have hmem:q.toNNReal∈Ioo v b ↔ q∈Ioo (v:ℝ) (b:ℝ):=by
      constructor <;> intro hh
      · have h1:(v:ℝ)<(q.toNNReal:ℝ):=by exact_mod_cast hh.1
        have h2:(q.toNNReal:ℝ)<(b:ℝ):=by exact_mod_cast hh.2
        rw [Real.coe_toNNReal _ hq0] at h1 h2
        exact ⟨h1,h2⟩
      · constructor
        · exact_mod_cast (by simpa only [Real.coe_toNNReal _ hq0] using hh.1 : (v:ℝ)<(q.toNNReal:ℝ))
        · exact_mod_cast (by simpa only [Real.coe_toNNReal _ hq0] using hh.2 : (q.toNNReal:ℝ)<(b:ℝ))
    by_cases hm:q∈Ioo (v:ℝ) (b:ℝ)
    · rw [indicator_of_mem (hmem.mpr hm),indicator_of_mem hm]
    · rw [indicator_of_notMem (fun hh=>hm (hmem.mp hh)),indicator_of_notMem hm]
  rw [lintegral_congr_ae he,lintegral_indicator measurableSet_Ioo]
  have hs:Ioo (v:ℝ) (b:ℝ)⊆Ioc (0:ℝ) (H:ℝ):=by
    intro q hq
    exact ⟨v.coe_nonneg.trans_lt hq.1,hq.2.le.trans (by exact_mod_cast hbH)⟩
  rw [Measure.restrict_restrict measurableSet_Ioo,inter_eq_left.mpr hs]
  have hp:MeasurePreserving (fun τ:ℝ=>(b:ℝ)-τ)
      (volume.restrict (Ioo (0:ℝ) ((b:ℝ)-(v:ℝ))))
      (volume.restrict (Ioo (v:ℝ) (b:ℝ))):=by
    have hh:=((volume:Measure ℝ).measurePreserving_sub_left (b:ℝ)).restrict_preimage (show MeasurableSet (Ioo (v:ℝ) (b:ℝ)) from measurableSet_Ioo)
    have hpre:(fun τ:ℝ=>(b:ℝ)-τ) ⁻¹' Ioo (v:ℝ) (b:ℝ)=Ioo (0:ℝ) ((b:ℝ)-(v:ℝ)):=by
      ext τ
      simp only [mem_preimage,mem_Ioo]
      constructor <;> intro ht <;> constructor <;> linarith [ht.1,ht.2]
    rwa [hpre] at hh
  rw [←restrict_Ioo_eq_restrict_Ioc]
  exact (hp.lintegral_comp_emb (MeasurableEquiv.subLeft (b:ℝ)).measurableEmbedding
    (fun q:ℝ=>F q.toNNReal)).symm
variable {Ω:Type*} [MeasurableSpace Ω]
/-- Fubini and the exact age change for arbitrary original joint fields.
This is the literal clock/section measure in the complete same-J bound. -/
theorem product (μ:Measure Ω) [SFinite μ] (H v b:ℝ≥0) (hbH:b≤H)
    (F:(ℝ≥0×Ω)→ℝ≥0∞) (hF:Measurable F):
    (∫⁻p,(NativeGammaClock.window v b).indicator F p ∂energyMeasure μ H)=
      ∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,F (((b:ℝ)-τ).toNNReal,ω) ∂μ :=by
  have ht:Measurable (fun p:ℝ≥0×Ω=>(p.1:ℝ)):=measurable_coe_nnreal_real.comp measurable_fst
  have hw:MeasurableSet (NativeGammaClock.window (Ω:=Ω) v b):=by
    exact (measurableSet_lt measurable_const ht).inter (measurableSet_lt ht measurable_const)
  calc
    _=(∫⁻q,∫⁻ω,(NativeGammaClock.window v b).indicator F (q,ω) ∂μ ∂timeMeasure H):=
      lintegral_prod _ (by exact (hF.indicator hw).aemeasurable)
    _=(∫⁻q,(Ioo v b).indicator (fun q=>∫⁻ω,F (q,ω) ∂μ) q ∂timeMeasure H):=by
      apply lintegral_congr
      intro q
      by_cases hq:q∈Ioo v b
      · simp only [indicator_of_mem hq]
        apply lintegral_congr
        intro ω
        exact indicator_of_mem (show (q,ω)∈NativeGammaClock.window v b from hq) F
      · rw [indicator_of_notMem hq]
        have he(ω:Ω): (NativeGammaClock.window v b).indicator F (q,ω)=0:=
          indicator_of_notMem (show (q,ω)∉NativeGammaClock.window v b from hq) F
        simp only [he,lintegral_zero]
    _=_:=scalar H v b hbH _
end SHE.NativeGammaAgeMeasure

