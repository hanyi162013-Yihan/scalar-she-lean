module

public import SHE.PredictableTime
public import SHE.ShiftedOldTimeMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.MovingClockEnergy
open Set MeasureTheory PredictableL2
open scoped NNReal ENNReal

theorem translation (v h : ℝ) : MeasurePreserving (MeasurableEquiv.addRight v)
    (volume.restrict (Ioc 0 h)) (volume.restrict (Ioc v (v+h))) := by
  have ht := (measurePreserving_add_right (volume : Measure ℝ) v).restrict_preimage
    (measurableSet_Ioc : MeasurableSet (Ioc v (v+h)))
  have he : (fun t : ℝ=>t+v) ⁻¹' Ioc v (v+h)=Ioc 0 h := by
    ext t
    simp only [mem_preimage,mem_Ioc]
    constructor <;> intro ht <;> constructor <;> linarith [ht.1,ht.2]
  rwa [he] at ht

/-- Moving a local current window into the same full native Ito
clock cannot increase the original unsigned energy mass. -/
theorem local_lintegral_le_native (H : ℝ≥0) (v h : ℝ) (hv : 0≤v) (hvh : v+h≤(H:ℝ))
    (f : ℝ≥0→ℝ≥0∞) :
    (∫⁻ s in Ioc (0:ℝ) h,f (s+v).toNNReal)≤∫⁻ q,f q ∂timeMeasure H := by
  rw [timeMeasure_lintegral]
  have hsub : Ioc v (v+h)⊆Ioc (0:ℝ) (H:ℝ):=by
    intro q hq
    exact ⟨by linarith [hq.1],hq.2.trans hvh⟩
  calc
    _=(∫⁻ q in Ioc v (v+h),f q.toNNReal):=
      (translation v h).lintegral_comp_emb (MeasurableEquiv.addRight v).measurableEmbedding _
    _≤_:=lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl

/-- A true physical-window budget has no hidden dependence on the
past location once transported to its relative current age. -/
theorem native_indicator_bound (H : ℝ≥0) (v h : ℝ) (B : ℝ→ℝ) :
    (∫⁻ q : ℝ≥0,ENNReal.ofReal (((Ioc v (v+h)).indicator (fun r=>B (r-v)) q)^2) ∂timeMeasure H)≤
      ∫⁻ s in Ioc (0:ℝ) h,ENNReal.ofReal ((B s)^2) := by
  rw [timeMeasure_lintegral]
  have he : (fun q : ℝ=>ENNReal.ofReal (((Ioc v (v+h)).indicator (fun r=>B (r-v)) q.toNNReal)^2))=ᵐ[volume.restrict (Ioc 0 (H:ℝ))]
      (Ioc v (v+h)).indicator (fun q=>ENNReal.ofReal ((B (q-v))^2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    rw [Real.coe_toNNReal _ hq.1.le]
    by_cases hp : q∈Ioc v (v+h)
    · simp only [indicator_of_mem hp]
    · simp only [indicator_of_notMem hp,zero_pow (by decide : (2:ℕ)≠0),ENNReal.ofReal_zero]
  rw [lintegral_congr_ae he]
  calc
    _≤(∫⁻ q,(Ioc v (v+h)).indicator (fun q=>ENNReal.ofReal ((B (q-v))^2)) q):=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _=(∫⁻ q in Ioc v (v+h),ENNReal.ofReal ((B (q-v))^2)):=lintegral_indicator measurableSet_Ioc _
    _=(∫⁻ s in Ioc (0:ℝ) h,ENNReal.ofReal ((B s)^2)):=by
      rw [←(translation v h).lintegral_comp_emb (MeasurableEquiv.addRight v).measurableEmbedding]
      apply lintegral_congr_ae
      filter_upwards [] with s
      change ENNReal.ofReal ((B ((s+v)-v))^2)=ENNReal.ofReal ((B s)^2)
      rw [add_sub_cancel_right]

end SHE.MovingClockEnergy
