module

public import SHE.HistoryProductMeasure
public import SHE.ObservationTimeShift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.ShiftedOldTimeMeasure
open Set MeasureTheory

/-- The physical old-time cube is the exact translate of its relative
cube. This includes depth zero and spans of zero measure. -/
theorem measurePreserving (v h : ℝ) (k : ℕ) :
    MeasurePreserving (fun t : Fin k→ℝ=>fun i=>t i+v)
      (Measure.pi (fun _ : Fin k=>volume.restrict (Ioc 0 h)))
      (Measure.pi (fun _ : Fin k=>volume.restrict (Ioc v (v+h)))) := by
  have ht := (measurePreserving_add_right (volume : Measure ℝ) v).restrict_preimage
    (measurableSet_Ioc : MeasurableSet (Ioc v (v+h)))
  have he : (fun t : ℝ=>t+v) ⁻¹' Ioc v (v+h)=Ioc 0 h := by
    ext t
    simp only [mem_preimage,mem_Ioc]
    constructor <;> intro ht <;> constructor <;> linarith [ht.1,ht.2]
  rw [he] at ht
  exact measurePreserving_pi _ _ (fun _=>ht)

/-- Bochner old-time integration may be moved to a fixed relative
cube before squaring, without any probability normalization factor. -/
theorem integral_translation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (v h : ℝ) (k : ℕ) (f : (Fin k→ℝ)→E) :
    (∫ t,f (fun i=>t i+v) ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc 0 h)))=
      ∫ t,f t ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc v (v+h))) :=
  by
  have hp := measurePreserving v h k
  exact hp.integral_comp (Homeomorph.addRight (fun _ : Fin k=>v)).isClosedEmbedding.measurableEmbedding f

end SHE.ShiftedOldTimeMeasure
