module

public import SHE.StoppedItoInputs

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.PastItoInputs
open MeasureTheory Set PredictableL2 Classical
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)

def eventAfter (v : ℝ≥0) (A : Set Ω) : Set (ℝ≥0×Ω) := Ioi v×ˢ A

theorem eventAfter_measurable (v : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[𝓕 v] A) :
    MeasurableSet[𝓕.predictable] (eventAfter v A) := measurableSet_predictable_Ioi_prod hA

/-- The literal full-horizon predictable L2 input restricted to an
event known at v and to times strictly after v. -/
def eventProcess (v : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 v] A)
    (u : Process (E := C) 𝓕 μ H) : Process (E := C) 𝓕 μ H :=
  ((Lp.memLp u).indicator (eventAfter_measurable 𝓕 v hA).nullMeasurableSet).toLp
    ((eventAfter v A).indicator u)

theorem eventProcess_ae (v : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 v] A)
    (u : Process (E := C) 𝓕 μ H) :
    eventProcess 𝓕 μ H v A hA u =ᵐ[energyMeasure μ H] (eventAfter v A).indicator u :=
  ae_eq_of_ae_eq_trim ((Lp.memLp u).indicator (eventAfter_measurable 𝓕 v hA).nullMeasurableSet).coeFn_toLp

def post (v : ℝ≥0) (u : Process (E := C) 𝓕 μ H) : Process (E := C) 𝓕 μ H :=
  eventProcess 𝓕 μ H v univ MeasurableSet.univ u

theorem post_ae (v : ℝ≥0) (u : Process (E := C) 𝓕 μ H) :
    post 𝓕 μ H v u =ᵐ[energyMeasure μ H] fun p => if v<p.1 then u p else 0 := by
  filter_upwards [eventProcess_ae 𝓕 μ H v univ MeasurableSet.univ u] with p hp
  change eventProcess 𝓕 μ H v univ MeasurableSet.univ u p=_
  rw [hp]
  simp only [eventAfter,indicator,mem_prod,mem_Ioi,mem_univ,and_true]

theorem post_supported (v : ℝ≥0) (u : Process (E := C) 𝓕 μ H) :
    ∀ᵐ p ∂energyMeasure μ H,p.1≤v → post 𝓕 μ H v u p=0 := by
  filter_upwards [post_ae 𝓕 μ H v u] with p hp hv
  rw [hp,if_neg (not_lt.mpr hv)]

variable [SFinite μ]

/-- The exact pathwise bracket is restricted by the same past event.
Both sides use the original full-horizon integral input space. -/
theorem event_bracket_ae (v : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 v] A)
    (u : Process (E := C) 𝓕 μ H) :
    ∀ᵐ ω ∂μ,(∫⁻ s,ENNReal.ofReal (‖eventProcess 𝓕 μ H v A hA u (s,ω)‖^2) ∂timeMeasure H)=
      if ω∈A then (∫⁻ s,ENNReal.ofReal (‖post 𝓕 μ H v u (s,ω)‖^2) ∂timeMeasure H) else 0 := by
  have he := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (eventProcess_ae 𝓕 μ H v A hA u)
  have hp := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (post_ae 𝓕 μ H v u)
  filter_upwards [Measure.ae_ae_of_ae_prod he,Measure.ae_ae_of_ae_prod hp] with ω he hp
  by_cases hω : ω∈A
  · rw [if_pos hω]
    apply lintegral_congr_ae
    filter_upwards [he,hp] with s hs ht
    dsimp only [Prod.swap] at hs ht
    rw [hs,ht]
    simp only [eventAfter,indicator,mem_prod,mem_Ioi,hω,and_true]
  · rw [if_neg hω]
    calc
      _ = ∫⁻ _s : ℝ≥0,(0:ℝ≥0∞) ∂timeMeasure H := by
        apply lintegral_congr_ae
        filter_upwards [he] with s hs
        dsimp only [Prod.swap] at hs
        rw [hs,indicator_of_notMem (show (s,ω)∉eventAfter v A from fun h => hω h.2)]
        simp
      _ = _ := by simp

end SHE.PastItoInputs
