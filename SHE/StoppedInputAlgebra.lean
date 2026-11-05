module

public import SHE.StoppedDampingClock
public import SHE.PredictableWeightedAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.StoppedInputAlgebra
open MeasureTheory Set PredictableL2 StoppedItoInputs PredictableContraction
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)

theorem stop_smul (t c : ℝ) (v : Process (E := C) 𝓕 μ H) :
    stop 𝓕 μ H t (c • v)=c • stop 𝓕 μ H t v := by
  apply Lp.ext
  filter_upwards [StoppedInputParameter.stop_ae_trim 𝓕 μ H (c • v) t,
    StoppedInputParameter.stop_ae_trim 𝓕 μ H v t,Lp.coeFn_smul c v,
    Lp.coeFn_smul c (stop 𝓕 μ H t v)] with p hl hs hi ho
  rw [hl,ho]
  change (before t).indicator (c • v) p=c • stop 𝓕 μ H t v p
  rw [hs]
  by_cases hp : p∈before (Ω := Ω) t
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem hp,hi]
    rfl
  · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem hp,smul_zero]

theorem stop_stop (s t : ℝ) (v : Process (E := C) 𝓕 μ H) :
    stop 𝓕 μ H s (stop 𝓕 μ H t v)=stop 𝓕 μ H (min s t) v := by
  apply Lp.ext
  filter_upwards [StoppedInputParameter.stop_ae_trim 𝓕 μ H (stop 𝓕 μ H t v) s,
    StoppedInputParameter.stop_ae_trim 𝓕 μ H v t,
    StoppedInputParameter.stop_ae_trim 𝓕 μ H v (min s t)] with p hl hi hr
  rw [hl,hr]
  simp only [Set.indicator_apply,before,Set.mem_setOf_eq]
  rw [hi]
  simp only [Set.indicator_apply,before,Set.mem_setOf_eq,lt_min_iff]
  by_cases hs : (p.1:ℝ)<s <;> by_cases ht : (p.1:ℝ)<t <;> simp [hs,ht]

theorem stop_weighted (t : ℝ) (a : ℝ≥0×Ω→ℝ)
    (ha : StronglyMeasurable[𝓕.predictable] a) (hb : ∀ p,|a p|≤1)
    (v : Process (E := C) 𝓕 μ H) :
    stop 𝓕 μ H t (weighted 𝓕 μ H a ha hb v)=weighted 𝓕 μ H a ha hb (stop 𝓕 μ H t v) := by
  apply Lp.ext
  filter_upwards [StoppedInputParameter.stop_ae_trim 𝓕 μ H (weighted 𝓕 μ H a ha hb v) t,
    StoppedInputParameter.stop_ae_trim 𝓕 μ H v t,
    (weighted_memLp 𝓕 μ H a ha hb v).coeFn_toLp,
    (weighted_memLp 𝓕 μ H a ha hb (stop 𝓕 μ H t v)).coeFn_toLp] with p hl hs hv hr
  change weighted 𝓕 μ H a ha hb v p=a p • v p at hv
  change weighted 𝓕 μ H a ha hb (stop 𝓕 μ H t v) p=a p • stop 𝓕 μ H t v p at hr
  rw [hl,hr,hs]
  by_cases hp : p∈before (Ω := Ω) t
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem hp,hv]
  · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem hp,smul_zero]

end SHE.StoppedInputAlgebra
