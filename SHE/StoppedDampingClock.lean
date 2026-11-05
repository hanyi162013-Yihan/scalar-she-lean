module

public import SHE.StoppedResolventIdentity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.StoppedDampingClock
open MeasureTheory Set Filter PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

theorem stop_sub (t : ℝ) (v w : Process (E := C) 𝓕 μ H) :
    stop 𝓕 μ H t (v-w)=stop 𝓕 μ H t v-stop 𝓕 μ H t w := by
  apply Lp.ext
  filter_upwards [StoppedInputParameter.stop_ae_trim 𝓕 μ H (v-w) t,
    StoppedInputParameter.stop_ae_trim 𝓕 μ H v t,StoppedInputParameter.stop_ae_trim 𝓕 μ H w t,
    Lp.coeFn_sub v w,Lp.coeFn_sub (stop 𝓕 μ H t v) (stop 𝓕 μ H t w)] with p hs hv hw hi ho
  rw [hs,ho]
  change (before t).indicator (v-w) p=stop 𝓕 μ H t v p-stop 𝓕 μ H t w p
  rw [hv,hw]
  by_cases hp : p∈before (Ω := Ω) t
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem hp,Set.indicator_of_mem hp,hi]
    rfl
  · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem hp,Set.indicator_of_notMem hp,sub_self]

/-- Exact integrating-factor identity for genuine predictable inputs.
The exponential is normalized at the fixed end b so the underlying
multiplier remains bounded on the original full horizon. -/
theorem integrating_factor {Λ : ℝ} (hΛ : 0≤Λ) (b q : ℝ≥0) (hqb : q≤b)
    (v : Process (E := C) 𝓕 μ H) :
    Real.exp (Λ*(q:ℝ)) • StoppedInputResolvent.damped 𝓕 μ H v hΛ q=
      Real.exp (Λ*(b:ℝ)) • stop 𝓕 μ H (q:ℝ)
        (PredictableContraction.weighted 𝓕 μ H (PredictableDamping.weight Λ b)
          (PredictableDamping.weight_predictable 𝓕 Λ b) (PredictableDamping.weight_bound hΛ b) v) := by
  let w := PredictableContraction.weighted 𝓕 μ H (PredictableDamping.weight Λ b)
    (PredictableDamping.weight_predictable 𝓕 Λ b) (PredictableDamping.weight_bound hΛ b) v
  apply Lp.ext
  have hw := (PredictableContraction.weighted_memLp 𝓕 μ H (PredictableDamping.weight Λ b)
    (PredictableDamping.weight_predictable 𝓕 Λ b) (PredictableDamping.weight_bound hΛ b) v).coeFn_toLp
  filter_upwards [Lp.coeFn_smul (Real.exp (Λ*(q:ℝ))) (StoppedInputResolvent.damped 𝓕 μ H v hΛ q),
    Lp.coeFn_smul (Real.exp (Λ*(b:ℝ))) (stop 𝓕 μ H (q:ℝ) w),
    StoppedInputResolvent.damped_ae_trim 𝓕 μ H v hΛ q,
    StoppedInputParameter.stop_ae_trim 𝓕 μ H v q,
    StoppedInputParameter.stop_ae_trim 𝓕 μ H w q,hw] with p hl hr hd hs ht hw
  rw [hl,hr]
  change Real.exp (Λ*(q:ℝ)) • StoppedInputResolvent.damped 𝓕 μ H v hΛ q p=
    Real.exp (Λ*(b:ℝ)) • stop 𝓕 μ H (q:ℝ) w p
  rw [hd,hs,ht]
  by_cases hp : p∈before (Ω := Ω) (q:ℝ)
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem hp]
    change w p=PredictableDamping.weight Λ b p • v p at hw
    rw [hw,smul_smul,smul_smul]
    have hpq : (p.1:ℝ)≤(q:ℝ) := hp.le
    have hpb : (p.1:ℝ)≤(b:ℝ) := hpq.trans (by exact_mod_cast hqb)
    have he : Real.exp (Λ*(q:ℝ))*PredictableDamping.weight Λ q p=
        Real.exp (Λ*(b:ℝ))*PredictableDamping.weight Λ b p := by
      rw [PredictableDamping.weight_eq hpq,PredictableDamping.weight_eq hpb,← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    exact congrArg (fun z : ℝ => z • v p) he
  · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem hp,smul_zero,smul_zero,smul_zero]

end SHE.StoppedDampingClock
