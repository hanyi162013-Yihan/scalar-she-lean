module

public import SHE.LpDominatedLimit
public import SHE.StoppedItoInputs
public import SHE.ApproximationClock

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.StoppedInputParameter
open MeasureTheory Filter Set PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal Topology
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0)
variable (v : Process (E := C) 𝓕 μ h)

theorem stop_ae_trim (t : ℝ) : stop 𝓕 μ h t v=ᵐ[(energyMeasure μ h).trim (predictable_le_product 𝓕)]
    (before t).indicator v :=
  ((Lp.memLp v).indicator (before_measurable 𝓕 t).nullMeasurableSet).coeFn_toLp

theorem norm_le_ae (t : ℝ) : ∀ᵐ p ∂(energyMeasure μ h).trim (predictable_le_product 𝓕),
    ‖stop 𝓕 μ h t v p‖≤‖v p‖ := by
  filter_upwards [stop_ae_trim 𝓕 μ h v t] with p hp
  rw [hp]
  by_cases hp : p∈before (Ω := Ω) t
  · rw [Set.indicator_of_mem hp]
  · rw [Set.indicator_of_notMem hp,norm_zero]
    exact norm_nonneg _

theorem stop_tendsto_left {t : ℝ} (s : ℕ→ℝ) (hs : ∀ n,s n≤t)
    (ht : Tendsto s atTop (𝓝 t)) :
    Tendsto (fun n => stop 𝓕 μ h (s n) v) atTop (𝓝 (stop 𝓕 μ h t v)) := by
  apply @LpDominatedLimit.tendsto (ℝ≥0×Ω) C 𝓕.predictable _ _
    ((energyMeasure μ h).trim (predictable_le_product 𝓕)) v _ _
    (fun n => norm_le_ae 𝓕 μ h v (s n)) (norm_le_ae 𝓕 μ h v t)
  have hall := ae_all_iff.mpr (fun n => stop_ae_trim 𝓕 μ h v (s n))
  filter_upwards [hall,stop_ae_trim 𝓕 μ h v t]
    with p hp hpt
  by_cases hr : (p.1:ℝ)<t
  · have he : ∀ᶠ n in atTop,(p.1:ℝ)<s n := ht.eventually (lt_mem_nhds hr)
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    rw [hp n,hpt,Set.indicator_of_mem (show p∈before (Ω := Ω) (s n) from hn),
      Set.indicator_of_mem (show p∈before (Ω := Ω) t from hr)]
  · have he : ∀ n,¬(p.1:ℝ)<s n := fun n hn => hr (hn.trans_le (hs n))
    have hz : stop 𝓕 μ h t v p=0 := by
      rw [hpt,Set.indicator_of_notMem (show p∉before (Ω := Ω) t from hr)]
    apply tendsto_const_nhds.congr'
    filter_upwards with n
    rw [hp n,hz,Set.indicator_of_notMem (show p∉before (Ω := Ω) (s n) from he n)]

theorem stronglyMeasurable : StronglyMeasurable (fun t : ℝ≥0 => stop 𝓕 μ h (t:ℝ) v) := by
  have happrox (n : ℕ) : StronglyMeasurable (fun t : ℝ≥0 =>
      stop 𝓕 μ h (ApproximationClock.left n (t:ℝ)) v) := by
    have hh := StronglyMeasurable.of_discrete (f := fun k : ℕ =>
      stop 𝓕 μ h (ApproximationClock.delta n*(k:ℝ)-ApproximationClock.delta n) v)
    exact hh.comp_measurable (Nat.measurable_ceil.comp
      (measurable_coe_nnreal_real.div_const (ApproximationClock.delta n)))
  apply stronglyMeasurable_of_tendsto atTop happrox
  apply tendsto_pi_nhds.mpr
  intro t
  apply stop_tendsto_left 𝓕 μ h v _ _ (ApproximationClock.left_tendsto t.2)
  intro n
  rcases lt_or_eq_of_le t.2 with ht|ht
  · exact (ApproximationClock.left_bounds n ht).2.1.le
  · rw [← ht,ApproximationClock.left,ApproximationClock.right]
    simp only [zero_div,Nat.ceil_zero,Nat.cast_zero,mul_zero,zero_sub]
    exact neg_nonpos.mpr (ApproximationClock.delta_pos n).le

end SHE.StoppedInputParameter
