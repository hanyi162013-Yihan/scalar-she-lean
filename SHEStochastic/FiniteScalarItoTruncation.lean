module

public import SHEStochastic.FiniteScalarTerminalIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.FiniteScalarItoProcess
open MeasureTheory ProbabilityTheory FiniteScalarIto
open scoped NNReal ENNReal
variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
local notation "ν" => inputMeasure F μ H

def trunc (t : ℝ≥0) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  FilteredItoProcessGeneral.truncCLM (𝓖 := F) (μ := μ) H t
    (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)

theorem trunc_ae (t : ℝ≥0) (v : Lp ℝ 2 ν) :
    trunc t v =ᵐ[ν] (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)).indicator v :=
  ((Lp.memLp v).indicator
    (FilteredItoProcessGeneral.measurableSet_band (𝓖 := F) t
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)).nullMeasurableSet).coeFn_toLp

variable (P : Family F μ H ι)

theorem prefixCLM_eq_zero_of_vanishes_before (i : ι) (t : ℝ≥0) (ht : t ≤ H)
    (v : Lp ℝ 2 ν) (hv : ∀ᵐ p ∂ν, p.1 ≤ t → v p = 0) :
    prefixCLM P i t v = 0 := by
  have hz : (∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)), v z ^ 2 ∂ν) = 0 := by
    have ha : ∀ᵐ z ∂(ν).restrict (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)), v z ^ 2 = 0 := by
      rw [ae_restrict_iff' (FilteredItoProcessGeneral.measurableSet_band (𝓖 := F) t
        (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const))]
      filter_upwards [hv] with z hz hmem
      rw [hz hmem.1.2, zero_pow two_ne_zero]
    rw [integral_congr_ae ha, integral_zero]
  apply norm_eq_zero.mp
  apply (pow_eq_zero_iff two_ne_zero).mp
  rw [prefixCLM_norm_sq P i t ht v, hz]

/-- Truncation of the input and conditional expectation of its terminal
integral agree, proved from finite-horizon band energy and adaptation. -/
theorem rawIsometry_trunc (i : ι) (t : ℝ≥0) (ht : t ≤ H) (v : Lp ℝ 2 ν) :
    rawIsometry P i (trunc t v) = prefixCLM P i t v := by
  have hafter : ∀ᵐ p ∂ν, t < p.1 → trunc t v p = 0 := by
    filter_upwards [trunc_ae t v] with p hp hpt
    rw [hp]
    exact Set.indicator_of_notMem
      (show p ∉ Set.Ioc 0 t ×ˢ (Set.univ : Set Ω) from fun hm ↦ not_le.mpr hpt hm.1.2) _
  have hbefore : ∀ᵐ p ∂ν, p.1 ≤ t → (v - trunc t v) p = 0 := by
    filter_upwards [trunc_ae t v, Lp.coeFn_sub v (trunc t v),
      FilteredItoCLM.ae_fst_mem_Ioc_trimMeasure_T (𝓖 := F) (μ := μ) H
        (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)] with p hp hs hm hpt
    rw [hs, Pi.sub_apply, hp, Set.indicator_of_mem
      (show p ∈ Set.Ioc 0 t ×ˢ (Set.univ : Set Ω) from ⟨⟨hm.1, hpt⟩, Set.mem_univ _⟩), sub_self]
  have hz := prefixCLM_eq_zero_of_vanishes_before P i t ht (v - trunc t v) hbefore
  rw [map_sub, sub_eq_zero] at hz
  rw [rawIsometry_eq_prefix_of_vanishes_after P i t ht _ hafter]
  exact hz.symm

end SHEStochastic.FiniteScalarItoProcess
