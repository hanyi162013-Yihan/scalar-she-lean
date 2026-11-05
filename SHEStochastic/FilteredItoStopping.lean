/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

Time-stopping argument from formal-mathfin, commit
3c41aee9bf2d9743f9e66b439f90d1635843d2d2, ItoIntegralLocality.lean,
now using a general Brownian filtration.
-/
module

public import SHEStochastic.FilteredItoProcessIsometry

@[expose] public section
namespace SHEStochastic.FilteredItoProcessGeneral
open MeasureTheory ProbabilityTheory FilteredItoCLM
open scoped NNReal ENNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {𝓖 : Filtration ℝ≥0 mΩ}
  (hB : IsPreBrownianReal B μ) [hFB : IsFilteredPreBrownian B 𝓖 μ]
include hB hFB

omit [IsProbabilityMeasure μ] hB hFB in
private lemma measurableSet_timeBand (u : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    MeasurableSet[𝓖.predictable]
      (Set.Ioc 0 u ×ˢ (Set.univ : Set Ω)) :=
  MeasureTheory.measurableSet_predictable_Ioc_prod
    (𝓕 := 𝓖) 0 u MeasurableSet.univ

theorem itoProcessCLM_eq_zero_of_vanishes_before (T u : ℝ≥0) (huT : u ≤ T)
    (hBmeas : ∀ t, Measurable (B t)) (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas))
    (hφ : ∀ᵐ p ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas), p.1 ≤ u → φ p = 0) :
    itoProcessCLM (𝓖 := 𝓖) hB T u hBmeas φ = 0 := by
  have hzero : ∫ z in (Set.Ioc 0 u ×ˢ (Set.univ : Set Ω)), (φ z) ^ 2
      ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) = 0 := by
    have hae : ∀ᵐ z ∂((trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas).restrict
        (Set.Ioc 0 u ×ˢ (Set.univ : Set Ω))), (φ z) ^ 2 = 0 := by
      rw [ae_restrict_iff' (measurableSet_timeBand (𝓖 := 𝓖) u hBmeas)]
      filter_upwards [hφ] with z hz hzmem
      rw [hz hzmem.1.2]
      ring
    rw [integral_congr_ae hae, integral_zero]
  refine norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp ?_)
  rw [itoProcessCLM_norm_sq (𝓖 := 𝓖) hB huT hBmeas φ, hzero]

theorem itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after (T u : ℝ≥0) (huT : u ≤ T)
    (hBmeas : ∀ t, Measurable (B t)) (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas))
    (hφ : ∀ᵐ p ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas), u < p.1 → φ p = 0) :
    itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas φ = itoProcessCLM (𝓖 := 𝓖) hB T u hBmeas φ := by
  haveI : Fact ((𝓖 u : MeasurableSpace Ω) ≤ mΩ) :=
    ⟨𝓖.le u⟩
  set X := itoIntegralCLM_T (𝓖 := 𝓖) hB T hBmeas φ with hX
  have hband : ∫ z in (Set.Ioc 0 u ×ˢ (Set.univ : Set Ω)), (φ z) ^ 2
      ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)
      = ∫ z, (φ z) ^ 2 ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) := by
    refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    filter_upwards [hφ, ae_fst_mem_Ioc_trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas] with z hz hzT hznot
    rw [hz (by by_contra hc; exact hznot ⟨⟨hzT.1, not_lt.mp hc⟩, Set.mem_univ _⟩)]
    ring
  have hnorm : ‖(condExpL2 ℝ ℝ (𝓖.le u) X : Lp ℝ 2 μ)‖ = ‖X‖ := by
    have hsq : ‖itoProcessCLM (𝓖 := 𝓖) hB T u hBmeas φ‖ ^ 2 = ‖X‖ ^ 2 := by
      rw [itoProcessCLM_norm_sq (𝓖 := 𝓖) hB huT hBmeas φ, hband, hX, itoIntegralCLM_T_norm (𝓖 := 𝓖) hB T hBmeas φ,
        MathFin.ItoIntegralL2.lp_two_norm_sq φ]
    rw [← itoProcessCLM_eq_condExpL2 (𝓖 := 𝓖) hB T u hBmeas φ]
    have hs := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hs
  rw [itoProcessCLM_eq_condExpL2 (𝓖 := 𝓖) hB T u hBmeas φ]
  have hcoe : ((condExpL2 ℝ ℝ (𝓖.le u) X : Lp ℝ 2 μ))
      = (lpMeas ℝ ℝ (𝓖 u) 2 μ).starProjection X := rfl
  rw [hcoe] at hnorm ⊢
  exact (Submodule.starProjection_eq_self_iff.mpr
    ((Submodule.mem_iff_norm_starProjection _ X).mpr hnorm)).symm


end SHEStochastic.FilteredItoProcessGeneral
