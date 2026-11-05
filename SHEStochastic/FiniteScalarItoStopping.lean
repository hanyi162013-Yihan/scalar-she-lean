/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

Reuses the band-energy and orthogonal-projection proofs of formal-mathfin,
3c41aee9bf2d9743f9e66b439f90d1635843d2d2. The stochastic rectangle pairing
is supplied by our finite-horizon law, with no global Brownian extension.
-/
module

public import SHEStochastic.FiniteScalarItoProcess

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
  (P : Coordinates F μ H ι)
local notation "ν" => inputMeasure F μ H

theorem simpleProcess_apply (i : ι) (V : Simple F H) (t : ℝ≥0) (ht : t ≤ H) (ω : Ω) :
    simpleProcess P i V t ω = ∑ p ∈ V.val.value.support,
      V.val.value p ω * (P.W i (min p.2 t) ω - P.W i (min p.1 t) ω) := by
  rw [simpleProcess, FilteredItoProcess.itoSimpleProcess_apply]
  simp only [clipped, min_assoc, min_eq_left ht, Finsupp.sum]

theorem simple_isometry_time (i : ι) (V : Simple F H) (t : ℝ≥0) (ht : t ≤ H) :
    ∫ ω, (simpleProcess P i V t ω) ^ 2 ∂μ =
      ∑ p ∈ V.val.value.support, ∑ q ∈ V.val.value.support,
        (∫ ω, V.val.value p ω * V.val.value q ω ∂μ) *
          max 0 (min ((min p.2 t : ℝ≥0) : ℝ) ((min q.2 t : ℝ≥0) : ℝ) -
            max ((min p.1 t : ℝ≥0) : ℝ) ((min q.1 t : ℝ≥0) : ℝ)) := by
  set a : (ℝ≥0 × ℝ≥0) → Ω → ℝ :=
    fun p ω ↦ V.val.value p ω * (P.W i (min p.2 t) ω - P.W i (min p.1 t) ω) with ha_def
  have ha_L2 : ∀ p ∈ V.val.value.support, MemLp (a p) 2 μ :=
    fun p hp ↦ by
      simpa only [clipped, min_assoc, min_eq_left ht] using
        IndependentDriverSimple.memLp_truncated_term (clipped_measurable P i) V.val t hp
  have hint : ∀ p ∈ V.val.value.support, ∀ q ∈ V.val.value.support,
      Integrable (fun ω ↦ a p ω * a q ω) μ :=
    fun p hp q hq ↦ (ha_L2 p hp).integrable_mul (ha_L2 q hq)
  calc ∫ ω, (simpleProcess P i V t ω) ^ 2 ∂μ
      = ∫ ω, ∑ p ∈ V.val.value.support, ∑ q ∈ V.val.value.support, a p ω * a q ω ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        show simpleProcess P i V t ω ^ 2
          = ∑ p ∈ V.val.value.support, ∑ q ∈ V.val.value.support, a p ω * a q ω
        rw [show simpleProcess P i V t ω = ∑ p ∈ V.val.value.support, a p ω from by
              rw [simpleProcess_apply P i V t ht], sq, Finset.sum_mul_sum]
    _ = ∑ p ∈ V.val.value.support, ∑ q ∈ V.val.value.support, ∫ ω, a p ω * a q ω ∂μ := by
        rw [integral_finsetSum _ (fun p hp ↦ integrable_finsetSum _ fun q hq ↦ hint p hp q hq)]
        exact Finset.sum_congr rfl fun p hp ↦
          integral_finsetSum _ (fun q hq ↦ hint p hp q hq)
    _ = ∑ p ∈ V.val.value.support, ∑ q ∈ V.val.value.support,
          (∫ ω, V.val.value p ω * V.val.value q ω ∂μ)
            * max 0 ((min ((min p.2 t : ℝ≥0) : ℝ) ((min q.2 t : ℝ≥0) : ℝ))
                - (max ((min p.1 t : ℝ≥0) : ℝ) ((min q.1 t : ℝ≥0) : ℝ))) := by
        refine Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun q hq ↦ ?_
        by_cases htp : p.1 ≤ t
        · by_cases htq : q.1 ≤ t
          · -- both rectangles active: collapse via the rectangle pairing
            simp only [ha_def, min_eq_left htp, min_eq_left htq]
            simpa only [ite_true, mul_one] using
              BrownianCoordinates.rectangle_pairing F μ H P.W P.law P.adapted i i
              (V.val.measurable_value p) (V.val.measurable_value q)
              (fun ω ↦ by rw [← Real.norm_eq_abs]; exact V.val.value_le_valueBound p ω)
              (fun ω ↦ by rw [← Real.norm_eq_abs]; exact V.val.value_le_valueBound q ω)
              (le_min (V.val.le_of_mem_support_value p hp) htp)
              (le_min (V.val.le_of_mem_support_value q hq) htq)
              ((min_le_right p.2 t).trans ht) ((min_le_right q.2 t).trans ht)
          · -- `q` past `t`: its increment collapses, overlap is zero
            have hq1 : min q.1 t = t := min_eq_right (not_le.mp htq).le
            have hq2 : min q.2 t = t :=
              min_eq_right ((not_le.mp htq).le.trans (V.val.le_of_mem_support_value q hq))
            have hz : ∀ ω, a p ω * a q ω = 0 := fun ω ↦ by simp [ha_def, hq1, hq2]
            rw [integral_congr_ae (Filter.Eventually.of_forall hz), integral_zero, hq1, hq2,
              max_eq_left (sub_nonpos.mpr ((min_le_right _ _).trans (le_max_right _ _))), mul_zero]
        · -- `p` past `t`: symmetric
          have hp1 : min p.1 t = t := min_eq_right (not_le.mp htp).le
          have hp2 : min p.2 t = t :=
            min_eq_right ((not_le.mp htp).le.trans (V.val.le_of_mem_support_value p hp))
          have hz : ∀ ω, a p ω * a q ω = 0 := fun ω ↦ by simp [ha_def, hp1, hp2]
          rw [integral_congr_ae (Filter.Eventually.of_forall hz), integral_zero, hp1, hp2,
            max_eq_left (sub_nonpos.mpr ((min_le_left _ _).trans (le_max_left _ _))), mul_zero]

theorem simple_band_isometry (i : ι) (V : Simple F H) (t : ℝ≥0) (ht : t ≤ H) :
    ‖simpleLp P i V t‖ ^ 2 =
      ∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)),
        (Function.uncurry ⇑V.val z) ^ 2 ∂ν := by
  simp only [inputMeasure]
  rw [FilteredItoProcessGeneral.band_integral_uncurry_sq (𝓖 := F) ht
    (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)]
  have hl : ‖simpleLp P i V t‖ ^ 2 = ∫ ω, simpleProcess P i V t ω ^ 2 ∂μ := by
    rw [MathFin.ItoIntegralL2.lp_two_norm_sq]
    exact integral_congr_ae ((simpleLp_ae P i V t).fun_comp (fun r : ℝ ↦ r ^ 2))
  rw [hl, simple_isometry_time P i V t ht]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  congr 1
  push_cast
  exact FilteredItoProcessGeneral.band_overlap_real _ _ _ _ _

theorem prefixCLM_norm_sq (i : ι) (t : ℝ≥0) (ht : t ≤ H) (v : Lp ℝ 2 ν) :
    ‖prefixCLM P i t v‖ ^ 2 =
      ∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)), (v z) ^ 2 ∂ν := by
  simp only [inputMeasure]
  let trunc := FilteredItoProcessGeneral.truncCLM (𝓖 := F) (μ := μ) H t
    (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)
  rw [← FilteredItoProcessGeneral.truncCLM_norm_sq (𝓖 := F) H t
    (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const) v]
  refine congrFun (DenseRange.equalizer (embedding_dense F μ H)
    ((continuous_pow 2).comp (prefixCLM P i t).continuous.norm)
    ((continuous_pow 2).comp trunc.continuous.norm) (funext fun V ↦ ?_)) v
  simp only [Function.comp_apply]
  rw [prefixCLM_simple, FilteredItoProcessGeneral.truncCLM_norm_sq (𝓖 := F),
    simple_band_isometry P i V t ht]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae
    (FilteredItoCLM.memLp_uncurry_trim_T (𝓖 := F) H
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const) V.val).coeFn_toLp] with z hz
  exact congrArg (fun r : ℝ ↦ r ^ 2) hz.symm

end SHEStochastic.FiniteScalarItoProcess
